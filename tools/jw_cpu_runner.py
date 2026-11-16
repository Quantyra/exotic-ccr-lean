#!/usr/bin/env python3
"""Guarded A001 CPU replay. No provisioning of accounts or host configuration.

The caller supplies a hash-bound admission, captured source archive and manifest.
The existing host-wide compiler flock covers downloads, cache and compilation.
Each attempted run is immutable; observe/collect a prior attempt, never restart it.
"""
from __future__ import annotations

import argparse
from collections import OrderedDict
from concurrent.futures import ThreadPoolExecutor
import errno
import gc
import gzip
from contextlib import contextmanager
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import pwd
import re
import shutil
import signal
import socket
import stat
import struct
import subprocess
import sys
import tarfile
import time
import zlib

ROOT = Path('/srv/kuzuryu-cloud/quantyra')
CGROUP = Path('/sys/fs/cgroup/user.slice/user-986.slice')
HOST = 'cpu-05'
SUPPORTED_HOSTS = frozenset(('cpu-02', 'cpu-03', 'cpu-04', 'cpu-05'))
UID = 986
DEFAULT_ROOT_FREE_THRESHOLD_BYTES = 500 * 2**20
MIN_FREE = DEFAULT_ROOT_FREE_THRESHOLD_BYTES
MIN_INODES = 100000
CACHE_ADVICE_MEMO_LIMIT = 8192
# Batch only the paused epoch's advice phase; resource and custody checks still
# run before every slice, and the existing one-second live-check ceiling holds.
PAUSED_EPOCH_ADVICE_SLICE_SECONDS = 0.5
PAUSED_EPOCH_ADVICE_WORKERS = 8
PAUSED_EPOCH_ADVICE_BATCH_SIZE = 512
# Minimum worker-slice capacity for this campaign. A host may have higher
# finite CPU, memory, and task limits; swap remains disabled. Runtime memory
# guards use the observed admitted limits; a versioned host profile may use
# verified capacity above this minimum for its flow-control thresholds.
MIN_LIMITS = {'cpu.max': '200000 100000', 'memory.high': '4294967296',
              'memory.max': '5368709120', 'memory.swap.max': '0', 'pids.max': '256'}
# Compatibility alias for legacy profiles. New profiles bind their threshold
# to a specific observed minimum-capacity class above the campaign floor.
LIMITS = MIN_LIMITS
EVENTS = ('high', 'max', 'oom', 'oom_kill')
MONITORED_EVENTS = ('max', 'oom', 'oom_kill')
# CYINT's trusted CPU-03 qualifier admits this one event history only on the
# exact boot it inspected; it rejects any later counter or boot change.
CPU03_EVENT_EXCEPTION_BOOT_ID = '82d42716-4868-43ae-b22e-52e55d5cbecf'
CPU03_EVENT_EXCEPTION_AUTHORITY_SHA256 = '655f591d36edf74d59c2f610b61c0e7009ad0cd3cb0b383e552a2c513439ea5f'
CPU03_EVENT_EXCEPTION_BINDING = {
    'host': 'cpu-03', 'boot_id': CPU03_EVENT_EXCEPTION_BOOT_ID,
    'events': {'high': 388, 'max': 0, 'oom': 0, 'oom_kill': 0},
    'authority_sha256': CPU03_EVENT_EXCEPTION_AUTHORITY_SHA256}
# Dan's 2026-11-15 direction binds CPU-05 run offers to this exact event
# exception; the pool-wide high-counter exclusion is recorded below.
CPU05_EVENT_EXCEPTION_AUTHORITY_ID = 'dan-direction-2026-11-15-ignore-cpu05-high-count'
CPU05_EVENT_EXCEPTION_BINDING = {
    'host': 'cpu-05', 'ignored_events': ['high'],
    'authority_id': CPU05_EVENT_EXCEPTION_AUTHORITY_ID}
# Dan's 2026-11-16 direction ignores the cumulative memory.events.high count
# across the approved compiler pool. Other memory event counters remain gated.
POOL_HIGH_EVENT_IGNORE_AUTHORITY_ID = 'dan-direction-2026-11-16-ignore-memory-events-high'
CPU03_DEEPER_REFILL_PROFILE = 'cpu03-deeper-refill-target-3.125GiB-v1'
CPU04_DEEPER_REFILL_PROFILE = 'cpu04-deeper-refill-target-3.125GiB-v1'
TOOLCHAIN = 'leanprover/lean4:v4.33.0-rc1'
TOOLCHAIN_ARCHIVE = 'lean-4.33.0-rc1-linux.tar.zst'
TOOLCHAIN_SHA256 = '25e7b3e18ec75a4e2529fc23194be8e3cc3183df99b553f870d8a111c7488210'
TOOLCHAIN_URL = ('https://github.com/leanprover/lean4/releases/download/'
                 'v4.33.0-rc1/' + TOOLCHAIN_ARCHIVE)


def now():
    return datetime.now(timezone.utc).isoformat()


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def root_free_threshold(config):
    """Return the hash-bound admission threshold, with the campaign default."""
    value = config.get('root_free_threshold_bytes', DEFAULT_ROOT_FREE_THRESHOLD_BYTES)
    require(type(value) is int and value >= DEFAULT_ROOT_FREE_THRESHOLD_BYTES,
            f'Root free-space threshold must be an integer at least {DEFAULT_ROOT_FREE_THRESHOLD_BYTES}')
    return value


def admission_host(config):
    """Return the exact approved pool host pinned by this admission."""
    value = config.get('host', HOST)
    require(type(value) is str and value in SUPPORTED_HOSTS,
            'Host is not in the approved S023 compiler pool')
    return value


def approved_event_exception(host, boot_id):
    if host == 'cpu-03' and boot_id == CPU03_EVENT_EXCEPTION_BOOT_ID:
        return CPU03_EVENT_EXCEPTION_BINDING
    if host == 'cpu-05':
        return CPU05_EVENT_EXCEPTION_BINDING
    return None


def event_signature(host, events):
    # This historical high-event counter is informational only on every
    # admitted compiler host; max/OOM counters remain part of admission and
    # continuous safety checks.
    return {name: value for name, value in events.items() if name != 'high'}


def admitted_event_profile(host, boot_id):
    binding = approved_event_exception(host, boot_id)
    if binding is None:
        authority = POOL_HIGH_EVENT_IGNORE_AUTHORITY_ID
        events = {name: 0 for name in EVENTS if name != 'high'}
    else:
        authority = (f"cyint-cpu03-pinned-boot-{CPU03_EVENT_EXCEPTION_AUTHORITY_SHA256}"
                     if host == 'cpu-03' else binding['authority_id'])
        events = (binding['events'] if host == 'cpu-03' else
                  {name: 0 for name in EVENTS if name not in binding['ignored_events']})
        events = {name: value for name, value in events.items() if name != 'high'}
    return (events, authority)


def validate_capacity_profile(limits):
    """Require at least the campaign's finite resource envelope."""
    require(type(limits) is dict and set(limits) == set(MIN_LIMITS),
            'Worker resource profile fields changed')

    cpu = limits['cpu.max'].split()
    minimum_cpu = MIN_LIMITS['cpu.max'].split()
    require(len(cpu) == 2 and all(part.isdigit() for part in cpu) and
            len(minimum_cpu) == 2 and all(part.isdigit() for part in minimum_cpu) and
            int(cpu[1]) > 0 and int(minimum_cpu[1]) > 0 and
            int(cpu[0])*int(minimum_cpu[1]) >= int(minimum_cpu[0])*int(cpu[1]),
            'Worker CPU capacity is below the campaign minimum')

    for name in ('memory.high', 'memory.max', 'pids.max'):
        value = limits[name]
        minimum = MIN_LIMITS[name]
        require(type(value) is str and value.isdigit() and
                int(value) >= int(minimum),
                f'Worker {name} capacity is below the campaign minimum')
    require(int(limits['memory.high']) <= int(limits['memory.max']),
            'Worker memory.high exceeds memory.max')
    require(limits['memory.swap.max'] == MIN_LIMITS['memory.swap.max'],
            'Worker swap limit differs from the campaign requirement')


def observed_memory_high(observation):
    return int(observation['limits']['memory.high'])


def validate_profile_capacity(config, observation):
    if config.get('reclaim_profile') == CPU05_HIGH_CAPACITY_PROFILE:
        require(admission_host(config) == 'cpu-05' and
                observed_memory_high(observation) >= 5*2**30 and
                int(observation['limits']['memory.max']) >= 6*2**30,
                'CPU-05 higher-capacity minimum profile is not present')


def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(chunk)
        if hasattr(os, 'posix_fadvise'):
            os.posix_fadvise(stream.fileno(), 0, 0, os.POSIX_FADV_DONTNEED)
    return h.hexdigest()


def write_json(path, value):
    path = Path(path)
    temporary = path.with_suffix(path.suffix + '.tmp')
    with temporary.open('w', encoding='utf-8', newline='\n') as stream:
        json.dump(value, stream, indent=2)
        stream.write('\n')
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(temporary, path)


def owned_path(value):
    p = Path(value).resolve()
    require(p.is_relative_to(ROOT) and p != ROOT, 'Path escapes worker root')
    return p


def observe():
    stat = os.statvfs('/')
    counters = dict(line.split() for line in (CGROUP/'memory.events').read_text().splitlines())
    filesystem_errors = {}
    # Kernel ext4 counters, where exposed. Missing visibility is recorded, not
    # represented as a successful disk diagnosis.
    for path in Path('/sys/fs/ext4').glob('*/errors_count'):
        try:
            filesystem_errors[str(path)] = int(path.read_text().strip())
        except (PermissionError, OSError, ValueError):
            filesystem_errors[str(path)] = None
    return {'utc': now(), 'host': socket.gethostname().split('.')[0],
            'boot_id': Path('/proc/sys/kernel/random/boot_id').read_text().strip(),
            'uid': os.getuid(), 'worker': pwd.getpwuid(os.getuid()).pw_name,
            'cgroup': Path('/proc/self/cgroup').read_text().strip(),
            'root_available_bytes': stat.f_bavail * stat.f_frsize,
            'root_available_inodes': stat.f_favail,
            'root_read_only': bool(stat.f_flag & os.ST_RDONLY),
            'limits': {name: (CGROUP/name).read_text().strip() for name in LIMITS},
            'memory_current': int((CGROUP/'memory.current').read_text()),
            'memory_stat': dict((key, int(value)) for key, value in
                (line.split() for line in (CGROUP/'memory.stat').read_text().splitlines())
                if key in ('anon', 'file', 'file_dirty', 'file_writeback', 'kernel',
                           'file_mapped', 'active_file', 'inactive_file', 'slab_reclaimable', 'slab_unreclaimable')),
            'events': {name: int(counters[name]) for name in MONITORED_EVENTS},
            'filesystem_error_counters': filesystem_errors}


def validate_observation(value, minimum_free=MIN_FREE, expected_host=HOST):
    require(type(minimum_free) is int and minimum_free >= MIN_FREE,
            f'Root free-space threshold cannot be below {MIN_FREE} bytes')
    require(expected_host in SUPPORTED_HOSTS, 'Host is not in the approved S023 compiler pool')
    require(value['host'] == expected_host, 'Wrong host')
    require(type(value.get('boot_id')) is str and re.fullmatch(r'[0-9a-f]{8}(?:-[0-9a-f]{4}){3}-[0-9a-f]{12}', value['boot_id']),
            'Missing or malformed host boot ID')
    require(value['uid'] == UID and value['worker'] == 'quantyra-worker', 'Wrong worker')
    require(value['cgroup'].startswith('0::/user.slice/user-986.slice/'), 'Wrong cgroup')
    validate_capacity_profile(value['limits'])
    require(not value['root_read_only'], 'Root filesystem is read-only')
    require(value['root_available_bytes'] >= minimum_free,
            f"Root reserve failed: available={value['root_available_bytes']} minimum={minimum_free}")
    require(value['root_available_inodes'] >= MIN_INODES, 'Root inode reserve failed')
    require(value['memory_current'] < observed_memory_high(value), 'MemoryHigh admission failed')
    require(all(type(value['events'].get(name)) is int and value['events'][name] >= 0
                for name in MONITORED_EVENTS), 'Invalid memory event evidence')


def validate_preflight(config, value):
    """Apply the hash-bound campaign reserve to the admission preflight."""
    minimum_free = root_free_threshold(config)
    expected_host = admission_host(config)
    validate_observation(value, minimum_free, expected_host)
    validate_profile_capacity(config, value)
    expected_events, profile_id = admitted_event_profile(expected_host, value['boot_id'])
    binding = approved_event_exception(expected_host, value['boot_id'])
    if binding is not None:
        require(config.get('approved_event_profile') == binding,
                'Admission does not bind the exact approved host/boot event profile')
    else:
        require('approved_event_profile' not in config,
                'Admission contains a host/event profile that does not match this boot')
    require(event_signature(expected_host, value['events']) == expected_events,
            'Memory event profile mismatch: '
            f"host={expected_host} boot={value['boot_id']} events={value['events']}")
    minimum_memory_headroom = config.get('minimum_memory_headroom_bytes', 0)
    require(type(minimum_memory_headroom) is int and
            0 <= minimum_memory_headroom <= observed_memory_high(value),
            'Invalid captured minimum memory headroom')
    require(value['memory_current'] <=
            observed_memory_high(value)-minimum_memory_headroom,
            'Memory headroom admission failed: '
            f"current={value['memory_current']} required_headroom={minimum_memory_headroom}")
    return minimum_free


def compiler_processes():
    rows = subprocess.check_output(['ps', '-eo', 'pid,comm'], text=True).splitlines()[1:]
    return [row.strip() for row in rows if row.split()[-1] in ('lean', 'lake')]


def compiler_details(include_pss=True, pss_budget=0.2):
    result = []
    pss_deadline = time.monotonic()+pss_budget
    queries = {'--version', '--help', '--print-prefix', '--print-libdir', '--githash'}
    for path in Path('/proc').iterdir():
        if not path.name.isdigit():
            continue
        try:
            command = (path/'comm').read_text().strip()
            if command not in ('lean', 'lake', 'cache') and int(path.name) != os.getpid():
                continue
            argv = (path/'cmdline').read_bytes().decode('utf-8', errors='replace').split('\0')
            argv = [argument for argument in argv if argument]
            executable = (path/'exe').readlink()
            native_lean = command == 'lean' and executable.name == 'lean'
            arguments = argv[1:] if native_lean else argv[2:]
            entry = {'pid': int(path.name), 'comm': command, 'argv': argv,
                     'start_ticks': (path/'stat').read_text().rsplit(')', 1)[1].split()[19],
                     'uid': path.stat().st_uid,
                     'cgroup': (path/'cgroup').read_text().strip(),
                     'executable': str(executable), 'native_lean': native_lean,
                     'query_only': len(arguments) == 1 and arguments[0] in queries}
            for source, fields in [('status', {'VmRSS', 'RssAnon', 'RssFile', 'RssShmem'}),
                    ('smaps_rollup', {'Rss', 'Pss', 'Pss_Anon', 'Pss_File', 'Pss_Shmem',
                                      'Shared_Clean', 'Private_Clean', 'Private_Dirty'})]:
                old_handler = None
                try:
                    if source == 'smaps_rollup':
                        remaining = pss_deadline-time.monotonic()
                        if not include_pss or remaining <= 0:
                            entry[source+'_bytes'] = None
                            entry[source+'_observation'] = 'not sampled in this bounded observation'
                            continue
                        def timed_out(signum, frame):
                            raise TimeoutError('bounded process PSS observation deadline')
                        old_handler = signal.signal(signal.SIGALRM, timed_out)
                        signal.setitimer(signal.ITIMER_REAL, min(0.1, remaining))
                    entry[source+'_bytes'] = {key.rstrip(':'): int(value.split()[0])*1024
                        for line in (path/source).read_text().splitlines() if ':' in line
                        for key,value in [line.split(':',1)] if key in fields}
                    if source == 'smaps_rollup':
                        entry[source+'_observed_utc'] = now()
                except (PermissionError, FileNotFoundError, ProcessLookupError, TimeoutError) as exc:
                    entry[source+'_bytes'] = None
                    entry[source+'_observation'] = type(exc).__name__
                finally:
                    if old_handler is not None:
                        signal.setitimer(signal.ITIMER_REAL, 0)
                        signal.signal(signal.SIGALRM, old_handler)
            result.append(entry)
        except PermissionError:
            result.append({'pid': int(path.name), 'comm': command, 'argv': [],
                'native_lean': command == 'lean', 'query_only': False,
                'uid': path.stat().st_uid, 'visibility_error': 'PermissionError'})
        except (FileNotFoundError, ProcessLookupError):
            continue
    return result


def cache_module_scope(source):
    modules = set()
    for path in source.rglob('*.lean'):
        if '.lake' in path.relative_to(source).parts:
            continue
        for line in path.read_text(encoding='utf-8').splitlines():
            match = re.match(r'^\s*import\s+(.+)$', line)
            if match:
                for name in match.group(1).split():
                    if name.startswith('--'):
                        break
                    if re.fullmatch(r'Mathlib(?:\.[A-Za-z0-9_]+)*', name):
                        modules.add(name)
    return modules


def artifact_roots(config, include_toolchain=False):
    workspace = owned_path(config['workspace'])
    roots = [workspace/'cache', owned_path(config['run'])/'source/.lake/build']
    packages = owned_path(config.get('dependency_source_root', str(owned_path(config['run'])/'source/.lake/packages')))
    roots.extend(path/'.lake/build' for path in packages.glob('*') if path.is_dir())
    if include_toolchain and config.get('toolchain_directory'):
        roots.append(owned_path(config['toolchain_directory']))
    require(all(root.resolve().is_relative_to(workspace) for root in roots), 'Artifact root escapes campaign')
    return roots


class CompletedArtifactDrain:
    """Release only closed, campaign-owned artifact files, without rewriting them."""
    def __init__(self, workspace, roots):
        self.workspace = owned_path(workspace)
        self.roots, self.seen = roots, {}
        self.files = self.bytes = 0

    def release(self, path):
        path = Path(path)
        require(path.resolve().is_relative_to(self.workspace), 'Artifact escapes campaign')
        with path.open('rb') as stream:
            info = os.fstat(stream.fileno())
            require(info.st_uid == UID and stat.S_ISREG(info.st_mode), 'Artifact is not worker-owned regular file')
            os.fsync(stream.fileno())
            os.posix_fadvise(stream.fileno(), 0, 0, os.POSIX_FADV_DONTNEED)
        self.files += 1
        self.bytes += info.st_size

    def sweep(self, force=False):
        for root in self.roots:
            for directory, dirs, names in os.walk(root, followlinks=False):
                dirs[:] = [name for name in dirs if not (Path(directory)/name).is_symlink()]
                for name in names:
                    path = Path(directory)/name
                    try:
                        info = path.stat(follow_symlinks=False)
                        if not stat.S_ISREG(info.st_mode):
                            continue
                        identity = (info.st_size, info.st_mtime_ns, info.st_ctime_ns)
                        if force or self.seen.get(str(path)) != identity:
                            self.release(path)
                            self.seen[str(path)] = identity
                    except FileNotFoundError:
                        continue


def drain_owned_artifacts(config, label='initial'):
    require(sys.platform == 'linux' and os.getuid() == UID, 'Designated Linux worker required')
    require(label in ('initial', 'pre-cache', 'pre-build'), 'Unknown artifact-drain label')
    before = observe()
    drain = CompletedArtifactDrain(config['workspace'], artifact_roots(config, include_toolchain=True))
    drain.sweep()
    result = {'utc': now(), 'operation': 'fsync and POSIX_FADV_DONTNEED of only closed campaign artifact files',
              'files': drain.files, 'bytes': drain.bytes, 'before': before, 'after': observe()}
    write_json(owned_path(config['run'])/(label+'-owned-cache-drain.json'), result)
    print(json.dumps({'files': drain.files, 'bytes': drain.bytes,
                      'memory_before': before['memory_current'], 'memory_after': result['after']['memory_current']}), flush=True)


def bounded_decompress(actual, config, arguments, source_stream=sys.stdin, batch_size=16, reader=observe):
    """Keep the native pinned leantar JSON protocol, with closed-file drains between batches."""
    require(sys.platform == 'linux' and os.getuid() == UID, 'Designated Linux worker required')
    import fcntl
    workspace, run = owned_path(config['workspace']), owned_path(config['run'])
    actual = owned_path(actual)
    require(actual.is_relative_to(workspace), 'Native decompressor escapes campaign')
    require(set(arguments) <= {'-x', '-f', '--delete-corrupted', '-j', '-'} and
            '-x' in arguments and arguments[-2:] == ['-j', '-'], 'Unsupported native decompression protocol')
    raw = source_stream.read()
    records = json.loads(raw)
    require(isinstance(records, list) and len(records) <= 20000, 'Invalid decompression batch input')
    input_paths = []
    for item in records:
        require(isinstance(item, (str, dict)), 'Invalid native archive record')
        filename = item if isinstance(item, str) else item.get('file')
        require(isinstance(filename, str), 'Invalid native cache filename')
        path = Path(filename).resolve()
        require(path.is_relative_to(workspace/'cache') and path.is_file(), 'Cache input escapes campaign')
        input_paths.append(path)
        if isinstance(item, dict) and 'base' in item:
            bases = item['base'] if isinstance(item['base'], list) else [item['base']]
            require(all(isinstance(base, str) and Path(base).resolve().is_relative_to(workspace)
                        for base in bases), 'Native extraction base escapes campaign')
    log = run/f'leantar-batches-{os.getpid()}.jsonl'
    def record(value):
        with log.open('a', encoding='utf-8') as stream:
            stream.write(json.dumps({'utc': now(), **value})+'\n')
            stream.flush(); os.fsync(stream.fileno())
    command = [str(actual), '--jobs', '1', *arguments]
    record({'kind': 'start', 'records': len(records), 'batch_size': batch_size,
            'input_json_sha256': hashlib.sha256(raw.encode()).hexdigest(), 'native_command': command})
    with (run/'cache-decompress.lock').open('a+') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        drain = CompletedArtifactDrain(workspace, artifact_roots(config))
        baseline = reader()
        baseline_boot_id = baseline['boot_id']
        drain.sweep()
        for offset in range(0, len(records), batch_size):
            before = reader(); validate_observation(before, root_free_threshold(config), admission_host(config))
            require(before['boot_id'] == baseline_boot_id, 'Host boot changed during decompression')
            require(event_signature(admission_host(config), before['events']) ==
                    event_signature(admission_host(config), baseline['events']),
                    'Memory events changed during decompression')
            reclaim = None
            headroom_limit = observed_memory_high(before)-2**30
            if before['memory_current'] >= headroom_limit:
                delegated = config.get('delegated_reclaim')
                require(type(delegated) is dict and set(delegated) == {'unit'},
                        'Low-memory cache decompression requires the recorded delegated service leaf')
                unit = delegated['unit']
                leaf, interface, custody = service_leaf(unit)
                relative = '0::' + str(leaf).removeprefix('/sys/fs/cgroup')
                members_before = tuple(sorted(int(value) for value in (leaf/'cgroup.procs').read_text().split()))
                require(os.getpid() in members_before and bool(members_before),
                        'Cache reclaim leaf does not contain this controller')
                for pid in members_before:
                    identity = process_identity(pid)
                    require(identity['uid'] == UID and
                            (Path('/proc')/str(pid)/'cgroup').read_text().strip() == relative and
                            process_identity(pid)['start_ticks'] == identity['start_ticks'],
                            'Cache reclaim leaf contains an unexpected or escaped process')
                profile = selected_reclaim_profile(config)
                cap = 838860800 if profile in (CPU02_DEEPER_REFILL_PROFILE,
                                                CPU03_DEEPER_REFILL_PROFILE,
                                                CPU04_DEEPER_REFILL_PROFILE,
                                                CPU05_HIGH_CAPACITY_PROFILE) else 436207616
                # Preserve the full decompressor safety margin, with one page of slack.
                target = headroom_limit-65536
                request_bytes = min(max(0, before['memory_current']-target), cap)
                require(request_bytes > 0,
                        'Cache reclaim was requested without a positive headroom deficit')
                interface.write_text(str(request_bytes), encoding='ascii')
                after_reclaim = reader()
                validate_observation(after_reclaim, root_free_threshold(config), admission_host(config))
                require(after_reclaim['boot_id'] == baseline_boot_id,
                        'Host boot changed during cache headroom reclaim')
                require(event_signature(admission_host(config), after_reclaim['events']) ==
                        event_signature(admission_host(config), before['events']),
                        'Memory events changed during cache headroom reclaim')
                leaf_after, interface_after, custody_after = service_leaf(unit, custody)
                require(leaf_after == leaf and interface_after == interface and
                        custody_after == custody and after_reclaim['memory_current'] < headroom_limit,
                        'Bounded cache reclaim did not restore the required decompression headroom')
                members_after = tuple(sorted(int(value) for value in (leaf/'cgroup.procs').read_text().split()))
                require(members_after == members_before,
                        'Cache reclaim service membership changed during headroom recovery')
                reclaim = {'request_bytes': request_bytes,
                           'memory_before': before['memory_current'],
                           'memory_after': after_reclaim['memory_current'],
                           'events_before': before['events'], 'events_after': after_reclaim['events'],
                           'unit': unit, 'leaf_members': list(members_after)}
                before = after_reclaim
                record({'kind': 'bounded-memory-reclaim', **reclaim})
            require(before['memory_current'] < observed_memory_high(before)-2**30,
                    'Native decompression batch lacks 1 GiB memory headroom')
            batch = records[offset:offset+batch_size]
            child = subprocess.run(command, input=json.dumps(batch), text=True)
            if child.returncode != 0:
                record({'kind': 'batch-failed', 'offset': offset, 'count': len(batch), 'exit_code': child.returncode})
                raise RuntimeError(f'Native decompressor failed: exit {child.returncode}')
            drain.sweep()
            for path in input_paths[offset:offset+batch_size]:
                drain.release(path)
            after = reader(); validate_observation(after, root_free_threshold(config), admission_host(config))
            require(after['boot_id'] == baseline_boot_id, 'Host boot changed during decompression')
            require(event_signature(admission_host(config), after['events']) ==
                    event_signature(admission_host(config), baseline['events']),
                    'Memory events changed during decompression')
            record({'kind': 'batch-completed', 'offset': offset, 'count': len(batch), 'exit_code': 0,
                    'memory_before': before['memory_current'], 'memory_after': after['memory_current'],
                    'cumulative_advised_files': drain.files, 'cumulative_advised_bytes': drain.bytes})
        record({'kind': 'completed', 'exit_code': 0, 'records': len(records)})


def write_inventory(root, destination, mode):
    """Bounded streaming inventory; invoked in a short-lived guarded child."""
    require(mode in ('all', 'dependency-source', 'compiled'), 'Unknown inventory mode')
    def files(directory):
        with os.scandir(directory) as entries:
            children = sorted(entries, key=lambda entry: entry.name)
        for entry in children:
            if entry.is_symlink():
                continue
            if entry.is_dir(follow_symlinks=False):
                yield from files(Path(entry.path))
            elif entry.is_file(follow_symlinks=False):
                yield Path(entry.path)
    temporary = destination.with_suffix(destination.suffix+'.tmp')
    count = 0
    with temporary.open('w', encoding='utf-8', newline='\n') as stream:
        stream.write('{\n  "files": [')
        for path in files(root):
            relative = path.relative_to(root)
            if mode == 'dependency-source' and ('.lake' in relative.parts or path.suffix not in ('.lean','.toml','.json')):
                continue
            if mode == 'compiled' and not ('.olean' in path.name or path.suffix in ('.ilean','.ir')):
                continue
            item = {'path': relative.as_posix(), 'sha256': digest(path), 'bytes': path.stat().st_size}
            stream.write(',\n' if count else '\n')
            stream.write('\n'.join('    '+line for line in json.dumps(item, indent=2).splitlines()))
            count += 1
        stream.write('\n  ]\n}\n' if count else ']\n}\n')
        stream.flush(); os.fsync(stream.fileno())
    os.replace(temporary, destination)
    return {'files': count, 'sha256': digest(destination), 'mode': mode}


def stream_inventory(path):
    """Read one captured pretty-printed inventory record at a time."""
    with Path(path).open('r', encoding='utf-8') as stream:
        lines = None
        for line in stream:
            if line.startswith('    {'):
                require(lines is None, 'Nested inventory record')
                lines = [line]
            elif lines is not None:
                lines.append(line)
                require(len(lines) <= 16 and sum(map(len, lines)) <= 16384,
                        'Inventory record exceeds bound')
                if line.startswith('    }'):
                    yield json.loads(''.join(lines).rstrip().rstrip(','))
                    lines = None
        require(lines is None, 'Incomplete inventory record')


@contextmanager
def lease(path):
    import fcntl
    require(path == ROOT/'locks/host-compiler.lock' and path.is_file(), 'Existing host lease required')
    require(path.stat().st_uid == UID, 'Wrong lease owner')
    with path.open('r+') as handle:
        try:
            fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise RuntimeError('Host compiler lease is already held') from exc
        try:
            yield
        finally:
            fcntl.flock(handle, fcntl.LOCK_UN)


class Guard:
    def __init__(self, directory, minimum_free=MIN_FREE, timeout=4 * 3600,
                 reader=observe, clock=time.monotonic, expected_host=HOST,
                 expected_boot_id=None, expected_events=None):
        self.reader, self.clock = reader, clock
        self.minimum_free, self.timeout, self.expected_host = minimum_free, timeout, expected_host
        self.start = clock()
        self.baseline = reader()
        validate_observation(self.baseline, minimum_free, expected_host)
        self.boot_id = self.baseline['boot_id']
        if expected_boot_id is not None:
            require(self.boot_id == expected_boot_id, 'Host boot changed before continuous guard started')
        if expected_events is not None:
            require(event_signature(expected_host, self.baseline['events']) ==
                    event_signature(expected_host, expected_events),
                    'Memory events changed before continuous guard started')
        self.directory = directory
        self.samples = 0
        self.minimum_available = self.baseline['root_available_bytes']
        self.maximum_memory = self.baseline['memory_current']
        self.peak_memory_sample = self.baseline
        self.last = self.baseline
        self.maximum_concurrent_lean = 0
        self.last_pss_sample = -float('inf')
        self.pss_cache = {}
        self.maximum_check_seconds = 0.0

    def check(self):
        check_started = time.monotonic()
        value = self.reader()
        try:
            validate_observation(value, self.minimum_free, self.expected_host)
            require(value['boot_id'] == self.boot_id, 'Host boot changed during compilation')
            require(event_signature(self.expected_host, value['events']) ==
                    event_signature(self.expected_host, self.baseline['events']),
                    'Memory pressure/OOM event or reset')
        except BaseException:
            value['compiler_processes'] = self.last.get('compiler_processes', [])
            value['process_details_observation'] = 'Previous guard sample; immediate resource failure stops before diagnostic reads'
            self.last = value
            self.samples += 1
            self.minimum_available = min(self.minimum_available, value['root_available_bytes'])
            if value['memory_current'] > self.maximum_memory:
                self.maximum_memory, self.peak_memory_sample = value['memory_current'], value
            raise
        sample_pss = time.monotonic()-self.last_pss_sample >= 5.0
        compilers = compiler_details(include_pss=sample_pss)
        if sample_pss:
            self.last_pss_sample = time.monotonic()
        for row in compilers:
            identity = (row['pid'], row.get('start_ticks'))
            if row.get('smaps_rollup_bytes') is not None:
                self.pss_cache[identity] = (row['smaps_rollup_bytes'], row['smaps_rollup_observed_utc'])
            elif identity in self.pss_cache:
                metrics, utc = self.pss_cache[identity]
                row['smaps_rollup_bytes'], row['smaps_rollup_observed_utc'] = metrics, utc
                row['smaps_rollup_observation'] = 'last bounded sample; timestamp preserved'
        # Never assess an event counter captured before diagnostic observation.
        value = self.reader()
        value['guard_check_seconds'] = time.monotonic()-check_started
        self.maximum_check_seconds = max(self.maximum_check_seconds, value['guard_check_seconds'])
        value['compiler_processes'] = compilers
        self.last = value
        self.samples += 1
        self.minimum_available = min(self.minimum_available, value['root_available_bytes'])
        if value['memory_current'] > self.maximum_memory:
            self.maximum_memory = value['memory_current']
            self.peak_memory_sample = value
        validate_observation(value, self.minimum_free, self.expected_host)
        require(value['boot_id'] == self.boot_id, 'Host boot changed during compilation')
        require(event_signature(self.expected_host, value['events']) ==
                event_signature(self.expected_host, self.baseline['events']),
                'Memory pressure/OOM event or reset')
        lean_count = sum(row['native_lean'] and not row['query_only'] for row in compilers)
        require(not any(row['native_lean'] and row['uid'] != UID for row in compilers),
                'Competing native Lean process belongs to another account')
        self.maximum_concurrent_lean = max(self.maximum_concurrent_lean, lean_count)
        require(lean_count <= 1, 'More than one concurrent Lean compiler')
        for path, count in self.baseline['filesystem_error_counters'].items():
            if count is not None:
                require(value['filesystem_error_counters'].get(path) == count,
                        'Filesystem error counter changed: ' + path)
        require(self.clock() - self.start < self.timeout, 'Total run timeout')
        if self.samples % 5 == 0:
            write_json(self.directory/'resource-current.json', self.summary())

    def summary(self):
        return {'host': self.expected_host, 'baseline': self.baseline, 'last': self.last, 'samples': self.samples,
                'minimum_available_bytes': self.minimum_available,
                'maximum_memory_bytes': self.maximum_memory,
                'peak_memory_sample': self.peak_memory_sample,
                'maximum_concurrent_lean': self.maximum_concurrent_lean,
                'maximum_guard_check_seconds': self.maximum_check_seconds,
                'root_reserve_bytes': self.minimum_free}


def process_identity(pid):
    path = Path('/proc')/str(pid)
    fields = (path/'stat').read_text().rsplit(')', 1)[1].split()
    return {'pid': pid, 'uid': path.stat().st_uid, 'state': fields[0],
            'pgrp': int(fields[2]), 'session': int(fields[3]), 'start_ticks': fields[19]}


def capture_stage_identity(process):
    try:
        leader = process_identity(process.pid)
    except FileNotFoundError:
        require(process.poll() is not None, 'Owned stage leader vanished unexpectedly')
        return None
    require(leader['uid'] == UID and leader['pgrp'] == process.pid
            and leader['session'] == process.pid and os.getpgrp() != process.pid,
            'Owned stage is not a distinct worker process group/session')
    identity = {'leader_pid': process.pid, 'leader_start_ticks': leader['start_ticks'],
                'known_members': {str(process.pid): leader['start_ticks']}}
    process.jw_identity = identity
    return identity


def owned_group_members(identity):
    require(identity is not None, 'Stage group identity was not captured')
    rows = []
    for path in Path('/proc').iterdir():
        if not path.name.isdigit():
            continue
        try:
            row = process_identity(int(path.name))
        except (FileNotFoundError, ProcessLookupError):
            continue
        if row['pgrp'] != identity['leader_pid']:
            continue
        require(row['uid'] == UID and row['session'] == identity['leader_pid']
                and int(row['start_ticks']) >= int(identity['leader_start_ticks']),
                'Owned stage group identity/ownership mismatch')
        rows.append(row)
    require(not rows or any(identity['known_members'].get(str(row['pid'])) == row['start_ticks']
                            for row in rows), 'No original process identity anchors stage group')
    identity['known_members'].update((str(row['pid']), row['start_ticks']) for row in rows)
    return rows


def terminate_owned(process):
    """Stop only the process group started by this runner, preserving other jobs."""
    identity = getattr(process, 'jw_identity', None)
    if identity is not None:
        rows = owned_group_members(identity)
        if any(row['state'] != 'Z' for row in rows):
            # Queue termination before continuing stopped processes so an
            # exception/guard/interrupt cannot strand a frozen descendant.
            try:
                os.killpg(process.pid, signal.SIGTERM)
                os.killpg(process.pid, signal.SIGCONT)
            except ProcessLookupError:
                pass  # The verified group completed between observation and signal.
            deadline = time.monotonic()+15
            while any(row['state'] != 'Z' for row in owned_group_members(identity)):
                if time.monotonic() >= deadline:
                    try:
                        os.killpg(process.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    break
                time.sleep(0.05)
        process.wait(timeout=15)
        require(not any(row['state'] != 'Z' for row in owned_group_members(identity)),
                'Owned stage descendants remain after termination')
        return
    if process.poll() is None:
        os.killpg(process.pid, signal.SIGTERM)
        try:
            process.wait(timeout=15)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait(timeout=15)


def advise_immutable_input(path, roots, expected_size=None):
    """Discard only expendable file cache; never alter a process mapping or bytes."""
    path = Path(path)
    require(path.is_absolute() and not path.is_symlink(), 'Invalid immutable input advice path')
    resolved = path.resolve()
    require(any(resolved.is_relative_to(root) for root in roots),
            'Immutable input advice escapes verified inputs')
    fd = os.open(resolved, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
    try:
        info = os.fstat(fd)
        require(info.st_uid == UID and stat.S_ISREG(info.st_mode), 'Wrong immutable input advice owner/type')
        if expected_size is not None:
            require(info.st_size == expected_size, 'Qualified input advice size changed')
        os.posix_fadvise(fd, 0, 0, os.POSIX_FADV_DONTNEED)
        return info.st_size
    finally:
        os.close(fd)


def is_vanished_lake_cache_executable(path, roots, error):
    """Recognize only the observed atomic Lake cache executable temp race."""
    path = Path(path)
    if (error.filename is not None and Path(error.filename) != path) or \
            not re.fullmatch(r'cache\.tmp[0-9a-f]+', path.name):
        return False
    try:
        resolved = path.resolve()
    except OSError:
        return False
    if not any(resolved.is_relative_to(root) for root in roots):
        return False
    return len(path.parts) >= 4 and path.parts[-4:-1] == ('.lake', 'build', 'bin')


def quiescent_group_snapshot(identity):
    """Check every thread, including owned helpers that are not Lean processes."""
    members = []
    for row in owned_group_members(identity):
        if row['state'] == 'Z':
            continue
        require(row['state'] in ('T', 't'), 'Paused epoch process is not quiescent')
        threads = []
        for task in (Path('/proc')/str(row['pid'])/'task').iterdir():
            fields = (task/'stat').read_text().rsplit(')', 1)[1].split()
            require(task.stat().st_uid == UID and fields[0] in ('T', 't', 'Z'),
                    'Paused epoch thread is not owned/quiescent')
            threads.append((int(task.name), fields[19]))
        members.append((row['pid'], row['start_ticks'], tuple(sorted(threads))))
    return tuple(sorted(members))


def service_leaf(unit, custody=None):
    """Use only the new service leaf already delegated to this worker."""
    require(isinstance(unit, str) and re.fullmatch(r'jw-[a-z0-9-]+\.service', unit),
            'Invalid delegated service unit')
    relative = '/user.slice/user-986.slice/user@986.service/app.slice/' + unit
    require(os.getuid() == UID and os.geteuid() == UID and
            Path('/proc/self/cgroup').read_text().strip() == '0::' + relative,
            'Controller/helper not born in the exact delegated service leaf')
    leaf = Path('/sys/fs/cgroup' + relative)
    require(leaf.resolve(strict=True) == leaf and leaf.stat().st_uid == UID and
            (leaf/'cgroup.type').read_text().strip() == 'domain' and
            not any(path.is_dir() for path in leaf.iterdir()), 'Wrong delegated leaf custody/type')
    interface = leaf/'memory.reclaim'
    require(interface.resolve(strict=True) == interface and interface.stat().st_uid == UID and
            os.access(interface, os.W_OK, effective_ids=True), 'Reclaim interface not delegated')
    identities = {}
    for name, path in (('leaf', leaf), ('interface', interface)):
        info = path.stat(follow_symlinks=False)
        identities[name] = [info.st_dev, info.st_ino, info.st_mode, info.st_uid, info.st_gid]
    require(custody is None or identities == custody, 'Delegated leaf/interface identity changed')
    return leaf, interface, identities


def leaf_resources(leaf):
    def values(name):
        return {key: int(value) for key, value in
                (line.split() for line in (leaf/name).read_text().splitlines())}
    def events():
        return {key: int(value) for key, value in
                (line.split() for line in (leaf/'memory.events').read_text().splitlines())
                if key in MONITORED_EVENTS}
    return {'utc': now(), 'current': int((leaf/'memory.current').read_text()),
            'stat': values('memory.stat'), 'events': events()}


def validate_compiler_placement(rows, leaf):
    expected = '0::' + str(leaf).removeprefix('/sys/fs/cgroup')
    for row in rows:
        if row['comm'] not in ('lean', 'lake'):
            continue
        try:
            current = process_identity(row['pid'])
            require(isinstance(row.get('start_ticks'), str) and row['start_ticks'].isdigit()
                    and isinstance(row.get('cgroup'), str) and not row.get('visibility_error'),
                    'Surviving compiler lacks captured birth/placement evidence')
            if current['start_ticks'] != row.get('start_ticks'):
                row['service_placement_check'] = 'Captured PID exited/reused; old row is not current'
                continue
            value = (Path('/proc')/str(row['pid'])/'cgroup').read_text().strip()
            if process_identity(row['pid'])['start_ticks'] != current['start_ticks']:
                row['service_placement_check'] = 'PID changed during placement observation'
                continue
        except (FileNotFoundError, ProcessLookupError):
            row['service_placement_check'] = 'Captured process vanished during placement observation'
            continue
        require(current['uid'] == UID and row.get('cgroup') == expected and value == expected,
                'Surviving compiler escaped the selected delegated leaf')
        row['service_placement_check'] = 'Same birth and exact selected leaf verified'


def reclaim_members(request, writer_pid=None):
    leaf, interface, _ = service_leaf(request['unit'], request['custody'])
    controller = process_identity(request['controller']['pid'])
    require(controller['uid'] == UID and controller['start_ticks'] ==
            request['controller']['start_ticks'], 'Reclaim controller identity changed')
    actual = json.loads(json.dumps(quiescent_group_snapshot(request['stage_identity'])))
    require(actual == request['stage_snapshot'], 'Reclaim stage/thread quiescence changed')
    expected = {controller['pid'], *(row[0] for row in actual)}
    if writer_pid is not None:
        expected.add(writer_pid)
    members = {int(value) for value in (leaf/'cgroup.procs').read_text().split()}
    require(members == expected, 'Unexpected or escaped delegated leaf member')
    for pid in members:
        row = process_identity(pid)
        require(row['uid'] == UID and int(row['start_ticks']) >= int(controller['start_ticks']) and
                (Path('/proc')/str(pid)/'cgroup').read_text().strip() ==
                '0::' + str(leaf).removeprefix('/sys/fs/cgroup'), 'Reclaim member placement changed')
    return leaf, interface


WIDER_REFILL_PROFILE = 'cpu05-wider-refill-3.25GiB-v1'
DEEPER_REFILL_PROFILE = 'cpu05-deeper-refill-target-3.125GiB-v1'
DEEPER_REFILL_PROFILE_V2 = 'cpu05-deeper-refill-target-3.125GiB-v2'
DEEPER_REFILL_PROFILE_V3 = 'cpu05-deeper-refill-target-3.125GiB-v3'
CPU05_HIGH_CAPACITY_PROFILE = 'cpu05-higher-capacity-refill-4.75-to-4.25GiB-v1'
CPU02_DEEPER_REFILL_PROFILE = 'cpu02-deeper-refill-target-3.125GiB-v1'


def selected_reclaim_profile(config):
    """A future profile is explicit and coherent; omitted means legacy."""
    if 'reclaim_profile' not in config:
        return None
    host = admission_host(config)
    allowed = ((CPU02_DEEPER_REFILL_PROFILE,) if host == 'cpu-02' else
               (CPU03_DEEPER_REFILL_PROFILE,) if host == 'cpu-03' and
               config.get('approved_event_profile') == CPU03_EVENT_EXCEPTION_BINDING else
               (CPU04_DEEPER_REFILL_PROFILE,) if host == 'cpu-04' else
               (WIDER_REFILL_PROFILE, DEEPER_REFILL_PROFILE,
                DEEPER_REFILL_PROFILE_V2,
                DEEPER_REFILL_PROFILE_V3,
                CPU05_HIGH_CAPACITY_PROFILE) if host == 'cpu-05' else ())
    require(type(config['reclaim_profile']) is str and config['reclaim_profile'] in allowed and
            config.get('flow_control') is True,
            'Unsupported captured reclaim profile')
    high_capacity = config['reclaim_profile'] == CPU05_HIGH_CAPACITY_PROFILE
    expected = {'trigger_bytes': 5100273664 if high_capacity else 4026531840,
        'resume_bytes': 4563402752 if high_capacity else 3489660928,
        'early_backlog_files': 8192, 'per_pause_timeout_seconds': 180,
        'aggregate_pause_timeout_seconds': 2400,
        'maximum_pauses': (96 if config['reclaim_profile'] in
                           (DEEPER_REFILL_PROFILE_V3, CPU04_DEEPER_REFILL_PROFILE,
                            CPU05_HIGH_CAPACITY_PROFILE) else
                           64 if config['reclaim_profile'] == DEEPER_REFILL_PROFILE_V2 else 32)}
    policy = config.get('flow_policy')
    require(type(policy) is dict and set(policy) == set(expected) and
            all(type(value) in (int, float) if key.endswith('_seconds')
                else type(value) is int for key, value in policy.items()) and
            policy == expected, 'Wider reclaim profile requires its exact captured flow policy')
    return config['reclaim_profile']


def deficit_reclaim_policy(parent_current, page_size, profile=None, memory_high=None):
    """The selected one-shot formula; integer arithmetic cannot wrap silently."""
    require(profile is None or profile in (WIDER_REFILL_PROFILE, DEEPER_REFILL_PROFILE,
                                           DEEPER_REFILL_PROFILE_V2, DEEPER_REFILL_PROFILE_V3,
                                           CPU02_DEEPER_REFILL_PROFILE, CPU03_DEEPER_REFILL_PROFILE,
                                           CPU04_DEEPER_REFILL_PROFILE,
                                           CPU05_HIGH_CAPACITY_PROFILE),
            'Unsupported reclaim sizing profile')
    high = (memory_high if memory_high is not None else
            5*2**30 if profile == CPU05_HIGH_CAPACITY_PROFILE else int(LIMITS['memory.high']))
    require(type(high) is int and high >= int(LIMITS['memory.high']),
            'Observed memory.high is below the campaign minimum')
    resume = (3355443200 if profile in (DEEPER_REFILL_PROFILE, DEEPER_REFILL_PROFILE_V2,
                                        DEEPER_REFILL_PROFILE_V3,
                                        CPU02_DEEPER_REFILL_PROFILE,
                                        CPU03_DEEPER_REFILL_PROFILE,
                                        CPU04_DEEPER_REFILL_PROFILE) else
              4563402752 if profile == CPU05_HIGH_CAPACITY_PROFILE else
              13*2**28 if profile == WIDER_REFILL_PROFILE else 29*2**27)
    buffer = 32*2**20
    cap = 838860800 if profile else 436207616
    require(type(parent_current) is int and 0 <= parent_current < high,
            'Invalid parent memory sample for reclaim sizing')
    require(type(page_size) is int and 4096 <= page_size <= 65536 and
            page_size & (page_size-1) == 0, 'Invalid reclaim page size')
    amount = (0 if parent_current <= resume else
              ((parent_current-resume+buffer+page_size-1)//page_size)*page_size)
    require(amount <= cap == (838860800 if profile else 436207616),
            'Deficit reclaim request exceeds selected cap')
    return {'parent_current': parent_current, 'resume_bytes': resume,
            'buffer_bytes': buffer, 'page_size': page_size,
            'maximum_request_bytes': cap, 'request_bytes': amount}


def deficit_reclaim_payload(request, expected_profile=None, expected_admission_sha256=None):
    profile = None
    sample = request['parent_sample']
    expected_host = sample['host']
    minimum_free = request.get('root_free_threshold_bytes', MIN_FREE)
    if expected_profile is not None:
        require(expected_profile in (WIDER_REFILL_PROFILE, DEEPER_REFILL_PROFILE,
                                     DEEPER_REFILL_PROFILE_V2, DEEPER_REFILL_PROFILE_V3,
                                     CPU02_DEEPER_REFILL_PROFILE, CPU03_DEEPER_REFILL_PROFILE,
                                     CPU04_DEEPER_REFILL_PROFILE,
                                     CPU05_HIGH_CAPACITY_PROFILE) and
                request.get('reclaim_profile') == expected_profile and
                isinstance(expected_admission_sha256, str) and
                re.fullmatch('[0-9a-f]{64}', expected_admission_sha256),
                'Request omitted or changed independently selected reclaim profile')
        binding = request['admission_binding']
        require(type(binding) is dict and set(binding) == {'path', 'sha256'},
                'Malformed reclaim admission binding')
        require(binding['sha256'] == expected_admission_sha256,
                'Request changed independently selected admission hash')
        admission = owned_path(binding['path'])
        data = admission.read_bytes()
        require(admission == owned_path(request['run'])/'admission.json' and
                hashlib.sha256(data).hexdigest() == binding['sha256'],
                'Reclaim admission hash/path changed')
        config = json.loads(data)
        profile = selected_reclaim_profile(config)
        validate_profile_capacity(config, sample)
        require(request.get('root_free_threshold_bytes', MIN_FREE) == root_free_threshold(config) and
                expected_host == admission_host(config),
                'Reclaim host/root-reserve admission differs from captured configuration')
        require(profile == request['reclaim_profile'] and
                config['runner_sha256'] == request['runner_sha256'] and
                config['delegated_reclaim'] == {'unit': request['unit']},
                'Reclaim admission profile/control/unit mismatch')
    else:
        require(expected_admission_sha256 is None and 'reclaim_profile' not in request and
                'admission_binding' not in request, 'Unselected reclaim admission/profile binding')
    validate_observation(sample, minimum_free, expected_host)
    require(sample['cgroup'] == Path('/proc/self/cgroup').read_text().strip() and
            event_signature(expected_host, sample['events']) ==
            event_signature(expected_host, request['parent_events']) and
            sample['filesystem_error_counters'] == request['filesystem_error_counters'],
            'Captured reclaim parent sample custody changed')
    policy = deficit_reclaim_policy(sample['memory_current'], os.sysconf('SC_PAGE_SIZE'), profile,
                                    observed_memory_high(sample))
    require(request['policy'] == policy and policy['request_bytes'] > 0,
            'Reclaim policy/payload mismatch or unnecessary request')
    return (str(policy['request_bytes'])+' swappiness=0\n').encode('ascii')


def delegated_reclaim_child(path, expected_sha256, expected_profile=None, expected_admission_sha256=None):
    """One hash-bound request, to this child's own validated leaf only."""
    path = owned_path(path)
    require(digest(path) == expected_sha256, 'Reclaim request hash mismatch')
    request = json.loads(path.read_text())
    require(digest(__file__) == request['runner_sha256'], 'Reclaim control hash changed')
    require(path.parent == owned_path(request['run']) and
            re.fullmatch(r'reclaim-[0-9]+-request\.json', path.name), 'Wrong reclaim request path')
    require(os.getppid() == request['controller']['pid'], 'Wrong reclaim helper parent')
    own = process_identity(os.getpid())
    require(own['pgrp'] == os.getpid() and own['session'] == os.getpid(), 'Wrong reclaim helper group')
    leaf, interface = reclaim_members(request, os.getpid())
    minimum_free = request.get('root_free_threshold_bytes', MIN_FREE)
    expected_host = request['parent_sample']['host']
    raw = observe(); validate_observation(raw, minimum_free, expected_host)
    require(raw['boot_id'] == request['parent_sample']['boot_id'] and
            event_signature(expected_host, raw['events']) ==
            event_signature(expected_host, request['parent_events']) and
            raw['filesystem_error_counters'] == request['filesystem_error_counters'],
            'Parent guard changed before reclaim write')
    require(leaf_resources(leaf)['events'] == request['leaf_events'], 'Leaf events changed before write')
    payload = deficit_reclaim_payload(request, expected_profile, expected_admission_sha256)
    terminal = path.with_name(path.name.replace('-request.json', '-terminal.json'))
    attempt = path.with_name(path.name.replace('-request.json', '-attempt.json'))
    row = {'started_utc': now(), 'pid': os.getpid(), 'identity': process_identity(os.getpid()),
           'request_sha256': expected_sha256, 'request': payload.decode('ascii').strip(),
           'policy': request['policy'],
           'interface': str(interface), 'members': sorted(int(x) for x in
               (leaf/'cgroup.procs').read_text().split())}
    with attempt.open('x') as stream:
        json.dump(row, stream); stream.flush(); os.fsync(stream.fileno())
    started = time.monotonic()
    fd = None
    try:
        fd = os.open(interface, os.O_WRONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
        info = os.fstat(fd)
        require([info.st_dev, info.st_ino, info.st_mode, info.st_uid, info.st_gid] ==
                request['custody']['interface'], 'Opened reclaim interface custody changed')
        written = os.write(fd, payload)
        require(written == len(payload), 'Partial reclaim request write')
        row.update(exit_code=0, errno=None, written_bytes=written)
    except OSError as exc:
        row.update(exit_code=1, errno=exc.errno, error=os.strerror(exc.errno))
    except BaseException as exc:
        row.update(exit_code=1, errno=None, error=type(exc).__name__ + ': ' + str(exc))
        raise
    finally:
        if fd is not None:
            os.close(fd)
        row.update(ended_utc=now(), seconds=time.monotonic()-started)
        write_json(terminal, row)
    return row['exit_code']


def classify_reclaim_result(profile, policy, child_exit, terminal, request_sha256,
                            payload, after):
    """Accept exact writes, or deeper-profile EAGAIN only after measured target success."""
    require(type(child_exit) is int and type(terminal) is dict and
            terminal.get('request_sha256') == request_sha256 and
            terminal.get('policy') == policy and
            terminal.get('request') == payload.decode('ascii').strip(),
            'Delegated reclaim terminal custody/policy mismatch')
    if child_exit == 0 and terminal.get('exit_code') == 0 and \
            terminal.get('written_bytes') == len(payload):
        return 'request-written'
    eagain = (profile in (DEEPER_REFILL_PROFILE, DEEPER_REFILL_PROFILE_V2,
                          DEEPER_REFILL_PROFILE_V3,
                          CPU02_DEEPER_REFILL_PROFILE,
                          CPU03_DEEPER_REFILL_PROFILE,
                          CPU04_DEEPER_REFILL_PROFILE,
                          CPU05_HIGH_CAPACITY_PROFILE) and child_exit == 1 and
              terminal.get('exit_code') == 1 and terminal.get('errno') == errno.EAGAIN and
              terminal.get('error') == os.strerror(errno.EAGAIN))
    if eagain:
        require(type(after) is dict and type(after.get('parent_current')) is int and
                after['parent_current'] <= policy['resume_bytes'],
                'Delegated reclaim EAGAIN did not meet the freshly measured target')
        return 'eagain-short-reclaim-target-met'
    raise RuntimeError('Delegated reclaim failed: ' + str(terminal))


class DelegatedReclaim:
    """A bounded fallback after complete epoch advice; never changes limits."""
    def __init__(self, config, run, guard):
        self.config, self.run, self.guard = config, run, guard
        self.profile = selected_reclaim_profile(config)
        self.maximum_requests = config.get('flow_policy', {}).get('maximum_pauses', 32)
        require(type(self.maximum_requests) is int and self.maximum_requests > 0,
                'Invalid reclaim request count budget')
        self.admission_binding = None
        if self.profile:
            admission = owned_path(run/'admission.json')
            data = admission.read_bytes()
            require(json.loads(data) == config,
                    'Wider reclaim admission differs from captured configuration')
            self.admission_binding = {'path': str(admission), 'sha256': hashlib.sha256(data).hexdigest()}
        spec = config['delegated_reclaim']
        require(set(spec) == {'unit'}, 'Unsupported delegated reclaim policy')
        self.unit = spec['unit']
        self.leaf, _, self.custody = service_leaf(self.unit)
        require({int(x) for x in (self.leaf/'cgroup.procs').read_text().split()} == {os.getpid()},
                'New service leaf contains another process')
        self.controller = process_identity(os.getpid())
        self.baseline = leaf_resources(self.leaf)
        self.summary = {'unit': self.unit, 'leaf': str(self.leaf), 'custody': self.custody,
            'controller': self.controller, 'request_policy': 'fresh-deficit-plus-buffer',
            'buffer_bytes': 32*2**20, 'maximum_request_bytes': (838860800 if self.profile else 436207616), 'request_timeout_seconds': 30,
            'requests': 0, 'cleanup_verified': True, 'old_charge_transfer_claimed': False}
        self.sample('service-born')

    def sample(self, label):
        service_leaf(self.unit, self.custody)
        validate_compiler_placement(self.guard.last.get('compiler_processes', []), self.leaf)
        leaf = leaf_resources(self.leaf)
        require(leaf['events'] == self.baseline['events'], 'Delegated leaf memory event or reset')
        row = {'utc': now(), 'label': label, 'leaf': leaf,
               'parent_current': self.guard.last['memory_current'],
               'parent_minus_leaf': self.guard.last['memory_current']-leaf['current']}
        with (self.run/'service-placement.jsonl').open('a') as stream:
            stream.write(json.dumps(row)+'\n'); stream.flush(); os.fsync(stream.fileno())
        return row

    def request(self, process, snapshot, pause_number, checkpoint, deadline):
        checkpoint()
        sample = {key: self.guard.last[key] for key in
            ('utc', 'host', 'boot_id', 'uid', 'worker', 'cgroup', 'root_available_bytes', 'root_available_inodes',
             'root_read_only', 'limits', 'events', 'filesystem_error_counters', 'memory_current')}
        policy = deficit_reclaim_policy(sample['memory_current'], os.sysconf('SC_PAGE_SIZE'), self.profile,
                                        observed_memory_high(self.guard.last))
        if policy['request_bytes'] == 0:
            self.sample('reclaim-unnecessary-'+str(pause_number))
            return  # The caller still performs fresh headroom/custody checks.
        # Leave ten seconds within the existing pause/global budgets for owned
        # helper cleanup. No deadline or guard is extended by this operation.
        require(deadline-time.monotonic() > 10, 'Insufficient remaining reclaim cleanup budget')
        request_deadline = min(time.monotonic()+30, deadline-10)
        request = {'unit': self.unit, 'custody': self.custody, 'controller': self.controller,
            'run': str(self.run), 'runner_sha256': self.config['runner_sha256'],
            'root_free_threshold_bytes': self.guard.minimum_free,
            'stage_identity': process.jw_identity,
            'stage_snapshot': json.loads(json.dumps(snapshot)),
            'parent_events': self.guard.baseline['events'],
            'filesystem_error_counters': self.guard.baseline['filesystem_error_counters'],
            'leaf_events': self.baseline['events'], 'parent_sample': sample, 'policy': policy}
        if self.profile:
            request.update(reclaim_profile=self.profile, admission_binding=self.admission_binding)
        payload = deficit_reclaim_payload(request, self.profile,
                    self.admission_binding['sha256'] if self.admission_binding else None)
        reclaim_members(request)
        path = self.run/f'reclaim-{pause_number}-request.json'
        require(not path.exists(), 'Duplicate reclaim request for this pause')
        write_json(path, request)
        before = self.sample('before-reclaim-'+str(pause_number))
        self.summary['requests'] += 1
        self.summary['last_request_bytes'] = policy['request_bytes']
        require(self.summary['requests'] <= self.maximum_requests,
                'Reclaim request count exceeded')
        child = None
        self.summary['cleanup_verified'] = False
        request_started = time.monotonic()
        try:
            with path.with_suffix('.stdout.txt').open('xb') as out, path.with_suffix('.stderr.txt').open('xb') as err:
                command = [sys.executable, str(Path(__file__).resolve()),
                    '--delegated-reclaim', str(path), digest(path)]
                if self.profile:
                    command.extend([self.profile, self.admission_binding['sha256']])
                child = subprocess.Popen(command, stdout=out, stderr=err,
                    stdin=subprocess.DEVNULL, start_new_session=True)
                capture_stage_identity(child)
                write_json(path.with_name(path.name.replace('-request.json', '-launch.json')),
                           {'identity': child.jw_identity, 'utc': now()})
                while child.poll() is None:
                    checkpoint()
                    require(time.monotonic() < request_deadline, 'Delegated reclaim request timeout')
                    require(json.loads(json.dumps(quiescent_group_snapshot(process.jw_identity))) ==
                            request['stage_snapshot'], 'Reclaim stage custody changed while waiting')
                    time.sleep(.05)
                completed = time.monotonic()
                self.summary['last_request_observed_seconds'] = completed-request_started
                require(completed <= request_deadline, 'Delegated reclaim completed after request deadline')
                checkpoint()
                require(not any(row['state'] != 'Z' for row in owned_group_members(child.jw_identity)),
                        'Reclaim helper left live descendants')
                terminal = json.loads(path.with_name(path.name.replace('-request.json', '-terminal.json')).read_text())
                after = self.sample('after-reclaim-'+str(pause_number))
                write_json(path.with_name(path.name.replace('-request.json', '-measurement.json')),
                           {'before': before, 'after': after, 'child_exit': child.returncode,
                            'terminal_sha256': digest(path.with_name(path.name.replace('-request.json', '-terminal.json')))})
                result = classify_reclaim_result(self.profile, policy, child.returncode,
                    terminal, digest(path), payload, after)
                self.summary['last_result'] = result
                if result == 'eagain-short-reclaim-target-met':
                    self.summary['eagain_target_met_count'] = self.summary.get('eagain_target_met_count', 0)+1
                reclaim_members(request)
        finally:
            identity = getattr(child, 'jw_identity', None) if child is not None else None
            live = (any(row['state'] != 'Z' for row in owned_group_members(identity))
                    if identity is not None else child is not None and child.poll() is None)
            if live:
                # A request can block in the kernel. Never claim cleanup from
                # a signal alone; preserve an explicit unknown state on expiry.
                self.summary['cleanup_verified'] = False
                require(identity is not None, 'UNKNOWN_DO_NOT_DUPLICATE: reclaim helper custody absent')
                rows = owned_group_members(identity)
                if any(row['state'] != 'Z' for row in rows):
                    try:
                        os.killpg(child.pid, signal.SIGTERM); os.killpg(child.pid, signal.SIGCONT)
                    except ProcessLookupError:
                        pass
                guard_errors = []
                def cleanup_checkpoint():
                    try:
                        checkpoint()
                    except BaseException as exc:
                        # Preserve the guard failure but finish owned cleanup.
                        if not guard_errors:
                            guard_errors.append(type(exc).__name__ + ': ' + str(exc))
                def alive():
                    return child.poll() is None or any(row['state'] != 'Z'
                        for row in owned_group_members(identity))
                stop_deadline = min(deadline, time.monotonic()+5)
                while alive() and time.monotonic() < stop_deadline:
                    cleanup_checkpoint()
                    time.sleep(.05)
                if alive():
                    owned_group_members(identity)
                    try:
                        os.killpg(child.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    while alive() and time.monotonic() < deadline:
                        cleanup_checkpoint()
                        time.sleep(.05)
                require(not alive(),
                    'UNKNOWN_DO_NOT_DUPLICATE: reclaim helper cleanup incomplete')
                self.summary['cleanup_verified'] = True
                if guard_errors:
                    self.summary['cleanup_guard_error'] = guard_errors[0]
                    raise RuntimeError(guard_errors[0])
            elif child is None:
                # Popen did not return a child handle; no successful launch is
                # asserted. Preserve pending/unknown on an interrupted spawn.
                self.summary['cleanup_verified'] = False
            elif child.poll() is not None and identity is not None:
                self.summary['cleanup_verified'] = True


def metadata_records(manifest):
    """Only the exact separately qualified excluded-metadata cohort is eligible."""
    with gzip.open(manifest, 'rt', encoding='utf-8') as stream:
        for line in stream:
            require(len(line) <= 16384, 'Metadata custody record exceeds bound')
            item = json.loads(line)
            require(item['uid'] == UID and stat.S_ISREG(item['mode']),
                    'Metadata custody owner/type is not the designated worker regular file')
            path = Path(item['path'])
            require(not path.is_absolute() and '..' not in path.parts
                    and len(path.parts) > 3 and path.parts[1:3] == ('.lake', 'build'),
                    'Metadata custody escapes dependency build root')
            suffix = path.suffix
            kind = ('trace' if suffix == '.trace' else 'ilean-hash' if path.name.endswith('.ilean.hash')
                    else 'ir-hash' if path.name.endswith('.ir.hash') else 'other-hash')
            require((suffix == '.trace' or suffix == '.hash' and '.olean' not in path.name)
                    and item['class'] == 'previously-excluded-'+kind,
                    'Metadata custody class is not authorized')
            item['stat_identity'] = PausedInputEpoch.STAT.pack(item['device'], item['inode'],
                item['mode'], item['uid'], item['bytes'], item['mtime_ns'], item['ctime_ns'])
            yield item


def qualify_metadata(config, destination):
    manifest, root = owned_path(config['manifest']), owned_path(config['root'])
    require(digest(manifest) == config['sha256'], 'Metadata custody manifest changed')
    count, seen = 0, set()
    for item in metadata_records(manifest):
        path = root/item['path']
        require(item['path'] not in seen, 'Duplicate metadata custody member')
        seen.add(item['path'])
        require(path.resolve(strict=True) == path, 'Metadata custody path is not canonical')
        fd = os.open(path, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW | os.O_NOATIME)
        try:
            expected = item['stat_identity']
            require(PausedInputEpoch.stat_bytes(os.fstat(fd)) == expected,
                    'Metadata custody stat changed before fresh qualification')
            h = hashlib.sha256()
            while data := os.read(fd, 2**20):
                h.update(data)
            require(h.hexdigest() == item['sha256'], 'Metadata content changed before fresh qualification')
            require(PausedInputEpoch.stat_bytes(os.fstat(fd)) == expected,
                    'Metadata custody stat changed during fresh qualification')
        finally:
            os.close(fd)
        count += 1
    require(count == config['files'], 'Metadata custody count differs from reviewed offer')
    write_json(destination, {'schema': 'jw-metadata-qualification-v1', 'utc': now(),
        'files': count, 'manifest_sha256': config['sha256'], 'root': str(root),
        'status': 'qualified', 'content_hashes_and_stat_verified': True})


class PausedStageCompleted(Exception):
    """The captured stage genuinely exited; no group needs a resume signal."""


class PausedInputEpoch:
    """One sealed union, with fresh per-member receipts independent of old rounds.

    Reuses the historical map's keys. Compact state replaces its boolean values;
    ordinary-only keys are removed on close. No second full path catalog exists.
    Input bytes are never read here: custody comes from the qualified inventories
    and the exact stat identities sealed before advice.
    """
    STAT = struct.Struct('<7Q')
    ORDINAL = struct.Struct('<Q')
    RECEIPT = struct.Struct('<QQQ')
    STATE_BYTES = 66  # stat56, ordinal8, historical/ordinary flags, success byte
    HISTORICAL, ORDINARY = 1, 2
    MAX_MEMBERS = 196608

    def __init__(self, replay, identity, snapshot, checkpoint, process=None):
        self.replay, self.identity, self.snapshot = replay, identity, snapshot
        self.process = process
        self.checkpoint = checkpoint
        self.members = replay.recent_input_mappings
        self.epoch = replay.flow_summary['pauses']
        self.started_ns = time.monotonic_ns()
        self.phase = 'historical'
        self.phase_started = time.monotonic()
        self.stats = {'epoch': self.epoch, 'started_monotonic_ns': self.started_ns,
            'mapping_scans': 0, 'mapping_lines': 0, 'rejected_mapping_lines': 0,
            'qualified_records': 0, 'members': 0, 'receipts': 0, 'advised_bytes': 0,
            'maximum_slice_seconds': 0.0, 'complete': False, 'slices': 0,
            'phase_seconds': {}, 'snapshot_seconds': 0.0, 'guard_seconds': 0.0,
            'work_seconds': 0.0, 'evidence_seconds': 0.0, 'phase_counts': {},
            'current_ordinal': None}
        prefix = replay.run/f'paused-epoch-{self.epoch:03d}'
        self.manifest = prefix.with_suffix('.cohort.jsonl.gz').open('wb')
        self.receipts = prefix.with_suffix('.receipts.bin').open('wb')
        self.manifest_hash, self.receipt_hash = hashlib.sha256(), hashlib.sha256()
        self.compressor = zlib.compressobj(level=1, wbits=31)
        self.work = self.operations()

    def enter_phase(self, phase):
        tick = time.monotonic()
        self.stats['phase_seconds'][self.phase] = tick-self.phase_started
        self.phase, self.phase_started = phase, tick

    def count(self, name, amount=1):
        counters = self.stats['phase_counts'].setdefault(self.phase, {})
        counters[name] = counters.get(name, 0)+amount

    def check_snapshot(self):
        started = time.monotonic()
        current = quiescent_group_snapshot(self.identity)
        self.stats['snapshot_seconds'] += time.monotonic()-started
        if not current and self.process is not None and self.process.poll() is not None:
            raise PausedStageCompleted()
        require(current == self.snapshot, 'Paused epoch membership/thread/quiescence changed')

    def check_guard(self):
        started = time.monotonic()
        self.checkpoint()
        self.stats['guard_seconds'] += time.monotonic()-started

    @classmethod
    def stat_bytes(cls, info):
        return cls.STAT.pack(info.st_dev, info.st_ino, info.st_mode, info.st_uid,
                             info.st_size, info.st_mtime_ns, info.st_ctime_ns)

    def open_member(self, value, expected=None):
        self.count('open_calls')
        path = Path(value)
        require(path.is_absolute() and path.resolve(strict=True) == path
                and any(path.is_relative_to(root) for root in self.replay.immutable_input_roots),
                'Paused epoch input path is not canonical/in qualified roots')
        fd = os.open(path, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW | os.O_NOATIME)
        try:
            info = os.fstat(fd)
            require(info.st_uid == UID and stat.S_ISREG(info.st_mode),
                    'Paused epoch input owner/type changed')
            packed = self.stat_bytes(info)
            if expected is not None:
                require(packed == expected, 'Paused epoch input stat identity changed')
            return fd, packed
        except BaseException:
            os.close(fd)
            raise

    def advise_member(self, value, expected):
        """Revalidate and advise one sealed member without shared-state writes."""
        path = Path(value)
        require(path.is_absolute() and path.resolve(strict=True) == path
                and any(path.is_relative_to(root) for root in self.replay.immutable_input_roots),
                'Paused epoch input path is not canonical/in qualified roots')
        fd = os.open(path, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW | os.O_NOATIME)
        try:
            info = os.fstat(fd)
            require(info.st_uid == UID and stat.S_ISREG(info.st_mode),
                    'Paused epoch input owner/type changed')
            packed = self.stat_bytes(info)
            require(packed == expected, 'Paused epoch input stat identity changed')
            os.posix_fadvise(fd, 0, 0, os.POSIX_FADV_DONTNEED)
            require(self.stat_bytes(os.fstat(fd)) == packed,
                    'Paused epoch input changed during advice')
        finally:
            os.close(fd)
        return time.monotonic_ns()

    def advice_batch_receipts(self, batch):
        """Write ordered success receipts only after every batch advice succeeds."""
        completed_members = []
        try:
            for path, value, future in batch:
                completed_members.append((path, value, future.result()))
        except BaseException:
            for _, _, future in batch:
                future.cancel()
            raise
        for path, value, completed in completed_members:
            require(value[65] == 0, 'Duplicate paused epoch receipt')
            self.count('open_calls')
            self.count('advice_calls')
            require(completed >= self.started_ns, 'Pre-epoch advice receipt')
            ordinal = self.ORDINAL.unpack_from(value, 56)[0]
            self.stats['current_ordinal'] = ordinal
            receipt = self.RECEIPT.pack(self.epoch, ordinal, completed)
            evidence_started = time.monotonic()
            self.receipts.write(receipt)
            self.receipt_hash.update(receipt)
            self.stats['evidence_seconds'] += time.monotonic()-evidence_started
            value[65] = 1  # Only after successful advice AND receipt write.
            self.stats['receipts'] += 1
            self.stats['advised_bytes'] += self.STAT.unpack(value[:56])[4]
            yield

    def bind(self, path, flags, size=None, expected=None, mapping_identity=None):
        self.count('bind_calls')
        previous = self.members.get(path)
        if isinstance(previous, bytearray):
            self.count('overlapping_bind_calls')
            packed = previous[:56]
        elif path in self.replay.recent_input_stat:
            # The immediately prior completed epoch's advice pass opened and
            # checked every retained member against this exact stat identity.
            # Reuse that identity while rebuilding the next union; the current
            # epoch still reopens and verifies every member in its advice phase
            # before any resume decision.
            packed = self.replay.recent_input_stat[path]
            require(type(packed) is bytes and len(packed) == self.STAT.size,
                    'Cached historical input identity is malformed')
            self.count('historical_stat_reuses')
        else:
            fd, packed = self.open_member(path, expected)
            os.close(fd)
        device, inode, _, _, actual_size, _, _ = self.STAT.unpack(packed)
        if size is not None:
            require(actual_size == size, 'Paused epoch qualified size changed')
        if expected is not None:
            require(packed == expected, 'Paused epoch overlapping member identity changed')
        if mapping_identity is not None:
            require((os.major(device), os.minor(device), inode) == mapping_identity,
                    'Paused epoch mapped device/inode differs from sealed input identity')
        if isinstance(previous, bytearray):
            # A bound path has already received the epoch's canonical open/stat.
            # Kernel map device/inode or Q's exact expected identity joins it;
            # advice still reopens canonically and checks every sealed field.
            self.count('identity_join_reuses')
            previous[64] |= flags
            return
        require(len(self.members) < self.MAX_MEMBERS or path in self.members,
                'Paused epoch union exceeded bounded catalog')
        value = bytearray(self.STATE_BYTES)
        self.count('new_bound_members')
        value[:56] = packed
        value[64] = flags
        self.members[path] = value

    def mapping_lines(self, pid, birth):
        try:
            require(process_identity(pid)['start_ticks'] == birth, 'Paused epoch PID birth changed')
            with (Path('/proc')/str(pid)/'maps').open() as stream:
                yield from stream
        except FileNotFoundError:
            # Only /proc disappearance enters this completion path; missing
            # immutable input files still fail custody unconditionally.
            self.check_guard()
            self.check_snapshot()
            raise

    def operations(self):
        # Existing booleans and incomplete active rounds deliberately contribute
        # no completion state to this epoch.
        for path in self.members:
            self.bind(path, self.HISTORICAL)
            yield
        self.enter_phase('mapping-snapshot')
        prefixes = tuple(str(root)+'/' for root in self.replay.immutable_input_roots)
        for pid, birth, _ in self.snapshot:
            for line in self.mapping_lines(pid, birth):
                fields = line.rstrip('\n').split(None, 5)
                path = fields[5] if len(fields) == 6 else ''
                self.stats['mapping_lines'] += 1
                if path.startswith(prefixes):
                    require(not path.endswith(' (deleted)'), 'Paused epoch qualified mapping was deleted')
                    device = fields[3].split(':')
                    require(len(device) == 2 and int(fields[4]) > 0,
                            'Paused epoch mapping lacks regular-file device/inode')
                    mapping_identity = (int(device[0], 16), int(device[1], 16), int(fields[4]))
                    self.bind(path, self.HISTORICAL, mapping_identity=mapping_identity)
                else:
                    self.stats['rejected_mapping_lines'] += 1
                yield
            self.stats['mapping_scans'] += 1
        self.enter_phase('qualified-union')
        for record in self.replay.qualified_read_records():
            self.stats['qualified_records'] += 1
            if record is not None:
                root, item = record
                self.bind(str(root/item['path']), self.ORDINARY, item['bytes'], item.get('stat_identity'))
            yield
        self.enter_phase('seal')
        for ordinal, (path, value) in enumerate(self.members.items()):
            self.stats['current_ordinal'] = ordinal
            require(isinstance(value, bytearray) and value[65] == 0,
                    'Paused epoch inherited success state')
            self.ORDINAL.pack_into(value, 56, ordinal)
            record = (json.dumps([self.epoch, ordinal, path, value[:56].hex(), value[64]],
                                 separators=(',', ':'))+'\n').encode()
            evidence_started = time.monotonic()
            compressed = self.compressor.compress(record)
            self.manifest.write(compressed); self.manifest_hash.update(compressed)
            self.stats['evidence_seconds'] += time.monotonic()-evidence_started
            yield
        compressed = self.compressor.flush()
        self.manifest.write(compressed); self.manifest_hash.update(compressed)
        self.manifest.flush()
        self.stats['members'] = len(self.members)
        self.stats['cohort_sha256'] = self.manifest_hash.hexdigest()
        self.replay.flow_record('epoch-sealed', epoch=dict(self.stats))
        self.enter_phase('advice')
        # Proven ordinary-read classes first. Overlaps are advised only here;
        # the second traversal skips them and does not make a second receipt.
        # Advice I/O is concurrent but bounded; custody checks, completions, and
        # receipts remain exact and receipts stay in canonical ordinal order.
        with ThreadPoolExecutor(max_workers=PAUSED_EPOCH_ADVICE_WORKERS) as advice_pool:
            for ordinary in (True, False):
                batch = []
                for path, value in self.members.items():
                    if bool(value[64] & self.ORDINARY) != ordinary:
                        continue
                    require(value[65] == 0, 'Duplicate paused epoch receipt')
                    future = advice_pool.submit(self.advise_member, path, bytes(value[:56]))
                    batch.append((path, value, future))
                    if len(batch) == PAUSED_EPOCH_ADVICE_BATCH_SIZE:
                        yield from self.advice_batch_receipts(batch)
                        batch = []
                if batch:
                    yield from self.advice_batch_receipts(batch)
        self.enter_phase('verify-receipts')
        for value in self.members.values():
            require(value[65] == 1, 'Missing post-epoch successful advice receipt')
            yield
        require(self.stats['receipts'] == len(self.members), 'Paused epoch receipt cardinality mismatch')
        self.receipts.flush()
        self.stats['receipts_sha256'] = self.receipt_hash.hexdigest()
        self.stats['cohort_bytes'] = self.manifest.tell()
        self.stats['receipts_bytes'] = self.receipts.tell()
        for output in (self.manifest, self.receipts):
            os.fsync(output.fileno())
            os.posix_fadvise(output.fileno(), 0, 0, os.POSIX_FADV_DONTNEED)
            yield
        self.stats['complete'] = True
        self.enter_phase('complete')

    def step(self):
        try:
            return self.checked_step()
        except BaseException:
            self.stats['complete'] = False
            self.stats['failed_phase'] = self.phase
            self.stats['phase_seconds'][self.phase] = time.monotonic()-self.phase_started
            self.phase = 'invalidated'
            raise

    def checked_step(self):
        self.check_guard()
        self.check_snapshot()
        started = time.monotonic()
        slice_phase = self.phase
        budget = (0.05 if slice_phase == 'mapping-snapshot' else
                  PAUSED_EPOCH_ADVICE_SLICE_SECONDS if slice_phase == 'advice' else 0.2)
        try:
            for _ in range(1024):
                next(self.work)
                self.count('visited_operations')
                if self.phase != slice_phase or time.monotonic()-started >= budget:
                    break
        except StopIteration:
            pass
        self.stats['maximum_slice_seconds'] = max(self.stats['maximum_slice_seconds'],
                                                  time.monotonic()-started)
        self.stats['work_seconds'] += time.monotonic()-started
        self.stats['slices'] += 1
        # The next slice rechecks resource and process custody before more I/O.
        # The bounded slice and the final pre-resume checks preserve continuous
        # monitoring without repeating the same expensive snapshot twice here.
        return self.stats['complete']

    def close(self, restore=True):
        self.work.close()
        self.manifest.close(); self.receipts.close()
        if not restore:
            return
        # Bounded rotation restores the existing active historical map without
        # copying its keys or retaining ordinary-only catalog state.
        started = time.monotonic()
        unadvised = 0
        next_stat = {}
        previous_stat = self.replay.recent_input_stat
        for index in range(len(self.members)):
            path, value = self.members.popitem(last=False)
            if not isinstance(value, bytearray) or value[64] & self.HISTORICAL:
                advised = bool(value[65]) if isinstance(value, bytearray) else value
                self.members[path] = advised
                unadvised += not advised
                if isinstance(value, bytearray):
                    if self.stats['complete'] and value[65] == 1:
                        next_stat[path] = bytes(value[:self.STAT.size])
                    elif path in previous_stat:
                        next_stat[path] = previous_stat[path]
            if index % 1024 == 0 or time.monotonic()-started >= 0.05:
                self.checkpoint(); started = time.monotonic()
        self.replay.recent_input_stat = next_stat
        self.replay.advice_round_remaining = self.replay.advice_round_size = 0
        self.replay.input_cache_advice['unadvised_files'] = unadvised


def artifact_reuse_scope(receipt, previous_admission, current_admission):
    require(receipt.get('schema') == 'jw-compiler-result-v1', 'Wrong prior artifact receipt schema')
    require(receipt.get('stages', {}).get('build', {}).get('exit_code') == 0,
            'Prior project build did not succeed')
    for field in ('source_commit', 'toolchain_inventory_sha256', 'dependency_source_root'):
        require(previous_admission.get(field) and previous_admission[field] == current_admission.get(field),
                'Artifact reuse changed compiler/dependency/source basis: ' + field)
    if receipt.get('purpose') in ('isolated-module-diagnostic', 'module-feedback'):
        require(receipt.get('status') == 'completed' and receipt.get('exit_code') == 0
                and receipt.get('build_targets'), 'Prior bounded build is not terminal-successful')
        return {'kind': 'bounded-module-build-only', 'targets': receipt['build_targets'],
                'certification': False}
    require(all(receipt['stages'].get(name, {}).get('exit_code') == 0
                for name in ('audit', 'audit-profile')), 'Prior full project audit/profile not successful')
    return {'kind': 'successful-build-and-original-audit-stages',
            'certification': False, 'note': 'Cache reuse only; current full acceptance stages remain required'}


def project_build_order(source, root='ExoticCCR'):
    """Dependency order for the captured default library root, without source edits."""
    import tomllib
    config = tomllib.loads((source/'lakefile.toml').read_text())
    require(config.get('defaultTargets') == [root], 'Unexpected default project build target')
    libraries = config.get('lean_lib', [])
    require(len(libraries) == 1 and libraries[0].get('name') == root
            and not any(k in libraries[0] for k in ('globs', 'roots', 'srcDir', 'defaultFacets')),
            'Sequential root closure requires captured default library configuration')
    done, active, order = set(), set(), []
    def visit(name):
        require(name not in active, 'Cyclic project import graph')
        if name in done:
            return
        require(re.fullmatch(r'ExoticCCR(?:\.[A-Za-z0-9_]+)*', name), 'Unsafe project module name')
        path = source.joinpath(*name.split('.')).with_suffix('.lean')
        require(path.is_file(), 'Project import source absent: ' + name)
        active.add(name)
        for imports in re.findall(r'^import\s+([^\r\n]+)', path.read_text(), re.M):
            for dependency in imports.split('--', 1)[0].split():
                require(re.fullmatch(r'[A-Za-z][A-Za-z0-9_.]*', dependency), 'Unsupported import syntax')
                if dependency == root or dependency.startswith(root+'.'):
                    visit(dependency)
        active.remove(name); done.add(name); order.append(name)
    visit(root)
    return order


class Replay:
    def __init__(self, config, run, guard):
        self.config, self.run, self.guard = config, run, guard
        profile = selected_reclaim_profile(config)
        self.delegated_reclaim = (DelegatedReclaim(config, run, guard)
                                  if config.get('delegated_reclaim') else None)
        self.source = run/'source'
        self.stages = {}
        self.environment = os.environ.copy()
        self.environment.update(LEAN_NUM_THREADS='1', OMP_NUM_THREADS='1',
            RAYON_NUM_THREADS='1',
            GIT_TERMINAL_PROMPT='0', GIT_ASKPASS='/bin/false', SSH_ASKPASS='/bin/false',
            XDG_CACHE_HOME=str(owned_path(config['workspace'])/'cache'))
        (run/'logs').mkdir()
        self.cache_advice = {'files': 0, 'bytes': 0, 'memo_limit': CACHE_ADVICE_MEMO_LIMIT,
            'maximum_memo_entries': 0, 'memo_evictions': 0,
            'scope': 'Only this campaign worker-owned files; fsync and POSIX_FADV_DONTNEED'}
        self.cache_advised = OrderedDict()
        self.cache_iterator = None
        self.active_pgid = None
        self.immutable_input_roots = []
        self.recent_input_mappings = OrderedDict()
        self.recent_input_stat = {}
        self.last_mapping_scan = 0.0
        self.mapping_iterator = None
        self.qualified_read_inventories = []
        self.qualified_metadata = None
        self.qualified_read_iterator = None
        self.read_cache_advice = {'records_scanned': 0, 'files': 0, 'bytes': 0,
            'rounds_completed': 0, 'round_files': 0, 'last_round_files': 0,
            'maximum_call_seconds': 0.0,
            'scope': 'Repeating advice for freshly hash-qualified dependency .lean/olean-family hashes and explicitly qualified metadata content/stat manifest members; no unchanged-file deduplication or input content reads during advice'}
        self.advice_round_remaining = 0
        self.advice_round_size = 0
        self.input_cache_advice = {'calls': 0, 'bytes': 0, 'mapping_scans': 0,
            'maximum_recent_files': 0, 'mapping_lines_scanned': 0, 'mapping_lines_skipped': 0,
            'mapping_rounds_completed': 0, 'unique_files_advised': 0, 'unadvised_files': 0,
            'vanished_mapped_files_skipped': 0,
            'advice_rounds_completed': 0, 'largest_completed_advice_round_files': 0,
            'maximum_discovery_seconds': 0.0, 'maximum_advice_seconds': 0.0,
            'scope': 'Repeated POSIX_FADV_DONTNEED for campaign-root files observed in owned native process mappings; a mapped path that disappears before advice is skipped and counted; no process memory or file-content mutation'}
        # One selected calibration after CPU05 v03's complete paused epoch
        # retained 3,707,056,128 bytes. The actual complete Basic working set
        # remains unverified; this changes only internal stage flow control.
        self.flow_trigger = 5100273664 if profile == CPU05_HIGH_CAPACITY_PROFILE else 15*2**28
        self.flow_resume = (4563402752 if profile == CPU05_HIGH_CAPACITY_PROFILE else
                            13*2**28 if profile else 29*2**27)
        self.flow_pause_timeout = 180.0
        self.flow_aggregate_timeout = 600.0
        if 'flow_policy' in config:
            captured_policy = config['flow_policy']
            require(type(captured_policy) is dict, 'Captured flow policy must be an object')
            allocation = captured_policy.get('aggregate_pause_timeout_seconds')
            require(type(allocation) in (int, float) and allocation in (600, 2400),
                    'Unsupported captured aggregate pause allocation')
            # The larger future-offer allocation is explicit. CPU-05 v2/v3
            # profiles allow 64/96 epochs, but aggregate and per-pause time
            # limits remain fixed. Legacy offers retain 600; there is no
            # runtime escalation or other budget change.
            self.flow_aggregate_timeout = float(allocation)
        policy = {'trigger_bytes': self.flow_trigger, 'resume_bytes': self.flow_resume,
            'early_backlog_files': 8192, 'per_pause_timeout_seconds': self.flow_pause_timeout,
            'aggregate_pause_timeout_seconds': self.flow_aggregate_timeout,
            'maximum_pauses': (96 if profile in
                               (DEEPER_REFILL_PROFILE_V3, CPU04_DEEPER_REFILL_PROFILE,
                                CPU05_HIGH_CAPACITY_PROFILE) else
                               64 if profile == DEEPER_REFILL_PROFILE_V2 else 32)}
        if 'flow_policy' in config:
            require(set(captured_policy) == set(policy), 'Captured flow policy fields changed')
            require(all(type(value) in (int, float) if key.endswith('_seconds')
                        else type(value) is int for key, value in captured_policy.items()),
                    'Malformed captured flow policy value')
            require(captured_policy == policy, 'Captured flow policy does not match execution controls')
        self.flow_summary = {'enabled': config.get('flow_control', False), 'pauses': 0,
            'total_pause_seconds': 0.0, **policy}

    def owned_mapping_lines(self):
        prefixes = tuple(str(root)+'/' for root in self.immutable_input_roots)
        rows = sorted(self.guard.last.get('compiler_processes', []), key=lambda row: row['comm'] != 'lean')
        for row in rows:
            if row['uid'] != UID or row['comm'] not in ('lean', 'lake'):
                continue
            try:
                if os.getpgid(row['pid']) != self.active_pgid:
                    continue
                with (Path('/proc')/str(row['pid'])/'maps').open() as stream:
                    for line in stream:
                        fields = line.rstrip('\n').split(None, 5)
                        path = fields[5] if len(fields) == 6 else ''
                        # Yield even a rejected line so skipped inputs cannot
                        # evade the parsing budget. Actual advice rechecks the
                        # resolved root, file type and worker ownership.
                        yield path if path.startswith(prefixes) and not path.endswith(' (deleted)') else None
            except (FileNotFoundError, ProcessLookupError):
                continue

    def release_import_readahead(self, budget=0.2, discovery_budget=0.05):
        if not self.immutable_input_roots or self.active_pgid is None:
            return
        started = time.monotonic()
        if self.mapping_iterator is None and started-self.last_mapping_scan >= 2.0:
            self.mapping_iterator = self.owned_mapping_lines()
            self.last_mapping_scan = started
            self.input_cache_advice['mapping_scans'] += 1
        if self.mapping_iterator is not None:
            for _ in range(4096):
                try:
                    path = next(self.mapping_iterator)
                except StopIteration:
                    self.mapping_iterator = None
                    self.input_cache_advice['mapping_rounds_completed'] += 1
                    break
                self.input_cache_advice['mapping_lines_scanned'] += 1
                if path is None:
                    self.input_cache_advice['mapping_lines_skipped'] += 1
                elif path not in self.recent_input_mappings:
                    require(len(self.recent_input_mappings) < 65536, 'Immutable input mapping inventory exceeded bound')
                    self.recent_input_mappings[path] = False
                    self.input_cache_advice['unadvised_files'] += 1
                if time.monotonic()-started >= discovery_budget:
                    break
        self.input_cache_advice['maximum_discovery_seconds'] = max(
            self.input_cache_advice['maximum_discovery_seconds'], time.monotonic()-started)
        self.input_cache_advice['maximum_recent_files'] = max(
            self.input_cache_advice['maximum_recent_files'], len(self.recent_input_mappings))
        # Advice owns a fresh, independent budget. Discovery may not consume it.
        started = time.monotonic()
        for _ in range(min(4096, len(self.recent_input_mappings))):
            if self.advice_round_remaining == 0:
                self.advice_round_remaining = self.advice_round_size = len(self.recent_input_mappings)
            path, advised = self.recent_input_mappings.popitem(last=False)
            self.recent_input_mappings[path] = True
            try:
                size = advise_immutable_input(path, self.immutable_input_roots)
            except FileNotFoundError as exc:
                # Only the Lake cache executable's atomic temp-file race is
                # skippable. Missing immutable Lean inputs remain fatal.
                require(is_vanished_lake_cache_executable(
                    path, self.immutable_input_roots, exc),
                    'Missing mapped input was not an atomic Lake cache executable')
                self.input_cache_advice['vanished_mapped_files_skipped'] += 1
                if not advised:
                    self.input_cache_advice['unadvised_files'] -= 1
                self.recent_input_mappings.pop(path, None)
            else:
                self.input_cache_advice['calls'] += 1
                self.input_cache_advice['bytes'] += size
                if not advised:
                    self.input_cache_advice['unique_files_advised'] += 1
                    self.input_cache_advice['unadvised_files'] -= 1
            self.advice_round_remaining -= 1
            if self.advice_round_remaining == 0:
                self.input_cache_advice['advice_rounds_completed'] += 1
                self.input_cache_advice['largest_completed_advice_round_files'] = max(
                    self.input_cache_advice['largest_completed_advice_round_files'], self.advice_round_size)
            if time.monotonic() - started >= budget:
                break
        self.input_cache_advice['maximum_advice_seconds'] = max(
            self.input_cache_advice['maximum_advice_seconds'], time.monotonic()-started)
        if self.guard.samples % 5 == 0:
            write_json(self.run/'immutable-input-cache-advice.json', self.input_cache_advice)

    def drain_recent_inputs(self, after_stage):
        require(not compiler_processes(), 'Compiler remained live between sequential project stages')
        self.guard.check()
        before = self.guard.last
        count, total, vanished = 0, 0, 0
        vanished_paths = []
        for path in self.recent_input_mappings:
            try:
                total += advise_immutable_input(path, self.immutable_input_roots)
                count += 1
            except FileNotFoundError as exc:
                require(is_vanished_lake_cache_executable(
                    path, self.immutable_input_roots, exc),
                    'Missing drained input was not an atomic Lake cache executable')
                vanished += 1
                vanished_paths.append(path)
            if (count + vanished) % 256 == 0:
                self.guard.check()
        self.guard.check()
        for path in vanished_paths:
            self.recent_input_mappings.pop(path, None)
        self.input_cache_advice['vanished_mapped_files_skipped'] += vanished
        with (self.run/'inter-module-cache-drains.jsonl').open('a', encoding='utf-8') as stream:
            stream.write(json.dumps({'utc': now(), 'after_stage': after_stage,
                'files': count, 'vanished_mapped_files_skipped': vanished,
                'advised_bytes': total, 'before': before, 'after': self.guard.last})+'\n')
            stream.flush(); os.fsync(stream.fileno())

    def qualified_read_records(self):
        for root, inventory in self.qualified_read_inventories:
            for item in stream_inventory(inventory):
                relative = Path(item['path'])
                require(not relative.is_absolute() and '..' not in relative.parts,
                        'Qualified read input escapes inventory root')
                # Lake may rewrite .olean.private.hash while compiling a
                # downstream module. It is mutable build metadata, not an
                # immutable compiler input eligible for qualified read advice.
                selected = relative.suffix == '.lean' or relative.name.endswith('.olean.hash')
                # Every skipped record still consumes the caller's bounded work.
                yield (root, item) if selected else None
        if self.qualified_metadata:
            root, manifest = self.qualified_metadata
            for item in metadata_records(manifest):
                yield root, item

    def restart_read_advice_round(self):
        if self.qualified_read_iterator is not None:
            self.qualified_read_iterator.close()
        self.qualified_read_iterator = None
        self.read_cache_advice['round_files'] = 0

    def release_qualified_read_cache(self, budget=0.05):
        if not self.qualified_read_inventories and not self.qualified_metadata:
            return
        started = time.monotonic()
        if self.qualified_read_iterator is None:
            self.qualified_read_iterator = self.qualified_read_records()
        for _ in range(1024):
            try:
                record = next(self.qualified_read_iterator)
            except StopIteration:
                self.qualified_read_iterator = None
                self.read_cache_advice['rounds_completed'] += 1
                self.read_cache_advice['last_round_files'] = self.read_cache_advice['round_files']
                self.read_cache_advice['round_files'] = 0
                break
            self.read_cache_advice['records_scanned'] += 1
            if record is not None:
                root, item = record
                if 'stat_identity' in item:
                    path = root/item['path']
                    require(path.resolve(strict=True) == path, 'Qualified metadata path changed')
                    fd = os.open(path, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW | os.O_NOATIME)
                    try:
                        require(PausedInputEpoch.stat_bytes(os.fstat(fd)) == item['stat_identity'],
                                'Qualified metadata identity changed before advice')
                        os.posix_fadvise(fd, 0, 0, os.POSIX_FADV_DONTNEED)
                        require(PausedInputEpoch.stat_bytes(os.fstat(fd)) == item['stat_identity'],
                                'Qualified metadata identity changed during advice')
                        size = item['bytes']
                    finally:
                        os.close(fd)
                else:
                    size = advise_immutable_input(root/item['path'], [root], item['bytes'])
                self.read_cache_advice['files'] += 1
                self.read_cache_advice['bytes'] += size
                self.read_cache_advice['round_files'] += 1
            if time.monotonic()-started >= budget:
                break
        self.read_cache_advice['maximum_call_seconds'] = max(
            self.read_cache_advice['maximum_call_seconds'], time.monotonic()-started)
        if self.guard.samples % 5 == 0:
            write_json(self.run/'qualified-read-cache-advice.json', self.read_cache_advice)

    def flow_record(self, kind, **extra):
        row = {'utc': now(), 'kind': kind, 'resources': self.guard.last,
               'input_advice': dict(self.input_cache_advice),
               'qualified_read_advice': dict(self.read_cache_advice), **extra}
        with (self.run/'flow-control.jsonl').open('a', encoding='utf-8') as stream:
            stream.write(json.dumps(row)+'\n'); stream.flush(); os.fsync(stream.fileno())

    def maybe_flow_control(self, process, live_guard):
        if not self.config.get('flow_control') or not self.immutable_input_roots:
            return
        current = self.guard.last['memory_current']
        if current < self.flow_trigger and not (current >= self.flow_resume
                and self.input_cache_advice['unadvised_files'] >= 8192):
            return
        identity = getattr(process, 'jw_identity', None)
        rows = owned_group_members(identity)
        if not any(row['state'] != 'Z' for row in rows):
            return
        require(self.flow_summary['total_pause_seconds'] < self.flow_aggregate_timeout,
                'Flow-control aggregate pause budget exhausted')
        require(self.flow_summary['pauses'] < self.flow_summary['maximum_pauses'],
                'Flow-control pause count budget exhausted')
        started = time.monotonic()
        self.flow_summary['pauses'] += 1
        self.flow_record('pause-requested', identity=identity, members=rows,
                         trigger_bytes=self.flow_trigger, resume_bytes=self.flow_resume)
        stopped = False
        epoch = None
        try:
            # Set conservatively before the syscall: Python can deliver an
            # interrupt after SIGSTOP succeeds but before its call returns.
            stopped = True
            try:
                os.killpg(process.pid, signal.SIGSTOP)
            except ProcessLookupError:
                require(process.poll() is not None, 'Owned group disappeared while leader remains live')
                self.flow_record('stage-completed-before-pause')
                return
            stop_deadline = time.monotonic()+5.0
            while True:
                live_guard()
                rows = owned_group_members(identity)
                if all(row['state'] in ('T', 't', 'Z') for row in rows):
                    break
                require(time.monotonic() < stop_deadline, 'Owned stage did not become quiescent within 5 seconds')
                time.sleep(0.02)
            self.flow_record('paused', identity=identity, members=rows)
            if self.mapping_iterator is not None:
                self.mapping_iterator.close()
                self.mapping_iterator = None
            self.last_mapping_scan = 0.0
            self.restart_read_advice_round()
            snapshot = quiescent_group_snapshot(identity)
            if not snapshot:
                require(process.poll() is not None, 'Paused owned group vanished while stage remains live')
                stopped = False
                self.flow_record('stage-completed-without-resume')
                return
            def epoch_checkpoint():
                live_guard()
                elapsed = time.monotonic()-started
                require(elapsed < self.flow_pause_timeout, 'Flow-control per-pause timeout')
                require(self.flow_summary['total_pause_seconds']+elapsed < self.flow_aggregate_timeout,
                        'Flow-control aggregate pause timeout')
            def final_snapshot():
                current_snapshot = quiescent_group_snapshot(identity)
                if not current_snapshot and process.poll() is not None:
                    raise PausedStageCompleted()
                require(current_snapshot == snapshot,
                        'Paused epoch membership/thread/signal custody changed before resume')
            epoch = PausedInputEpoch(self, identity, snapshot, epoch_checkpoint, process)
            reclaim_requested_early = False
            try:
                # Request delegated reclaim before the potentially long per-member
                # cache-advice epoch. Reclaim retains the same pause/aggregate/service
                # deadline; one request per pause is preserved, with the fresh headroom
                # guard below deciding whether the process may resume.
                if self.guard.last['memory_current'] > self.flow_resume and self.delegated_reclaim:
                    self.delegated_reclaim.request(process, snapshot, self.flow_summary['pauses'],
                        epoch_checkpoint, min(started+self.flow_pause_timeout,
                            started+self.flow_aggregate_timeout-self.flow_summary['total_pause_seconds'],
                            self.guard.start+self.guard.timeout))
                    reclaim_requested_early = True
                    epoch_checkpoint()
                    final_snapshot()
                last_record = time.monotonic()
                while not epoch.step():
                    if time.monotonic()-last_record >= 5.0:
                        self.flow_record('paused-epoch-progress', phase=epoch.phase,
                            epoch=dict(epoch.stats), elapsed_seconds=time.monotonic()-started)
                        last_record = time.monotonic()
                stats = dict(epoch.stats)
                epoch.close()
                epoch = None
            finally:
                if epoch is not None:
                    epoch.close(restore=False)
            # Catalog cleanup/evidence is included in the pause budget and in
            # the fresh headroom measurement, before any resume decision.
            epoch_checkpoint()
            final_snapshot()
            self.flow_record('epoch-completed', epoch=stats,
                             elapsed_seconds=time.monotonic()-started)
            if (self.guard.last['memory_current'] > self.flow_resume and self.delegated_reclaim
                    and not reclaim_requested_early):
                self.delegated_reclaim.request(process, snapshot, self.flow_summary['pauses'],
                    epoch_checkpoint, min(started+self.flow_pause_timeout,
                        started+self.flow_aggregate_timeout-self.flow_summary['total_pause_seconds'],
                        self.guard.start+self.guard.timeout))
                epoch_checkpoint()
                final_snapshot()
            require(self.guard.last['memory_current'] <= self.flow_resume,
                    'Flow-control capacity: NO_HEADROOM after complete fresh paused epoch; '
                    f"current={self.guard.last['memory_current']} resume={self.flow_resume}")
            self.flow_record('resume-requested', identity=identity, epoch=stats,
                             elapsed_seconds=time.monotonic()-started)
            epoch_checkpoint()
            require(self.guard.last['memory_current'] <= self.flow_resume,
                    'Flow-control capacity: NO_HEADROOM immediately before resume')
            final_snapshot()
            os.killpg(process.pid, signal.SIGCONT)
            stopped = False
            self.flow_record('resumed', elapsed_seconds=time.monotonic()-started)
        except PausedStageCompleted:
            live_guard()
            if epoch is not None:
                # This is a successful stage boundary, so subsequent audit or
                # warmup stages must not inherit partial epoch bytearrays/Q.
                epoch.close()
                epoch = None
            live_guard()
            require(not any(row['state'] != 'Z' for row in owned_group_members(identity))
                    and process.poll() is not None, 'Paused completion lost exact stage custody')
            stopped = False
            self.flow_record('stage-completed-without-resume')
            return
        except BaseException as exc:
            if stopped:
                terminate_owned(process)
                stopped = False
            self.flow_record('terminated-during-pause', error=f'{type(exc).__name__}: {exc}',
                             members=owned_group_members(identity))
            raise
        finally:
            if stopped:
                terminate_owned(process)
            self.flow_summary['total_pause_seconds'] += time.monotonic()-started
            write_json(self.run/'flow-control-summary.json', self.flow_summary)

    def release_own_clean_cache(self, budget=0.4):
        """Bound installation/cache page residency without changing host guards."""
        if self.guard.last['memory_current'] < 3 * 2**29:
            return
        workspace = owned_path(self.config['workspace'])
        roots = [workspace/'cache', self.source/'.lake/build', workspace/'downloads']
        if self.config.get('dependency_source_root'):
            root = owned_path(self.config['dependency_source_root'])
            require(root.is_relative_to(workspace), 'Shared dependencies escape campaign')
            roots.extend(path/'.lake/build' for path in root.iterdir() if path.is_dir())
        else:
            roots.extend(path/'.lake/build' for path in (self.source/'.lake/packages').glob('*') if path.is_dir())
        if self.config.get('toolchain_directory'):
            roots.append(owned_path(self.config['toolchain_directory']))
        # Resume the traversal on the next sample. Restarting a large source tree
        # at each time slice can starve later generated artifacts indefinitely.
        if self.cache_iterator is None:
            self.cache_iterator = (path for root in roots for path in root.rglob('*'))
        started = time.monotonic()
        while True:
            try:
                path = next(self.cache_iterator)
            except StopIteration:
                self.cache_iterator = None
                return
            try:
                if path.is_file() and not path.is_symlink():
                    stat = path.stat()
                    identity = (stat.st_size, stat.st_mtime_ns)
                    if (stat.st_uid == UID and time.time() - stat.st_mtime >= 1 and
                            self.cache_advised.get(str(path)) != identity):
                        require(path.resolve().is_relative_to(workspace), 'Cache advice path escapes campaign')
                        with path.open('rb') as stream:
                            os.fsync(stream.fileno())
                            os.posix_fadvise(stream.fileno(), 0, 0, os.POSIX_FADV_DONTNEED)
                        self.cache_advised[str(path)] = identity
                        # This memo only avoids redundant closed-file advice.
                        # Eviction makes a file eligible again; H/Q custody and
                        # paused-epoch receipts live in separate structures.
                        if len(self.cache_advised) > CACHE_ADVICE_MEMO_LIMIT:
                            self.cache_advised.popitem(last=False)
                            self.cache_advice['memo_evictions'] += 1
                        self.cache_advice['maximum_memo_entries'] = max(
                            self.cache_advice['maximum_memo_entries'], len(self.cache_advised))
                        self.cache_advice['files'] += 1
                        self.cache_advice['bytes'] += stat.st_size
            except FileNotFoundError:
                pass
            if time.monotonic() - started >= budget:
                return

    def stage(self, name, command, cwd=None):
        self.guard.check()
        if self.delegated_reclaim:
            self.delegated_reclaim.sample('stage-start-'+name)
        require(re.fullmatch(r'[a-z0-9-]+', name), 'Unsafe stage name')
        entry = {'command': command, 'cwd': str(cwd or self.run), 'started_utc': now(),
                 'exit_code': None, 'pre_stage_resources': self.guard.last}
        self.stages[name] = entry
        write_json(self.run/'stages.json', self.stages)
        stdout_path, stderr_path = self.run/'logs'/f'{name}.stdout.log', self.run/'logs'/f'{name}.stderr.log'
        print(json.dumps({'stage': name, 'state': 'starting', 'utc': now()}), flush=True)
        with stdout_path.open('xb') as stdout, stderr_path.open('xb') as stderr:
            process = subprocess.Popen(command, cwd=cwd or self.run, env=self.environment,
                stdin=subprocess.DEVNULL, stdout=stdout, stderr=stderr, start_new_session=True)
            entry['pid'] = process.pid
            self.active_pgid = process.pid
            try:
                identity = capture_stage_identity(process)
            except BaseException:
                terminate_owned(process)
                raise
            entry['process_group_identity'] = identity
            last_guard_started = time.monotonic()
            entry['maximum_live_guard_interval_seconds'] = 0.0
            entry['maximum_flow_decision_gap_seconds'] = 0.0
            entry['flow_decision_checks'] = 0
            last_flow_decision = None
            last_flow_pause_total = self.flow_summary['total_pause_seconds']
            def live_guard():
                nonlocal last_guard_started
                started = time.monotonic()
                entry['maximum_live_guard_interval_seconds'] = max(
                    entry['maximum_live_guard_interval_seconds'], started-last_guard_started)
                last_guard_started = started
                self.guard.check()
                if self.delegated_reclaim:
                    service_leaf(self.delegated_reclaim.unit, self.delegated_reclaim.custody)
                    validate_compiler_placement(self.guard.last.get('compiler_processes', []),
                                                self.delegated_reclaim.leaf)
                    require(leaf_resources(self.delegated_reclaim.leaf)['events'] ==
                            self.delegated_reclaim.baseline['events'], 'Delegated leaf memory event or reset')
            def normal_stage_guard():
                nonlocal last_flow_decision, last_flow_pause_total
                live_guard()
                if (not self.config.get('flow_control') or process.poll() is not None or
                        not (name in ('dependency-cache', 'build', 'audit', 'declaration-types') or
                             name.startswith('prepare-module-'))):
                    return
                decision = time.monotonic()
                paused = self.flow_summary['total_pause_seconds']
                if last_flow_decision is not None:
                    require(paused >= last_flow_pause_total, 'Flow pause accounting regressed')
                    gap = max(0.0, decision-last_flow_decision-(paused-last_flow_pause_total))
                    entry['maximum_flow_decision_gap_seconds'] = max(
                        entry['maximum_flow_decision_gap_seconds'], gap)
                entry['flow_decision_checks'] += 1
                last_flow_decision, last_flow_pause_total = decision, paused
                # Paused callbacks receive only the raw guard: no recursive
                # decisions. The next normal checkpoint excludes recorded pause
                # duration, while retaining all other live response overhead.
                self.maybe_flow_control(process, live_guard)
            write_json(self.run/'active-stage.json', {'stage': name, **entry})
            try:
                while process.poll() is None:
                    normal_stage_guard()
                    self.release_qualified_read_cache()
                    normal_stage_guard()
                    self.release_import_readahead()
                    normal_stage_guard()
                    self.release_own_clean_cache()
                    normal_stage_guard()
                    time.sleep(0.5)
                entry['exit_code'] = process.returncode
                if identity is not None:
                    require(not any(row['state'] != 'Z' for row in owned_group_members(identity)),
                            'Stage leader exited with live descendants')
                self.guard.check()
                if self.delegated_reclaim:
                    self.delegated_reclaim.sample('stage-end-'+name)
            except BaseException as exc:
                entry['stop_reason'] = str(exc)
                terminate_owned(process)
                entry['exit_code'] = process.returncode
                raise
            finally:
                entry['ended_utc'] = now()
                stdout.flush(); stderr.flush()
                entry['stdout_sha256'] = digest(stdout_path)
                entry['stderr_sha256'] = digest(stderr_path)
                combined = self.run/'logs'/f'{name}.log'
                with combined.open('xb') as target:
                    for path in (stdout_path, stderr_path):
                        with path.open('rb') as source:
                            shutil.copyfileobj(source, target)
                entry['log_sha256'] = digest(combined)
                write_json(self.run/'stages.json', self.stages)
                self.active_pgid = None
                if self.mapping_iterator is not None:
                    self.mapping_iterator.close()
                    self.mapping_iterator = None
        require(entry['exit_code'] == 0, f'Stage {name} failed: exit {entry["exit_code"]}')
        return entry

    def verify_source(self):
        manifest = json.loads((self.run/'source-manifest.json').read_text())
        require(manifest['schema'] == 'jw-source-manifest-v1', 'Wrong source-manifest schema')
        seen = set()
        for item in manifest['files']:
            path = Path(item['path'])
            require(not path.is_absolute() and '..' not in path.parts and str(path) not in seen,
                    'Unsafe or duplicate source path')
            seen.add(str(path))
            require(digest(self.source/path) == item['sha256'], 'Captured source changed: ' + str(path))
        require((self.source/'lean-toolchain').read_text().strip() == TOOLCHAIN, 'Wrong toolchain pin')
        require(digest(self.source/self.config['audit_path']) == self.config['audit_source_sha256'],
                'Audit source binding changed')
        inventory = {p.relative_to(self.source).as_posix() for p in self.source.rglob('*.lean')
                     if '.lake' not in p.relative_to(self.source).parts}
        expected = {item['path'] for item in manifest['files'] if item['path'].endswith('.lean')}
        require(inventory == expected, 'Captured Lean source inventory changed')
        configured_cache = set(self.config.get('cache_modules', []))
        require(not configured_cache or 'Mathlib' in configured_cache or
                cache_module_scope(self.source) <= configured_cache,
                'Cache scope omits a captured source import (including bare Mathlib)')
        scope = json.loads((self.run/'audit-scope.json').read_text())
        original_names = [line.split()[-1] for line in
            (self.source/self.config['audit_path']).read_text().splitlines()
            if line.startswith('#print axioms ')]
        type_names = [line.removeprefix('#check @') for line in
            (self.run/'DeclarationTypes.lean').read_text().splitlines() if line.startswith('#check @')]
        names = scope['exports'] if scope['schema'] == 'jw-baseline-audit-scope-v1' else scope['declarations']
        require(names == original_names == type_names, 'Audit scope/type/export mismatch')
        return manifest

    def inventory(self, root, destination, mode='all'):
        self.stage('inventory-'+destination.stem, ['python3', str(Path(__file__).resolve()),
            '--inventory', mode, str(root), str(destination)])
        return digest(destination)

    def serialized_toolchain(self, actual):
        """Lake's documented override selects an overlay; real tools stay intact."""
        overlay = self.run/'serialized-toolchain'
        overlay.mkdir()
        binary = overlay/'bin'; binary.mkdir()
        for path in actual.iterdir():
            if path.name != 'bin':
                (overlay/path.name).symlink_to(path, target_is_directory=path.is_dir())
        for path in (actual/'bin').iterdir():
            if path.name == 'lake':
                shutil.copy2(path, binary/path.name)
                require(digest(binary/path.name) == digest(path), 'Overlay Lake bytes differ')
            elif path.name not in ('lean', 'leantar'):
                (binary/path.name).symlink_to(path)
        wrapper = ('#!/usr/bin/python3\nimport os,sys,fcntl\n'
            'if sys.argv[1:]==["--print-prefix"]:\n'
            ' print('+repr(str(overlay))+');sys.exit(0)\n'
            'queries={"--version","--help","--print-prefix","--print-libdir","--githash"}\n'
            'if not (len(sys.argv)==2 and sys.argv[1] in queries):\n'
            ' fd=os.open('+repr(str(self.run/'lean-process.lock'))+',os.O_RDWR|os.O_CREAT,0o600)\n'
            ' fcntl.flock(fd,fcntl.LOCK_EX)\n'
            ' os.set_inheritable(fd,True)\n'
            'os.execv('+repr(str(actual/'bin/lean'))+', ['+repr(str(actual/'bin/lean'))+']+sys.argv[1:])\n')
        (binary/'lean').write_text(wrapper)
        (binary/'lean').chmod(0o700)
        leantar_wrapper = ('#!/usr/bin/python3\nimport os,sys,json,datetime\n'
            'argv=['+repr(str(actual/'bin/leantar'))+',"--jobs","1"]+sys.argv[1:]\n'
            'with open('+repr(str(self.run/'leantar-adapter-invocations.jsonl'))+',"a") as stream:\n'
            ' stream.write(json.dumps({"utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),'
            '"pid":os.getpid(),"forwarded_argv":argv})+"\\n");stream.flush();os.fsync(stream.fileno())\n'
            'if "-x" in sys.argv[1:]:\n'
            ' os.execv("/usr/bin/python3",["python3",'+repr(str(Path(__file__).resolve()))+
            ',"--bounded-decompress",'+repr(str(self.run/'admission.json'))+','+
            repr(str(actual/'bin/leantar'))+']+sys.argv[1:])\n'
            'os.execv('+repr(str(actual/'bin/leantar'))+', ['+repr(str(actual/'bin/leantar'))+
            ',"--jobs","1"]+sys.argv[1:])\n')
        if (actual/'bin/leantar').is_file():
            (binary/'leantar').write_text(leantar_wrapper)
            (binary/'leantar').chmod(0o700)
        self.environment.update(LEAN_SYSROOT=str(overlay), LAKE_OVERRIDE_LEAN='true',
            PATH=str(binary)+os.pathsep+self.environment.get('PATH',''))
        write_json(self.run/'compiler-serialization.json', {'method': 'Lake LAKE_OVERRIDE_LEAN and LEAN_SYSROOT; compiler-only flock; query-only invocations exempt',
            'wrapper_sha256': digest(binary/'lean'), 'real_lean_sha256': digest(actual/'bin/lean'),
            'toolchain_bytes_modified': False, 'reported_wrapper_sysroot': str(overlay),
            'requested_leantar_jobs': 1, 'leantar_wrapper_sha256': digest(binary/'leantar') if (binary/'leantar').exists() else None,
            'decompression_batch_records': 16, 'batch_policy': 'native pinned protocol; drain completed artifacts and input caches between batches; require 1 GiB memory headroom',
            'lake_overlay_kind': 'byte-identical executable copy; verified original libraries via symlink',
            'lake_overlay_sha256': digest(binary/'lake') if (binary/'lake').exists() else None,
            'lock': str(self.run/'lean-process.lock')})

    def execute(self):
        cfg = self.config
        workspace = owned_path(cfg['workspace'])
        self.source.mkdir()
        with tarfile.open(self.run/'source.tar.gz', 'r:gz') as archive:
            for member in archive.getmembers():
                p = Path(member.name)
                require(not p.is_absolute() and '..' not in p.parts and not member.issym()
                        and not member.islnk() and (member.isfile() or member.isdir()), 'Unsafe archive member')
            archive.extractall(self.source, filter='data')
        self.verify_source()
        if cfg.get('project_artifact_source_run'):
            previous_run = owned_path(cfg['project_artifact_source_run'])
            require(previous_run.parent == workspace/'runs', 'Project artifact source escapes campaign runs')
            require(digest(previous_run/'terminal-receipt.json') == cfg['project_terminal_receipt_sha256'],
                    'Project artifact receipt changed')
            previous_receipt = json.loads((previous_run/'terminal-receipt.json').read_text())
            require(digest(previous_run/'admission.json') == previous_receipt['admission_sha256'],
                    'Prior artifact admission changed')
            previous_admission = json.loads((previous_run/'admission.json').read_text())
            previous_manifest_sha = digest(previous_run/'source-manifest.json')
            require(previous_manifest_sha == previous_receipt['source_manifest_sha256'], 'Prior source manifest changed')
            relation = cfg.get('project_artifact_source_relation', 'identical')
            require(relation in ('identical', 'strict-extension'), 'Unknown project artifact source relation')
            if relation == 'identical':
                require(previous_manifest_sha == cfg['source_manifest_sha256'],
                        'Project artifacts do not match captured source identity')
            else:
                previous_files = {item['path']: item['sha256'] for item in
                    json.loads((previous_run/'source-manifest.json').read_text())['files']}
                current_files = {item['path']: item['sha256'] for item in
                    json.loads((self.run/'source-manifest.json').read_text())['files']}
                require(previous_files.items() <= current_files.items(),
                        'Project source extension changed or removed an original file')
            reuse_scope = artifact_reuse_scope(previous_receipt, previous_admission, cfg)
            for item in json.loads((previous_run/'source-manifest.json').read_text())['files']:
                require(digest(previous_run/'source'/item['path']) == item['sha256'],
                        'Prior project source bytes changed after compilation')
            previous_build = owned_path(previous_run/'source/.lake/build')
            require(previous_build.is_dir(), 'Prior project build directory absent')
            (self.source/'.lake').mkdir()
            inventory_sha = self.inventory(previous_build, self.run/'project-artifact-reuse-inventory.json')
            copied = [0]
            def copy_artifact(source, destination):
                require(Path(source).resolve().is_relative_to(previous_build), 'Project artifact link escapes prior build')
                result = shutil.copy2(source, destination)
                with Path(destination).open('rb') as stream:
                    os.fsync(stream.fileno())
                    os.posix_fadvise(stream.fileno(), 0, 0, os.POSIX_FADV_DONTNEED)
                copied[0] += 1
                if copied[0] % 25 == 0:
                    self.guard.check()
                return result
            shutil.copytree(previous_build, self.source/'.lake/build', copy_function=copy_artifact)
            for item in json.loads((self.run/'project-artifact-reuse-inventory.json').read_text())['files']:
                require(digest(self.source/'.lake/build'/item['path']) == item['sha256'], 'Project artifact clone changed')
            write_json(self.run/'project-artifact-reuse.json', {'previous_run': str(previous_run),
                'previous_terminal_sha256': cfg['project_terminal_receipt_sha256'],
                'source_relation': relation, 'previous_source_manifest_sha256': previous_manifest_sha,
                'current_source_manifest_sha256': cfg['source_manifest_sha256'],
                'project_artifact_inventory_sha256': inventory_sha,
                'prior_success_scope': reuse_scope,
                'validation': 'Receipt-bound artifact clone with matching original source files; current Lake build/audit exits still required'})
        self.stage('owned-cache-drain', ['python3', str(Path(__file__).resolve()),
            '--drain-owned-artifacts', str(self.run/'admission.json')])
        downloads = workspace/'downloads'; downloads.mkdir(exist_ok=True)
        archive = downloads/TOOLCHAIN_ARCHIVE
        if not archive.exists():
            self.stage('download-toolchain', ['curl', '--fail', '--location', '--retry', '2',
                '--connect-timeout', '30', '--output', str(archive), TOOLCHAIN_URL])
        require(digest(archive) == TOOLCHAIN_SHA256, 'Official toolchain archive digest mismatch')
        tools = owned_path(cfg['toolchain_directory']); tools.mkdir(exist_ok=True)
        require(tools.parent == workspace, 'Toolchain directory must be campaign-owned')
        binpath = tools/'lean-4.33.0-rc1-linux/bin'
        if cfg.get('toolchain_inventory_path'):
            previous = owned_path(cfg['toolchain_inventory_path'])
            require(digest(previous) == cfg['toolchain_inventory_sha256'], 'Qualified toolchain inventory changed')
            previous_files = json.loads(previous.read_text())['files']
            require({item['path'] for item in previous_files} ==
                    {path.relative_to(binpath.parent).as_posix() for path in binpath.parent.rglob('*')
                     if path.is_file() and not path.is_symlink()}, 'Qualified toolchain file inventory changed')
            for i, item in enumerate(previous_files):
                require(digest(tools/'lean-4.33.0-rc1-linux'/item['path']) == item['sha256'],
                        'Qualified toolchain file changed: ' + item['path'])
                if i % 25 == 0:
                    self.guard.check()
        else:
            require(not binpath.exists(), 'New replay requires a fresh, fully verified extraction directory')
            self.stage('extract-toolchain', ['python3', str(Path(__file__).resolve()),
                '--extract-toolchain', str(archive), str(tools)])
        require((binpath/'lean').is_file() and (binpath/'lake').is_file(), 'Incomplete toolchain')
        pins_path = tools/'toolchain-executable-pins.json'
        pins = {name: digest(binpath/name) for name in ('lean', 'lake')}
        if pins_path.exists():
            require(json.loads(pins_path.read_text()) == pins, 'Retained toolchain executable changed')
        else:
            require('extract-toolchain' in self.stages, 'Unqualified existing toolchain')
            write_json(pins_path, pins)
        self.environment['PATH'] = str(binpath) + os.pathsep + self.environment.get('PATH', '')
        if cfg.get('toolchain_inventory_path'):
            shutil.copyfile(previous, self.run/'toolchain-file-inventory.json')
            toolchain_inventory_sha = digest(self.run/'toolchain-file-inventory.json')
            require(toolchain_inventory_sha == cfg['toolchain_inventory_sha256'], 'Inventory copy changed')
        else:
            toolchain_inventory_sha = self.inventory(tools/'lean-4.33.0-rc1-linux',
                self.run/'toolchain-file-inventory.json')
        write_json(self.run/'toolchain-provenance.json', {'origin': TOOLCHAIN_URL,
            'publisher_archive_sha256': TOOLCHAIN_SHA256, 'archive_sha256': digest(archive),
            'executables': pins, 'file_inventory_sha256': toolchain_inventory_sha})
        self.stage('lean-version', ['lean', '--version'])
        self.stage('lake-version', ['lake', '--version'])
        require('4.33.0-rc1' in (self.run/'logs/lean-version.stdout.log').read_text(), 'Compiler version mismatch')
        self.serialized_toolchain(binpath.parent)
        packages = json.loads((self.source/'lake-manifest.json').read_text())['packages']
        pkgroot = self.source/'.lake/packages'; pkgroot.mkdir(parents=True)
        provenance = []
        for package in packages:
            name, revision, url = package['name'], package['rev'], package['url']
            require(re.fullmatch('[A-Za-z0-9_-]+', name) and re.fullmatch('[a-f0-9]{40}', revision), 'Invalid package pin')
            require(url.startswith('https://github.com/leanprover-community/') or
                    url.startswith('https://github.com/leanprover/'), 'Unexpected package origin')
            if cfg.get('dependency_source_root'):
                directory = owned_path(cfg['dependency_source_root'])/name
                require(directory.is_dir(), 'Qualified dependency directory absent')
                origin = subprocess.check_output(['git','remote','get-url','origin'],cwd=directory,text=True).strip()
                require(origin == url, 'Dependency origin changed')
                changes = subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=directory,text=True)
                require(not changes.strip(), 'Dependency tracked source changed')
                (pkgroot/name).symlink_to(directory, target_is_directory=True)
            else:
                directory = pkgroot/name; directory.mkdir()
                self.stage('git-init-'+name.lower(), ['git', 'init', '-q'], directory)
                self.stage('git-origin-'+name.lower(), ['git', 'remote', 'add', 'origin', url], directory)
                self.stage('git-fetch-'+name.lower(), ['git', 'fetch', '--depth=1', 'origin', revision], directory)
                self.stage('git-checkout-'+name.lower(), ['git', '-c', 'advice.detachedHead=false', 'checkout', '--detach', revision], directory)
            self.stage('git-head-'+name.lower(), ['git', 'rev-parse', 'HEAD'], directory)
            actual = (self.run/'logs'/f'git-head-{name.lower()}.stdout.log').read_text().strip()
            require(actual == revision, 'Dependency checkout differs from pinned revision')
            provenance.append({'name': name, 'url': url, 'revision': actual,
                'origin': 'verified-prior-public-pinned' if cfg.get('dependency_source_root') else 'fresh-public-pinned', 'tree': subprocess.check_output(
                    ['git', 'rev-parse', 'HEAD^{tree}'], cwd=directory, text=True).strip()})
        write_json(self.run/'dependency-provenance.json', provenance)
        overlay = self.run/'serialized-toolchain'
        probe = ('import json,pathlib,shutil,subprocess; '
            'root=pathlib.Path('+repr(str(overlay))+'); '
            'assert pathlib.Path(shutil.which("lean"))==root/"bin/lean"; '
            'assert pathlib.Path(shutil.which("leantar"))==root/"bin/leantar"; '
            'prefix=subprocess.check_output(["lean","--print-prefix"],text=True).strip(); '
            'assert prefix==str(root); '
            'r=subprocess.run(["leantar","--help"],text=True,capture_output=True); '
            'assert r.returncode==0; '
            'print(json.dumps({"status":"PASS","lean_lookup":shutil.which("lean"),'
            '"leantar_lookup":shutil.which("leantar"),"prefix":prefix,"leantar_help_exit":r.returncode}))')
        self.stage('adapter-integration', ['lake', 'env', 'python3', '-c', probe], self.source)
        external_probe = self.run/'ExternalPathProbe.lean'
        external_probe.write_text('#check Nat\n', encoding='utf-8')
        write_json(self.run/'external-path-probe-input.json', {'path': str(external_probe),
            'sha256': digest(external_probe), 'scope': 'Path/CLI probe only; no new declaration or proof'})
        self.stage('external-path-preflight', ['lake', 'env', 'lean', '--root', str(self.run),
            str(external_probe)], self.source)
        self.stage('pre-cache-closed-cache-drain', ['python3', str(Path(__file__).resolve()),
            '--drain-owned-artifacts', str(self.run/'admission.json'), 'pre-cache'])
        cache_modules = cfg.get('cache_modules', [])
        require(isinstance(cache_modules, list) and all(isinstance(module, str) and
            re.fullmatch(r'Mathlib(?:\.[A-Za-z0-9_]+)*', module) for module in cache_modules),
            'Unsafe cache module scope')
        inventory_root = owned_path(cfg['dependency_source_root']) if cfg.get('dependency_source_root') else pkgroot
        source_inventory = self.run/'dependency-source-inventory.json'
        source_inventory_sha = self.inventory(inventory_root, source_inventory,
            'dependency-source')
        # Pin dependency source inputs before cache preparation so its Lake
        # process can use the same bounded pause/advice path as the project
        # build. The package tree is detached at the captured manifest commits;
        # advice only drops file cache and never changes their bytes.
        self.qualified_read_inventories = [(inventory_root, source_inventory)]
        self.immutable_input_roots = [(tools/'lean-4.33.0-rc1-linux').resolve(),
                                      inventory_root.resolve()]
        self.stage('dependency-cache', ['lake', 'exe', 'cache', 'get', *cache_modules], self.source)
        source_after_cache = self.run/'dependency-source-after-cache-inventory.json'
        source_after_cache_sha = self.inventory(inventory_root, source_after_cache,
            'dependency-source')
        require(source_after_cache_sha == source_inventory_sha,
                'Pinned dependency source changed during cache preparation')
        self.inventory(inventory_root, self.run/'dependency-compiled-inventory.json',
            'compiled')
        self.qualified_read_inventories = [(inventory_root, source_inventory),
            (inventory_root, self.run/'dependency-compiled-inventory.json')]
        if cfg.get('qualified_metadata'):
            metadata = cfg['qualified_metadata']
            require(owned_path(metadata['root']) == inventory_root.resolve(),
                    'Metadata custody has a different dependency root')
            self.stage('qualify-metadata', ['python3', str(Path(__file__).resolve()),
                '--qualify-metadata', str(self.run/'admission.json'),
                str(self.run/'metadata-qualification.json')])
            self.qualified_metadata = (inventory_root.resolve(), owned_path(metadata['manifest']))
        self.verify_source()
        targets = cfg.get('build_targets', [])
        require(isinstance(targets, list) and all(isinstance(target, str) and
            re.fullmatch(r'[A-Za-z][A-Za-z0-9_.]*', target) for target in targets),
            'Unsafe build target')
        diagnostic_only = cfg.get('purpose') in ('module-feedback', 'isolated-module-diagnostic')
        require(not diagnostic_only or targets, 'Module feedback/diagnostic requires explicit targets')
        self.cache_iterator = None
        self.cache_advised.clear()
        gc.collect()
        self.stage('pre-build-closed-cache-drain', ['python3', str(Path(__file__).resolve()),
            '--drain-owned-artifacts', str(self.run/'admission.json'), 'pre-build'])
        self.guard.check()
        write_json(self.run/'immediate-pre-build-resources.json', self.guard.last)
        sequential = cfg.get('sequential_project_targets')
        if sequential is not None:
            require(not diagnostic_only and not targets, 'Sequential warmup only precedes the exact full default build')
            require(sequential == project_build_order(self.source), 'Sequential plan differs from captured root import closure')
            write_json(self.run/'sequential-project-plan.json', {'targets': sequential,
                'scope': 'One new project module per invocation, then exact default build; no source change'})
            for index, target in enumerate(sequential):
                stage = f'prepare-module-{index:03d}'
                self.stage(stage, ['lake', 'build', target], self.source)
                self.drain_recent_inputs(stage)
        self.stage('build', ['lake', 'build', *targets], self.source)
        options = ['-D', 'maxSynthPendingDepth=3', '-D', 'weak.linter.mathlibStandardSet=true',
                   '-D', 'relaxedAutoImplicit=false', '-D', 'pp.unicode.fun=true']
        if not diagnostic_only:
            self.stage('audit', ['lake', 'env', 'lean', *options, cfg['audit_path']], self.source)
            if cfg['audit_path'] == 'ExoticCCR/PublicationAxiomAudit.lean':
                self.stage('audit-profile', ['python3', 'scripts/check_publication_axioms.py',
                           str(self.run/'logs/audit.log')], self.source)
            self.stage('declaration-types', ['lake', 'env', 'lean', *options,
                       '--root', str(self.run), str(self.run/'DeclarationTypes.lean')], self.source)
        self.verify_source()
        for package in provenance:
            directory = pkgroot/package['name']
            actual = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=directory, text=True).strip()
            changes = subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no'], cwd=directory, text=True)
            require(actual == package['revision'] and not changes.strip(), 'Dependency source changed after cache/build')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('admission')
    parser.add_argument('admission_sha256')
    args = parser.parse_args()
    require(sys.platform == 'linux' and os.getuid() == UID, 'Run only as the designated Linux worker')
    admission = owned_path(args.admission)
    require(digest(admission) == args.admission_sha256, 'Admission hash mismatch')
    cfg = json.loads(admission.read_text())
    require(cfg['schema'] == 'jw-admission-v1', 'Wrong admission schema')
    expected_host = admission_host(cfg)
    require(cfg['compiler_owner'] == 'jacobian-weyl-completion-20261110/compiler-admission', 'Wrong compiler custody')
    require(digest(__file__) == cfg['runner_sha256'], 'Runner hash mismatch')
    workspace, run = owned_path(cfg['workspace']), owned_path(cfg['run'])
    require(run.parent == workspace/'runs' and workspace.stat().st_uid == UID and run.stat().st_uid == UID,
            'Wrong workspace/run ownership or layout')
    for filename, field in [('source.tar.gz', 'source_archive_sha256'),
            ('source-manifest.json', 'source_manifest_sha256'), ('audit-scope.json', 'audit_scope_sha256'),
            ('DeclarationTypes.lean', 'type_capture_sha256')]:
        require(digest(run/filename) == cfg[field], 'Input changed: ' + filename)
    require(not (run/'attempt.json').exists(), 'Run already attempted; observe and collect it')
    initial = observe(); minimum_free = validate_preflight(cfg, initial)
    result = {'schema': 'jw-compiler-result-v1', 'status': 'running', 'started_utc': now(),
        'purpose': cfg.get('purpose', 'frozen-baseline-replay'),
        'source_identity_kind': cfg.get('source_identity_kind', 'exact-git-archive'),
        'candidate_overlay_hashes': cfg.get('candidate_overlay_hashes', {}),
        'build_targets': cfg.get('build_targets', []),
        'diagnostic_scope': cfg.get('diagnostic_scope'),
        'host': expected_host, 'uid': UID, 'pid': os.getpid(), 'source_commit': cfg['source_commit'],
        'boot_id': initial['boot_id'], 'parent_event_baseline': initial['events'],
        'parent_event_profile': admitted_event_profile(expected_host, initial['boot_id'])[1],
        'root_free_threshold_bytes': minimum_free,
        'source_manifest_sha256': cfg['source_manifest_sha256'],
        'audit_scope_sha256': cfg['audit_scope_sha256'], 'audit_source_sha256': cfg['audit_source_sha256'],
        'admission_sha256': args.admission_sha256, 'runner_sha256': cfg['runner_sha256']}
    def stop(signum, _frame):
        raise RuntimeError('Runner received signal ' + str(signum))
    for signum in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):
        signal.signal(signum, stop)
    with lease(ROOT/'locks/host-compiler.lock'):
        require(not compiler_processes(), 'Competing compiler process exists')
        result['lease'] = {'path': str(ROOT/'locks/host-compiler.lock'),
                          'inode': (ROOT/'locks/host-compiler.lock').stat().st_ino,
                          'acquired_utc': now(), 'exclusive': True}
        write_json(run/'attempt.json', result)
        guard = None
        replay = None
        try:
            guard = Guard(run, minimum_free=minimum_free, expected_host=expected_host,
                          expected_boot_id=initial['boot_id'], expected_events=initial['events'])
            replay = Replay(cfg, run, guard)
            replay.execute()
            guard.check()
            result['status'] = 'completed'
            result['exit_code'] = 0
        except BaseException as exc:
            result['status'] = 'failed'
            result['error'] = f'{type(exc).__name__}: {exc}'
            result['exit_code'] = 1
            print(result['error'], file=sys.stderr, flush=True)
        finally:
            result['ended_utc'] = now()
            result['stages'] = replay.stages if replay else {}
            result['resources'] = guard.summary() if guard else {'initial': initial}
            result['own_file_cache_advice'] = replay.cache_advice if replay else None
            result['immutable_input_cache_advice'] = replay.input_cache_advice if replay else None
            result['qualified_read_cache_advice'] = replay.read_cache_advice if replay else None
            result['qualified_metadata'] = cfg.get('qualified_metadata')
            result['flow_control'] = replay.flow_summary if replay else None
            result['delegated_reclaim'] = (replay.delegated_reclaim.summary
                if replay and replay.delegated_reclaim else None)
            result['lease']['release_pending_on_return'] = True
            write_json(run/'terminal-receipt.json', result)
    return result['exit_code']


def extract_toolchain(archive, destination):
    """Stream verified public distribution and release only our clean file cache."""
    require(sys.platform == 'linux' and os.getuid() == UID, 'Designated Linux worker required')
    archive, destination = owned_path(archive), owned_path(destination)
    require(digest(archive) == TOOLCHAIN_SHA256, 'Toolchain archive digest mismatch')
    require(destination.parent.name == 'jacobian-weyl-20261110', 'Wrong extraction destination')
    require(not (destination/'lean-4.33.0-rc1-linux').exists(), 'Extraction output already exists')
    child = subprocess.Popen(['zstd', '-dc', str(archive)], stdout=subprocess.PIPE)
    try:
        with tarfile.open(fileobj=child.stdout, mode='r|') as tar:
            for item in tar:
                path = Path(item.name)
                require(not path.is_absolute() and '..' not in path.parts,
                        'Unsafe toolchain archive path')
                target = destination/path
                require(target.resolve().is_relative_to(destination), 'Toolchain member escapes destination')
                if item.isdir():
                    target.mkdir(parents=True, exist_ok=True)
                elif item.isfile():
                    target.parent.mkdir(parents=True, exist_ok=True)
                    with tar.extractfile(item) as source, target.open('xb') as output:
                        shutil.copyfileobj(source, output, length=1024*1024)
                        output.flush()
                        os.fsync(output.fileno())
                        os.posix_fadvise(output.fileno(), 0, 0, os.POSIX_FADV_DONTNEED)
                    target.chmod(item.mode & 0o777)
                elif item.issym():
                    require(not Path(item.linkname).is_absolute() and
                            (target.parent/item.linkname).resolve().is_relative_to(destination),
                            'Toolchain symlink escapes destination')
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.symlink_to(item.linkname)
                elif item.islnk():
                    link = destination/item.linkname
                    require(link.resolve().is_relative_to(destination), 'Toolchain hardlink escapes destination')
                    target.parent.mkdir(parents=True, exist_ok=True)
                    os.link(link, target)
                else:
                    raise RuntimeError('Unsupported toolchain archive member')
        require(child.wait() == 0, 'Toolchain decompressor failed')
    finally:
        if child.poll() is None:
            child.terminate(); child.wait(timeout=15)
        child.stdout.close()


if __name__ == '__main__':
    if len(sys.argv) in (4, 6) and sys.argv[1] == '--delegated-reclaim':
        raise SystemExit(delegated_reclaim_child(*sys.argv[2:]))
    elif len(sys.argv) == 4 and sys.argv[1] == '--extract-toolchain':
        extract_toolchain(sys.argv[2], sys.argv[3])
    elif len(sys.argv) in (3,4) and sys.argv[1] == '--drain-owned-artifacts':
        config = json.loads(owned_path(sys.argv[2]).read_text())
        require(digest(__file__) == config['runner_sha256'], 'Artifact drain control hash changed')
        drain_owned_artifacts(config, sys.argv[3] if len(sys.argv)==4 else 'initial')
    elif len(sys.argv) >= 5 and sys.argv[1] == '--bounded-decompress':
        config = json.loads(owned_path(sys.argv[2]).read_text())
        require(digest(__file__) == config['runner_sha256'], 'Decompression control hash changed')
        bounded_decompress(sys.argv[3], config, sys.argv[4:])
    elif len(sys.argv) == 4 and sys.argv[1] == '--qualify-metadata':
        require(sys.platform == 'linux' and os.getuid() == UID, 'Designated Linux worker required')
        config = json.loads(owned_path(sys.argv[2]).read_text())
        require(digest(__file__) == config['runner_sha256'], 'Metadata qualification control hash changed')
        destination = owned_path(sys.argv[3])
        require(destination.parent == owned_path(config['run']), 'Metadata receipt escapes captured run')
        qualify_metadata(config['qualified_metadata'], destination)
    elif len(sys.argv) == 5 and sys.argv[1] == '--inventory':
        require(sys.platform == 'linux' and os.getuid() == UID, 'Designated Linux worker required')
        root, destination = owned_path(sys.argv[3]), owned_path(sys.argv[4])
        config = json.loads((destination.parent/'admission.json').read_text())
        require(digest(__file__) == config['runner_sha256'], 'Inventory control hash changed')
        require(destination.parent == owned_path(config['run']) and root.is_relative_to(owned_path(config['workspace'])),
                'Inventory input/output escapes campaign')
        print(json.dumps(write_inventory(root, destination, sys.argv[2])), flush=True)
    else:
        raise SystemExit(main())
