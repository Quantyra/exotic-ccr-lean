"""Native Linux regressions: admission failures and owned-process clean stop."""
import copy
import ctypes
import errno
import io
import gzip
import hashlib
import json
import mmap
import os
from pathlib import Path
import tempfile
import time
import subprocess
import struct
import shutil
import sys
from unittest.mock import patch

import jw_cpu_runner as runner


def fixture_reserve_check(evidence, phase, index, current, remaining, reserve, high, message, cycle=None):
    """Retain exact failed operands outside the disposable fixture directory."""
    if current + remaining + reserve < high:
        return
    record = {'schema': 'jw-native-fixture-reserve-failure-v1', 'phase': phase,
        'index': index, 'cycle': cycle, 'current_bytes': current,
        'remaining_bytes': remaining, 'reserve_bytes': reserve, 'high_bytes': high,
        'total_bytes': current + remaining + reserve, 'predicate': 'current + remaining + reserve < high',
        'error': message}
    print(json.dumps(record, sort_keys=True), file=sys.stderr, flush=True)
    runner.write_json(evidence/'reserve-failure.json', record)
    raise AssertionError(message)


def root_free_threshold_fixture(current):
    floor = 500 * 2**20
    assert runner.DEFAULT_ROOT_FREE_THRESHOLD_BYTES == floor
    assert runner.root_free_threshold({}) == floor
    higher = floor + 123456789
    assert runner.root_free_threshold({'root_free_threshold_bytes': higher}) == higher
    for bad in (None, True, False, floor-1, 0, '524288000'):
        try: runner.root_free_threshold({'root_free_threshold_bytes': bad})
        except RuntimeError: pass
        else: raise AssertionError('Invalid/lowered root-free threshold accepted')

    sample = copy.deepcopy(current)
    sample['events'] = {name: 0 for name in runner.EVENTS}
    sample['root_available_bytes'] = floor
    assert runner.validate_preflight({}, sample) == floor
    sample['root_available_bytes'] = higher
    assert runner.validate_preflight({'root_free_threshold_bytes': higher}, sample) == higher
    sample['root_available_bytes'] = higher-1
    try: runner.validate_preflight({'root_free_threshold_bytes': higher}, sample)
    except RuntimeError as exc:
        assert 'Root reserve failed' in str(exc)
    else: raise AssertionError('Preflight ignored the configured root-free threshold')

    sample = copy.deepcopy(current)
    sample['events'] = {name: 0 for name in runner.EVENTS}
    sample['events']['high'] = 1
    assert runner.validate_preflight({}, sample) == runner.MIN_FREE

    with tempfile.TemporaryDirectory(prefix='root-free-guard-fixture-') as directory:
        baseline = copy.deepcopy(current); baseline['root_available_bytes'] = floor+1
        below = copy.deepcopy(current); below['root_available_bytes'] = floor-1
        samples = iter((baseline, below))
        guard = runner.Guard(Path(directory), minimum_free=floor, reader=lambda: next(samples))
        try: guard.check()
        except RuntimeError as exc:
            assert 'Root reserve failed' in str(exc)
        else: raise AssertionError('Continuous guard did not stop at the configured threshold')
        assert guard.minimum_free == floor and guard.minimum_available == floor-1
    return ['500MiB-campaign-default-and-hash-bound-higher-override',
            'preflight-and-continuous-guard-share-configured-reserve',
            'invalid-lowered-and-below-threshold-values-rejected']


def compiler_host_pool_fixture(current):
    for host in ('cpu-02', 'cpu-03', 'cpu-04', 'cpu-05', 'cpu-06'):
        config = {'host': host}
        assert runner.admission_host(config) == host
        sample = copy.deepcopy(current); sample['host'] = host
        sample['events'] = {name: 0 for name in runner.EVENTS}
        sample['root_available_bytes'] = runner.MIN_FREE
        assert runner.validate_preflight(config, sample) == runner.MIN_FREE
        sample['host'] = 'cpu-05' if host != 'cpu-05' else 'cpu-04'
        try: runner.validate_preflight(config, sample)
        except RuntimeError: pass
        else: raise AssertionError('Host admission accepted a mismatched hostname')
    for bad in ('cpu-01', 'cpu-07', None, True):
        try: runner.admission_host({'host': bad})
        except RuntimeError: pass
        else: raise AssertionError('Host outside the authorized CPU-02/03/04/05/06 pool accepted')
    return ['hash-bound-cpu02-cpu03-cpu04-cpu05-cpu06-host-allowlist',
            'observed-host-must-match-admission',
        'cpu01-cpu07-and-unknown-hosts-rejected-by-this-runner']


def wider_profile_config(config):
    return dict(config, reclaim_profile=runner.WIDER_REFILL_PROFILE,
        flow_control=True, flow_policy={'trigger_bytes': 4026531840,
        'resume_bytes': 3489660928, 'early_backlog_files': 8192,
        'per_pause_timeout_seconds': 180, 'aggregate_pause_timeout_seconds': 2400,
        'maximum_pauses': 32})


def deeper_profile_config(config):
    return dict(config, reclaim_profile=runner.DEEPER_REFILL_PROFILE,
        flow_control=True, flow_policy={'trigger_bytes': 4026531840,
        'resume_bytes': 3489660928, 'early_backlog_files': 8192,
        'per_pause_timeout_seconds': 180, 'aggregate_pause_timeout_seconds': 2400,
        'maximum_pauses': 32})


def deeper_profile_fixture():
    """Policy-only check; the EAGAIN example replays preserved native measurements."""
    profile = runner.DEEPER_REFILL_PROFILE
    config = deeper_profile_config({})
    assert runner.selected_reclaim_profile(config) == profile
    assert runner.selected_reclaim_profile(wider_profile_config({})) == runner.WIDER_REFILL_PROFILE
    cpu06_config = deeper_profile_config({'host': 'cpu-06'})
    cpu06_config['reclaim_profile'] = runner.CPU06_DEEPER_REFILL_PROFILE
    assert runner.selected_reclaim_profile(cpu06_config) == runner.CPU06_DEEPER_REFILL_PROFILE
    assert runner.deficit_reclaim_policy(before, 4096, runner.CPU06_DEEPER_REFILL_PROFILE) == \
        runner.deficit_reclaim_policy(before, 4096, profile)
    for invalid in (dict(cpu06_config, host='cpu-05'),
                    dict(deeper_profile_config({'host': 'cpu-05'}), reclaim_profile=runner.CPU06_DEEPER_REFILL_PROFILE)):
        try: runner.selected_reclaim_profile(invalid)
        except RuntimeError: pass
        else: raise AssertionError('Host-specific refill profile mismatch accepted')
    before = 4004335616
    policy = runner.deficit_reclaim_policy(before, 4096, profile)
    assert policy == {'parent_current': before, 'resume_bytes': 3355443200,
        'buffer_bytes': 33554432, 'page_size': 4096,
        'maximum_request_bytes': 838860800, 'request_bytes': 682446848}
    payload = b'682446848 swappiness=0\n'
    terminal = {'request_sha256': 'a'*64, 'policy': policy,
        'request': payload.decode().strip(), 'exit_code': 1, 'errno': 11,
        'error': 'Resource temporarily unavailable'}
    after = {'parent_current': 3332542464}
    assert runner.classify_reclaim_result(profile, policy, 1, terminal, 'a'*64,
        payload, after) == 'eagain-short-reclaim-target-met'
    # These preserved native observations are not a new reclaim execution.
    leaf_before, leaf_after = 703864832, 32206848
    assert leaf_before-leaf_after == 671657984
    assert before-3332542464 == 671793152
    assert 3332542464 < policy['resume_bytes']
    bads = [
        (profile, dict(terminal, errno=5), after),
        (profile, terminal, {'parent_current': policy['resume_bytes']+1}),
        (runner.WIDER_REFILL_PROFILE, terminal, after),
        (profile, dict(terminal, request_sha256='b'*64), after),
    ]
    for selected, receipt, measurement in bads:
        try:
            runner.classify_reclaim_result(selected, policy, 1, receipt, 'a'*64,
                payload, measurement)
        except RuntimeError:
            pass
        else:
            raise AssertionError('Unqualified EAGAIN or unmet target was accepted')
    written = dict(terminal, exit_code=0, errno=None, error=None,
        written_bytes=len(payload))
    assert runner.classify_reclaim_result(profile, policy, 0, written, 'a'*64,
        payload, {'parent_current': before}) == 'request-written'
    return ['deeper-profile-exact-flow-policy-and-800MiB-request-cap',
        'preserved-native-EAGAIN-accepted-only-after-fresh-target-check',
        'EAGAIN-with-target-miss-wrong-profile-errno-or-binding-rejected',
        'exact-successful-write-still-accepted',
        'cpu06-profile-bound-to-cpu06-host-and-rejects-cross-host-binding']


def wider_profile_fixture(workspace):
    """Pure policy/captured-admission tests; mocked self-cgroup is not host evidence."""
    wide = runner.WIDER_REFILL_PROFILE
    assert runner.selected_reclaim_profile({}) is None
    cfg = wider_profile_config({})
    assert runner.selected_reclaim_profile(cfg) == wide
    bad_configs = [dict(cfg, reclaim_profile=x) for x in (None, False, 1, '', '3.0GiB')]
    bad_configs += [dict(cfg, flow_control=False), dict(cfg, flow_policy={})]
    for key in cfg['flow_policy']:
        for value in (None, True, str(cfg['flow_policy'][key]), cfg['flow_policy'][key]+1):
            bad_configs.append(dict(cfg, flow_policy=dict(cfg['flow_policy'], **{key:value})))
    bad_configs.append(dict(cfg, flow_policy=dict(cfg['flow_policy'], aggregate_pause_timeout_seconds=600)))
    for bad in bad_configs:
        try: runner.selected_reclaim_profile(bad)
        except RuntimeError: pass
        else: raise AssertionError('Mixed/unselected wider profile accepted')
    page, resume, high = 4096, 3489660928, 4294967296
    assert runner.deficit_reclaim_policy(3989532672, page, wide)['request_bytes'] == 533426176
    assert runner.deficit_reclaim_policy(high-1, page, wide)['request_bytes'] == 838860800
    for current in (resume, resume-1, 0):
        assert runner.deficit_reclaim_policy(current, page, wide)['request_bytes'] == 0
    assert runner.deficit_reclaim_policy(resume+1, page, wide)['request_bytes'] == 33558528
    assert runner.deficit_reclaim_policy(3989532672, page)['request_bytes'] == 130772992
    for current,size,profile in ((True,page,wide),(-1,page,wide),(high,page,wide),
            (2**200,page,wide),(resume+1,0,wide),(resume+1,4097,wide),
            (resume+1,True,wide),(resume+1,page,'3.0GiB')):
        try: runner.deficit_reclaim_policy(current,size,profile)
        except RuntimeError: pass
        else: raise AssertionError('Invalid wider sizing accepted')
    with tempfile.TemporaryDirectory(prefix='wider-policy-fixture-',dir=workspace) as directory:
        root=Path(directory);run=root/'run';run.mkdir();admission=run/'admission.json'
        config=wider_profile_config({'workspace':str(root),'runner_sha256':'1'*64,
            'delegated_reclaim':{'unit':'jw-policy-fixture.service'}})
        runner.write_json(admission,config);expected=runner.digest(admission)
        cg='0::/user.slice/user-986.slice/user@986.service/app.slice/jw-policy-fixture.service'
        sample={'host':runner.HOST,'uid':runner.UID,'worker':'quantyra-worker','cgroup':cg,
            'root_available_bytes':runner.MIN_FREE,'root_available_inodes':runner.MIN_INODES,
            'root_read_only':False,'limits':dict(runner.LIMITS),'memory_current':3989532672,
            'events':{name:0 for name in runner.EVENTS},'filesystem_error_counters':{}}
        request={'run':str(run),'runner_sha256':'1'*64,'unit':'jw-policy-fixture.service',
            'reclaim_profile':wide,'admission_binding':{'path':str(admission),'sha256':expected},
            'parent_sample':sample,'parent_events':sample['events'],'filesystem_error_counters':{},
            'policy':runner.deficit_reclaim_policy(sample['memory_current'],page,wide)}
        native_read=Path.read_text
        def read(path,*args,**kwargs):
            return cg if path.as_posix()=='/proc/self/cgroup' else native_read(path,*args,**kwargs)
        with patch.object(runner,'ROOT',root.parent),patch.object(Path,'read_text',read), \
             patch.object(runner.os,'sysconf',create=True,return_value=page):
            parent_config=dict(config);parent_config.pop('delegated_reclaim')
            replay=runner.Replay(parent_config,run,object())
            assert replay.flow_resume==resume and replay.flow_trigger==4026531840
            assert replay.flow_aggregate_timeout==2400 and replay.flow_pause_timeout==180
            assert runner.deficit_reclaim_payload(request,wide,expected)==b'533426176 swappiness=0\n'
            bads=[]
            for key in request['policy']:
                bad=copy.deepcopy(request);bad['policy'][key]+=1;bads.append(bad)
            for missing in ('reclaim_profile','admission_binding'):
                bad=copy.deepcopy(request);del bad[missing];bads.append(bad)
            bad=copy.deepcopy(request);del bad['reclaim_profile'];del bad['admission_binding']
            bad['policy']=runner.deficit_reclaim_policy(sample['memory_current'],page);bads.append(bad)
            bad=copy.deepcopy(request);bad['admission_binding']['sha256']='2'*64;bads.append(bad)
            bad=copy.deepcopy(request);bad['unit']='jw-wrong.service';bads.append(bad)
            for bad in bads:
                try:runner.deficit_reclaim_payload(bad,wide,expected)
                except (RuntimeError,KeyError):pass
                else:raise AssertionError('Wider child profile downgrade/tamper accepted')
            for profile,hashed in ((None,None),(wide,'3'*64),('3.0GiB',expected)):
                try:runner.deficit_reclaim_payload(request,profile,hashed)
                except RuntimeError:pass
                else:raise AssertionError('Wrong independent child binding accepted')
            changed=dict(config,flow_policy=dict(config['flow_policy'],resume_bytes=3892314112))
            runner.write_json(admission,changed)
            try:runner.deficit_reclaim_payload(request,wide,expected)
            except RuntimeError:pass
            else:raise AssertionError('Changed admission accepted')
    return ['wider-profile-explicit-coherent-whitelist-default-preservation',
            'wider-profile-real-integer-cap-rounding-zero-invalid-overflow',
            'wider-child-independent-invocation-admission-and-payload-binding',
            'wider-child-omission-legacy-downgrade-and-admission-mutation-rejected']


def pause_allocation_policy_fixture(workspace):
    """Only two exact aggregate allocations; all other policy fields stay fixed."""
    policy = {'trigger_bytes': 4026531840, 'resume_bytes': 3892314112,
        'early_backlog_files': 8192, 'per_pause_timeout_seconds': 180.0,
        'aggregate_pause_timeout_seconds': 600.0, 'maximum_pauses': 32}
    with tempfile.TemporaryDirectory(prefix='pause-policy-fixture-', dir=workspace) as folder:
        root = Path(folder); serial = [0]
        def make(selected=False, value=None):
            serial[0] += 1; run = root/str(serial[0]); run.mkdir()
            config = {'workspace': str(root), 'flow_control': True}
            if selected:
                config['flow_policy'] = value
            return runner.Replay(config, run, object())
        assert make().flow_aggregate_timeout == 600
        for allocation in (600, 600.0, 2400, 2400.0):
            selected = dict(policy, aggregate_pause_timeout_seconds=allocation)
            replay = make(True, selected)
            assert replay.flow_aggregate_timeout == allocation
            assert replay.flow_summary['aggregate_pause_timeout_seconds'] == allocation
            assert replay.flow_pause_timeout == 180 and replay.flow_summary['maximum_pauses'] == 32
            assert replay.flow_trigger == 4026531840 and replay.flow_resume == 3892314112
            assert replay.config['flow_policy'] == selected  # No admission mutation.
        malformed = [None, [], '2400', {}, dict(policy, extra=1)]
        for allocation in (True, False, None, '2400', 0, -1, 601, 2399, 2401,
                           3600, 2400.01, float('nan'), float('inf'), 2**200):
            malformed.append(dict(policy, aggregate_pause_timeout_seconds=allocation))
        for key in policy:
            missing = dict(policy); del missing[key]; malformed.append(missing)
            bad = dict(policy); bad[key] = policy[key]+1; malformed.append(bad)
        for key in ('trigger_bytes', 'resume_bytes', 'early_backlog_files', 'maximum_pauses'):
            malformed.append(dict(policy, **{key: float(policy[key])}))
        malformed.append(dict(policy, per_pause_timeout_seconds='180'))
        for value in malformed:
            try:
                make(True, value)
            except RuntimeError:
                pass
            else:
                raise AssertionError('Malformed or mismatched captured policy accepted: '+repr(value))
    return ['pause-allocation-omitted-policy-keeps-legacy600',
            'pause-allocation-explicit600-and2400-preserve-all-other-controls-and-input',
            'pause-allocation-rejects-other-types-values-fields-and-control-mismatches']


def pause_allocation_deadline_fixture(workspace):
    """Real owned process pause/cleanup, synthetic elapsed time, no Lean/reclaim."""
    native_time = time.monotonic
    cases = ('legacy-exhausted', 'selected-allows-past600', 'selected-exhausted',
             'count32', 'legacy-during-pause', 'selected-during-pause',
             'per-pause180', 'outer14400', 'reclaim-per-pause-intersection',
             'reclaim-aggregate-intersection', 'reclaim-outer-intersection',
             'reclaim-insufficient-cleanup')
    passed = []
    for case in cases:
        with tempfile.TemporaryDirectory(prefix='pause-budget-fixture-', dir=workspace) as folder:
            root = Path(folder); run = root/'run'; run.mkdir()
            inputs = root/'inputs'; inputs.mkdir(); (inputs/'one.olean').write_bytes(b'input')
            guard = runner.Guard(run)
            assert guard.timeout == 14400
            policy = {'trigger_bytes': 4026531840, 'resume_bytes': 3892314112,
                'early_backlog_files': 8192, 'per_pause_timeout_seconds': 180.0,
                'aggregate_pause_timeout_seconds': 600 if case.startswith('legacy') else 2400,
                'maximum_pauses': 32}
            replay = runner.Replay({'workspace': str(root), 'flow_control': True,
                                    'flow_policy': policy}, run, guard)
            replay.immutable_input_roots = [inputs]
            replay.flow_trigger = 1  # Test-only trigger; actual raw host guard is unchanged.
            offsets = [0.0]; relieved = [False]; pause_start = [None]; deadlines = []
            expected_error = None
            if case == 'legacy-exhausted':
                replay.flow_summary['total_pause_seconds'] = 600
                expected_error = 'aggregate pause budget exhausted'
            elif case == 'selected-allows-past600':
                replay.flow_summary['total_pause_seconds'] = 600
            elif case == 'selected-exhausted':
                replay.flow_summary['total_pause_seconds'] = 2400
                expected_error = 'aggregate pause budget exhausted'
            elif case == 'count32':
                replay.flow_summary['pauses'] = 32
                expected_error = 'pause count budget exhausted'
            elif case in ('legacy-during-pause', 'selected-during-pause'):
                replay.flow_summary['total_pause_seconds'] = replay.flow_aggregate_timeout-.5
                expected_error = 'aggregate pause timeout'
            elif case == 'per-pause180':
                expected_error = 'per-pause timeout'
            elif case == 'outer14400':
                expected_error = 'Total run timeout'
            elif case == 'reclaim-aggregate-intersection':
                replay.flow_summary['total_pause_seconds'] = 2380
            elif case == 'reclaim-outer-intersection':
                guard.start = native_time()-guard.timeout+20
            elif case == 'reclaim-insufficient-cleanup':
                replay.flow_summary['total_pause_seconds'] = 2391
                expected_error = 'Insufficient remaining reclaim cleanup budget'
            original_record = replay.flow_record
            def record(kind, **extra):
                original_record(kind, **extra)
                if kind == 'pause-requested':
                    pause_start[0] = native_time()
                if kind == 'paused':
                    if case.endswith('during-pause'):
                        offsets[0] = 1.0
                    elif case == 'per-pause180':
                        offsets[0] = 181.0
                    elif case == 'outer14400':
                        guard.clock = lambda: guard.start+guard.timeout+1
            replay.flow_record = record
            def checkpoint():
                guard.check()  # Always real host observations before test injection.
                if case.startswith('reclaim-') and not relieved[0]:
                    guard.last = copy.deepcopy(guard.last)
                    guard.last['memory_current'] = replay.flow_resume+1
            if case.startswith('reclaim-'):
                class RequestProbe:
                    def request(self, process, snapshot, number, check, deadline):
                        check(); deadlines.append(deadline)
                        if case == 'reclaim-insufficient-cleanup':
                            probe = object.__new__(runner.DelegatedReclaim); probe.guard = guard
                            with patch.object(runner.subprocess, 'Popen', side_effect=AssertionError('No request child may start')):
                                probe.request(process, snapshot, number, check, deadline)
                            raise AssertionError('Insufficient cleanup budget was accepted')
                        assert deadline-native_time() > 10
                        relieved[0] = True
                replay.delegated_reclaim = RequestProbe()
            process = subprocess.Popen(['python3', '-c', 'import time; time.sleep(30)'], start_new_session=True)
            identity = runner.capture_stage_identity(process)
            replay.active_pgid = process.pid
            error = None
            try:
                with patch.object(runner.time, 'monotonic', side_effect=lambda: native_time()+offsets[0]):
                    try:
                        replay.maybe_flow_control(process, checkpoint)
                    except RuntimeError as exc:
                        error = str(exc)
                if expected_error:
                    assert error and expected_error in error, (case, error)
                else:
                    assert error is None, (case, error)
                    assert process.poll() is None and runner.process_identity(process.pid)['state'] not in ('T', 't')
                    assert replay.flow_summary['total_pause_seconds'] < replay.flow_aggregate_timeout
                if case.startswith('reclaim-'):
                    assert len(deadlines) == 1
                    if case == 'reclaim-outer-intersection':
                        expected = guard.start+guard.timeout
                    else:
                        remaining = 20 if case == 'reclaim-aggregate-intersection' else 9 if case == 'reclaim-insufficient-cleanup' else 180
                        expected = pause_start[0]+remaining
                    assert abs(deadlines[0]-expected) < .15, (case, deadlines[0], expected)
                if case == 'selected-allows-past600':
                    assert replay.flow_summary['total_pause_seconds'] > 600
                if case in ('per-pause180', 'outer14400', 'legacy-during-pause', 'selected-during-pause', 'reclaim-insufficient-cleanup'):
                    assert process.poll() is not None
                    assert not any(row['state'] != 'Z' for row in runner.owned_group_members(identity))
                print(json.dumps({'pause_allocation_case': case, 'error': error,
                    'selected_seconds': replay.flow_aggregate_timeout,
                    'total_pause_seconds': replay.flow_summary['total_pause_seconds'],
                    'request_calls': len(deadlines), 'synthetic_time_offset_seconds': offsets[0]}), flush=True)
                passed.append('pause-allocation-'+case)
            finally:
                if any(row['state'] != 'Z' for row in runner.owned_group_members(identity)):
                    runner.terminate_owned(process)
                assert not any(row['state'] != 'Z' for row in runner.owned_group_members(identity))
    return passed


def deficit_policy_fixture():
    page = os.sysconf('SC_PAGE_SIZE')
    resume, high = 3892314112, 4294967296
    assert runner.deficit_reclaim_policy(4053856256, page)['request_bytes'] == 195096576
    assert runner.deficit_reclaim_policy(high-1, page)['request_bytes'] == 436207616
    assert runner.deficit_reclaim_policy(resume, page)['request_bytes'] == 0
    assert runner.deficit_reclaim_policy(resume-1, page)['request_bytes'] == 0
    assert runner.deficit_reclaim_policy(resume+1, page)['request_bytes'] == 33554432+page
    for current, size in ((True, page), (-1, page), (high, page), (2**200, page),
                          (float(resume), page), (resume+1, 0), (resume+1, 4097),
                          (resume+1, 2**32), (resume+1, True)):
        try:
            runner.deficit_reclaim_policy(current, size)
        except RuntimeError:
            pass
        else:
            raise AssertionError('Invalid or overflow policy accepted')
    sample = runner.observe(); sample['memory_current'] = 4053856256
    request = {'parent_sample': sample, 'policy': runner.deficit_reclaim_policy(sample['memory_current'], page),
        'parent_events': sample['events'], 'filesystem_error_counters': sample['filesystem_error_counters']}
    assert runner.deficit_reclaim_payload(request) == b'195096576 swappiness=0\n'
    for field in request['policy']:
        bad = copy.deepcopy(request); bad['policy'][field] += 1
        try:
            runner.deficit_reclaim_payload(bad)
        except RuntimeError:
            pass
        else:
            raise AssertionError('Tampered policy field accepted: '+field)
    zero = copy.deepcopy(request); zero['parent_sample']['memory_current'] = resume
    zero['policy'] = runner.deficit_reclaim_policy(resume, page)
    try:
        runner.deficit_reclaim_payload(zero)
    except RuntimeError:
        pass
    else:
        raise AssertionError('Zero-byte helper request accepted')
    small = copy.deepcopy(request); small['parent_sample']['memory_current'] = resume+1
    small['policy'] = runner.deficit_reclaim_policy(resume+1, page)
    assert len(runner.deficit_reclaim_payload(small)) == 22  # Not a hard-coded23.
    return ['deficit-policy-pause4-upper-cap-page-rounding-and-zero',
            'deficit-policy-rejects-invalid-types-overflow-and-pages',
            'deficit-child-recomputes-all-bound-fields-and-variable-payload-length']


def injected_deficit_checkpoint(guard, checkpoint, actual_samples, first, sizing_sample=4053856256):
    """Fixture input only: real host guard first, never allocate to force pressure."""
    checkpoint()
    if first[0]:
        first[0] = False
        actual = runner.observe(); runner.validate_observation(actual)
        assert actual['events'] == guard.baseline['events']
        actual_samples.append(actual)
        guard.last = copy.deepcopy(guard.last)
        guard.last['memory_current'] = sizing_sample  # Explicit labelled fixture policy input only.


def delegated_reclaim_fixture(workspace, wider=False, interface_sizing=False):
    """Native own-leaf placement, two real requests, then bounded fault injection."""
    assert not interface_sizing or wider, 'Interface mode requires the captured wider profile'
    unit = os.environ['JW_TEST_SERVICE_UNIT']
    leaf, _, custody = runner.service_leaf(unit)
    passed, metrics = [], []
    evidence = Path(__file__).parent/('wider-interface-fixture-evidence' if interface_sizing else
        'wider-refill-fixture-evidence' if wider else 'delegated-reclaim-fixture-evidence')
    evidence.mkdir(exist_ok=True)
    def preserve(run, label):
        destination = evidence/label; destination.mkdir(exist_ok=True)
        for path in run.iterdir():
            if path.is_file() and path.suffix in ('.json', '.jsonl', '.txt'):
                shutil.copyfile(path, destination/path.name)
    for bad in ('wrong.service', '../user-986.slice', unit.replace('jw-', 'foreign-', 1)):
        try:
            runner.service_leaf(bad)
        except RuntimeError:
            pass
        else:
            raise AssertionError('Invalid target accepted')
    for label, change in (('leaf', 1), ('interface', 1)):
        bad = copy.deepcopy(custody); bad[label][1] += change
        try:
            runner.service_leaf(unit, bad)
        except RuntimeError:
            pass
        else:
            raise AssertionError('Changed cgroup inode accepted')
    with patch.object(runner.os, 'geteuid', return_value=0):
        try:
            runner.service_leaf(unit)
        except RuntimeError:
            pass
        else:
            raise AssertionError('Privileged helper identity accepted')
    with patch.object(runner.os, 'access', return_value=False):
        try:
            runner.service_leaf(unit)
        except RuntimeError:
            pass
        else:
            raise AssertionError('Undelegated interface accepted')
    passed.append('delegated-leaf-invalid-target-owner-and-inode-rejected-without-write')

    def resident(path):
        with path.open('rb') as stream, mmap.mmap(stream.fileno(), 0, access=mmap.ACCESS_COPY) as mapped:
            anchor = ctypes.c_char.from_buffer(mapped)
            vector = (ctypes.c_ubyte * (len(mapped)//mmap.PAGESIZE))()
            library = ctypes.CDLL(None, use_errno=True)
            library.mincore.argtypes = (ctypes.c_void_p, ctypes.c_size_t, ctypes.c_void_p)
            assert library.mincore(ctypes.addressof(anchor), len(mapped), vector) == 0
            amount = sum(value & 1 for value in vector)*mmap.PAGESIZE
            del anchor
            return amount

    with tempfile.TemporaryDirectory(prefix='delegated-real-fixture-', dir=workspace) as directory:
        root = Path(directory); run = root/'run'; run.mkdir()
        guard = runner.Guard(run)
        cfg = {'workspace': str(root), 'runner_sha256': runner.digest(runner.__file__),
               'delegated_reclaim': {'unit': unit}, 'flow_control': True}
        if wider:
            cfg=wider_profile_config(cfg)
            runner.write_json(run/'admission.json',cfg)
        replay = runner.Replay(cfg, run, guard)
        actual_samples = []
        interface_boundaries = []
        native_request = replay.delegated_reclaim.request
        def computed_request(process, snapshot, number, checkpoint, deadline):
            first = [True]
            if interface_sizing:
                def interface_checkpoint():
                    capture = first[0]
                    injected_deficit_checkpoint(guard, checkpoint, actual_samples, first, 3989532672)
                    if capture:
                        boundary = {'cycle': number, 'utc': runner.now(),
                            'actual_parent': actual_samples[-1], 'actual_leaf': runner.leaf_resources(leaf),
                            'actual_resident_bytes': resident(path),
                            'synthetic_policy_parent_bytes': 3989532672,
                            'computed_request_bytes': runner.deficit_reclaim_policy(3989532672,
                                mmap.PAGESIZE, runner.WIDER_REFILL_PROFILE)['request_bytes'],
                            'scope': 'Actual request-boundary measurements after complete epoch; only the separately labelled policy input is injected'}
                        assert boundary['computed_request_bytes'] == 533426176
                        assert boundary['actual_resident_bytes'] >= 524288000
                        interface_boundaries.append(boundary)
                        runner.write_json(run/f'interface-cycle-{number}-request-boundary.json', boundary)
                return native_request(process, snapshot, number, interface_checkpoint, deadline)
            if wider:
                def actual_checkpoint():
                    checkpoint()
                    if first[0]:
                        first[0]=False
                        actual=runner.observe();runner.validate_observation(actual)
                        assert actual['events']==guard.baseline['events']
                        actual_samples.append(actual);guard.last=actual
                        policy=runner.deficit_reclaim_policy(actual['memory_current'],mmap.PAGESIZE,runner.WIDER_REFILL_PROFILE)
                        assert policy['request_bytes']>=500*2**20,'Real wider deficit prerequisite unavailable; no injected fallback'
                return native_request(process,snapshot,number,actual_checkpoint,deadline)
            return native_request(process, snapshot, number,
                lambda: injected_deficit_checkpoint(guard, checkpoint, actual_samples, first), deadline)
        replay.delegated_reclaim.request = computed_request
        path = root/'mapped-input.bin'
        fixture_mib=640 if wider else 256
        fixture_bytes=fixture_mib*2**20
        reserve=192*2**20
        if wider:
            guard.check()
            fixture_reserve_check(evidence, 'baseline', None, guard.last['memory_current'],
                fixture_bytes, reserve, int(runner.LIMITS['memory.high']),
                'Wider fixture baseline/remaining-charge reserve failed')
        block = bytes((i+3) % 256 for i in range(2**20))
        with path.open('xb') as stream:
            for index in range(fixture_mib):
                if wider:
                    guard.check()
                    fixture_reserve_check(evidence, 'creation', index, guard.last['memory_current'],
                        (fixture_mib-index)*2**20, reserve, int(runner.LIMITS['memory.high']),
                        'Wider fixture creation reserve failed')
                stream.write(block)
                guard.check()
            stream.flush(); os.fsync(stream.fileno())
            if not wider:
                os.posix_fadvise(stream.fileno(), 0, 0, os.POSIX_FADV_DONTNEED)
        original = runner.digest(path); original_stat = path.stat()
        if wider:
            guard.check()
            with path.open('rb') as stream:
                os.posix_fadvise(stream.fileno(),0,0,os.POSIX_FADV_DONTNEED)
        code = ('import mmap,pathlib,time\n'
            'p=pathlib.Path('+repr(str(path))+');f=p.open("rb");m=mmap.mmap(f.fileno(),0,access=mmap.ACCESS_COPY)\n'
            'for cycle in (1,2):\n'
            ' if cycle==2:\n'
            '  while not (p.parent/"refault").exists():time.sleep(.01)\n'
            ' checksum=sum(m[i] for i in range(0,len(m),4096))\n'
            ' (p.parent/("ready-"+str(cycle))).write_text(str(checksum))\n'
            'while True:time.sleep(.1)\n')
        if wider:
            code=('import mmap,pathlib,time\n'
                'p=pathlib.Path('+repr(str(path))+');f=p.open("rb");m=mmap.mmap(f.fileno(),0,access=mmap.ACCESS_COPY)\n'
                'for cycle in (1,2):\n'
                ' if cycle==2:\n'
                '  while not (p.parent/"refault").exists():time.sleep(.01)\n'
                ' checksum=0\n'
                ' for index,offset in enumerate(range(0,len(m),16*2**20)):\n'
                '  (p.parent/("need-%d-%d"%(cycle,index))).write_text("ready")\n'
                '  while not (p.parent/("grant-%d-%d"%(cycle,index))).exists():time.sleep(.01)\n'
                '  checksum+=sum(m[i] for i in range(offset,min(offset+16*2**20,len(m)),4096))\n'
                ' (p.parent/("ready-"+str(cycle))).write_text(str(checksum))\n'
                'while True:time.sleep(.1)\n')
        process = subprocess.Popen(['python3', '-c', code], start_new_session=True)
        runner.capture_stage_identity(process)
        replay.immutable_input_roots = [root]
        replay.recent_input_mappings[str(path)] = False
        replay.input_cache_advice['unadvised_files'] = 1
        try:
            for cycle in (1, 2):
                if cycle == 2:
                    (root/'refault').write_text('refault unchanged bytes')
                deadline = time.monotonic()+(30 if wider else 10)
                if wider:
                    for index in range(fixture_mib//16):
                        while not (root/f'need-{cycle}-{index}').exists():
                            guard.check();assert time.monotonic()<deadline;time.sleep(.01)
                        guard.check()
                        remaining=fixture_bytes-resident(path)
                        fixture_reserve_check(evidence, 'refault', index, guard.last['memory_current'],
                            remaining, reserve, int(runner.LIMITS['memory.high']),
                            'Wider fixture refault remaining-charge reserve failed', cycle=cycle)
                        (root/f'grant-{cycle}-{index}').write_text('bounded16MiB touch')
                while not (root/f'ready-{cycle}').exists():
                    guard.check(); assert time.monotonic() < deadline; time.sleep(.01)
                guard.check()
                before = resident(path)
                assert before == fixture_bytes
                replay.flow_trigger = 1
                if not wider:
                    replay.flow_resume = guard.last['memory_current']-100204544
                else:
                    fixture_reserve_check(evidence, 'charged-ready', None, guard.last['memory_current'],
                        0, reserve, int(runner.LIMITS['memory.high']),
                        'Wider fixture charged-state reserve failed', cycle=cycle)
                    if interface_sizing:
                        replay.flow_resume = guard.last['memory_current']-100204544
                        assert replay.flow_resume > 0
                        forcing = {'cycle': cycle, 'mode': 'explicit-captured-v07-interface-only',
                            'actual_cycle_start_parent_bytes': guard.last['memory_current'],
                            'production_trigger_bytes': 4026531840, 'fixture_trigger_bytes': 1,
                            'production_resume_bytes': 3489660928,
                            'fixture_resume_bytes': replay.flow_resume,
                            'fixture_resume_offset_bytes': 100204544,
                            'synthetic_policy_parent_bytes': 3989532672,
                            'synthetic_policy_request_bytes': 533426176,
                            'flow_summary_scope': 'Configured production profile only; actual fixture behavior uses the explicitly recorded fixture_trigger_bytes and fixture_resume_bytes',
                            'scope': 'Test-only forced entry/threshold and captured sizing; not an actual production deficit or Lean resume qualification'}
                        runner.write_json(run/f'interface-cycle-{cycle}-forcing.json', forcing)
                        replay.flow_record('interface-fixture-forcing', **forcing)
                    else:
                        assert guard.last['memory_current']>replay.flow_resume,'No actual wider deficit; no fallback'
                replay.maybe_flow_control(process, guard.check)
                after = resident(path)
                measurement = json.loads((run/f'reclaim-{cycle}-measurement.json').read_text())
                request = json.loads((run/f'reclaim-{cycle}-request.json').read_text())
                receipt = json.loads((run/f'reclaim-{cycle}-terminal.json').read_text())
                actual_after = runner.observe(); runner.validate_observation(actual_after)
                assert actual_after['events'] == guard.baseline['events']
                amount=request['policy']['request_bytes']
                assert amount>=500*2**20 if wider else amount==195096576
                assert receipt['request']==str(amount)+' swappiness=0' and receipt['exit_code']==0
                if interface_sizing:
                    actual_leaf_after = runner.leaf_resources(leaf)
                    boundary = interface_boundaries[-1]
                    assert amount == 533426176 and request['parent_sample']['memory_current'] == 3989532672
                    relief = {'parent_bytes': boundary['actual_parent']['memory_current']-actual_after['memory_current'],
                        'leaf_bytes': boundary['actual_leaf']['current']-actual_leaf_after['current'],
                        'mapped_file_bytes': boundary['actual_resident_bytes']-after}
                    result = {'cycle': cycle, 'request_boundary': boundary,
                        'actual_parent_after': actual_after, 'actual_leaf_after': actual_leaf_after,
                        'actual_resident_after_bytes': after, 'actual_relief': relief,
                        'scope': 'Interface effect only; injected policy sample is never an actual relief operand'}
                    runner.write_json(run/f'interface-cycle-{cycle}-actual-result.json', result)
                    assert all(value >= 524288000 for value in relief.values()), relief
                    assert actual_leaf_after['events'] == boundary['actual_leaf']['events']
                else:
                    relief_floor=amount-32*2**20 if wider else 161542144
                    assert before-after>relief_floor
                    assert measurement['before']['leaf']['current']-measurement['after']['leaf']['current']>relief_floor
                    assert actual_samples[-1]['memory_current']-actual_after['memory_current']>relief_floor
                if wider and not interface_sizing:
                    assert actual_after['memory_current']<=3489660928
                    assert request['parent_sample']['memory_current']==actual_samples[-1]['memory_current']
                assert process.poll() is None and replay.delegated_reclaim.summary['requests'] == cycle
                metrics.append({'cycle': cycle, 'resident_before': before, 'resident_after': after,
                    'measurement': measurement, 'actual_parent_before': actual_samples[-1],
                    'actual_parent_after': actual_after,
                    'policy_sample_scope': ('Explicit captured v07 interface sizing and labelled fixture trigger/resume; actual request-boundary relief is stored independently, no actual-deficit/Lean-fit claim' if interface_sizing else 'Actual fresh parent deficit; no injected positive sizing or fallback' if wider else 'Injected pause4 sizing input after successful real raw guard; actual parent reduction uses actual_parent_before, not injected measurement.before.parent_current'),
                    'request': request, 'receipt': receipt})
                preserve(run, 'real-two-cycle')
            events = [json.loads(line) for line in (run/'flow-control.jsonl').read_text().splitlines()]
            assert sum(row['kind']=='epoch-completed' for row in events) == 2
            assert sum(row['kind']=='resumed' for row in events) == 2
        finally:
            runner.terminate_owned(process)
            preserve(run, 'real-two-cycle')
        assert runner.digest(path) == original
        current = path.stat()
        assert (current.st_ino, current.st_size, current.st_mtime_ns, current.st_ctime_ns) == (
            original_stat.st_ino, original_stat.st_size, original_stat.st_mtime_ns, original_stat.st_ctime_ns)
        guard.check()
        passed.append('delegated-reclaim-two-complete-epochs-one-request-each-real-charge-mincore-refault-byte-preservation')

    native_popen = subprocess.Popen
    cases = ('eagain', 'partial', 'timeout', 'late-completion', 'control-hash',
                 'unexpected-member', 'stage-birth', 'nonquiescent', 'guard-fault',
                 'interrupt-after-spawn', 'cleanup-census-fault',
                 'successful-write-no-headroom', 'headroom-already-met', 'fresh-headroom-recovered',
                  'duplicate-request', 'insufficient-cleanup-budget')
    if wider:
        cases += ('profile-downgrade', 'admission-mutation')
    for case in cases:
        with tempfile.TemporaryDirectory(prefix='delegated-fault-fixture-', dir=workspace) as directory:
            root = Path(directory); run = root/'run'; run.mkdir()
            guard = runner.Guard(run)
            cfg = {'workspace': str(root), 'runner_sha256': runner.digest(runner.__file__),
                   'delegated_reclaim': {'unit': unit}, 'flow_control': True}
            if wider:
                cfg=wider_profile_config(cfg)
                runner.write_json(run/'admission.json',cfg)
            replay = runner.Replay(cfg, run, guard)
            replay.immutable_input_roots = [root]
            process = native_popen(['python3', '-c', 'import time;time.sleep(60)'], start_new_session=True)
            runner.capture_stage_identity(process)
            child_rows, error, count = [], None, [0]
            def spawn(command, *args, **kwargs):
                if '--delegated-reclaim' not in command:
                    return native_popen(command, *args, **kwargs)
                count[0] += 1
                injection = ''
                if case == 'eagain':
                    injection = 'def fake(fd,data):raise OSError(11,"injected EAGAIN")\nr.os.write=fake\n'
                elif case == 'partial':
                    injection = 'r.os.write=lambda fd,data:len(data)-1\n'
                elif case == 'timeout':
                    injection = 'def fake(fd,data):time.sleep(60);return len(data)\nr.os.write=fake\n'
                else:
                    injection = 'r.os.write=lambda fd,data:len(data)\n'
                if case == 'profile-downgrade':
                    injection += ('q=r.Path(sys.argv[1]);v=r.json.loads(q.read_text());'
                        'v.pop("reclaim_profile");v.pop("admission_binding");'
                        'v["policy"]=r.deficit_reclaim_policy(v["parent_sample"]["memory_current"],r.os.sysconf("SC_PAGE_SIZE"));'
                        'r.write_json(q,v);sys.argv[2]=r.digest(q)\n')
                if case == 'admission-mutation':
                    injection += ('q=r.Path(sys.argv[1]);v=r.json.loads(q.read_text());'
                        'a=r.Path(v["admission_binding"]["path"]);c=r.json.loads(a.read_text());'
                        'c.pop("reclaim_profile");r.write_json(a,c)\n')
                wrapped = ('import sys,time\nsys.path.insert(0,'+repr(str(Path(runner.__file__).parent))+')\n'
                           'import jw_cpu_runner as r\n'+injection+
                           'raise SystemExit(r.delegated_reclaim_child(*sys.argv[1:]))\n')
                child = native_popen(['python3', '-c', wrapped, *command[command.index('--delegated-reclaim')+1:]], *args, **kwargs)
                if case == 'late-completion':
                    native_poll, native_wait = child.poll, child.wait
                    first = [True]
                    def late_poll():
                        if first[0]:
                            first[0] = False
                            native_wait(timeout=2)
                            time.sleep(.3)
                        return native_poll()
                    child.poll = late_poll
                child_rows.append(child)
                return child
            original_record = replay.flow_record
            def record(kind, **extra):
                original_record(kind, **extra)
                if kind == 'epoch-completed':
                    if case == 'fresh-headroom-recovered':
                        guard.last = copy.deepcopy(guard.last)
                        guard.last['memory_current'] = 4053856256
                    if case == 'duplicate-request':
                        (run/'reclaim-1-request.json').write_text('preserved earlier attempt')
                    if case == 'control-hash':
                        cfg['runner_sha256'] = '0'*64
                    if case == 'stage-birth':
                        process.jw_identity['leader_start_ticks'] = str(int(process.jw_identity['leader_start_ticks'])+1)
                    if case == 'nonquiescent':
                        os.killpg(process.pid, runner.signal.SIGCONT)
            replay.flow_record = record
            replay.flow_trigger = 1
            replay.flow_resume = (2**62 if case == 'headroom-already-met' else
                                  (3489660928 if wider else 3892314112) if case == 'fresh-headroom-recovered' else 1)
            native_request = replay.delegated_reclaim.request
            def request(*args):
                values = list(args)
                if case != 'fresh-headroom-recovered':
                    first = [True]; native_checkpoint = values[-2]
                    values[-2] = lambda: injected_deficit_checkpoint(guard, native_checkpoint, [], first,
                        3989532672 if wider else 4053856256)
                if case in ('timeout', 'late-completion'):
                    values[-1] = time.monotonic()+10.25
                if case == 'insufficient-cleanup-budget':
                    values[-1] = time.monotonic()+9
                return native_request(*values)
            replay.delegated_reclaim.request = request
            capture = runner.capture_stage_identity
            def capture_interrupt(child):
                result = capture(child)
                if case == 'interrupt-after-spawn':
                    raise KeyboardInterrupt('injected post-capture interrupt')
                return result
            original_reader = guard.reader
            def checkpoint():
                if case == 'guard-fault' and child_rows:
                    value = original_reader(); value['root_available_bytes'] = runner.MIN_FREE-1
                    guard.reader = lambda: value
                guard.check()
            original_members = runner.reclaim_members
            def membership(request, writer_pid=None):
                if case == 'unexpected-member':
                    request = copy.deepcopy(request)
                    request['stage_snapshot'].append([999999999, '0', []])
                return original_members(request, writer_pid)
            original_identity = copy.deepcopy(process.jw_identity)
            original_owned = runner.owned_group_members
            original_signal = runner.os.killpg
            signals = []
            def signal_group(pid, signum):
                signals.append((pid, signum))
                return original_signal(pid, signum)
            def owned(identity):
                if case == 'cleanup-census-fault' and child_rows and identity and \
                        identity['leader_pid'] == child_rows[0].pid:
                    raise RuntimeError('injected final helper ownership census failure')
                return original_owned(identity)
            try:
                with patch.object(runner.subprocess, 'Popen', spawn), \
                     patch.object(runner, 'capture_stage_identity', capture_interrupt), \
                     patch.object(runner, 'reclaim_members', membership), \
                     patch.object(runner, 'owned_group_members', owned), \
                     patch.object(runner.os, 'killpg', signal_group):
                    replay.maybe_flow_control(process, checkpoint)
            except BaseException as exc:
                error = type(exc).__name__+': '+str(exc)
            finally:
                guard.reader = original_reader
                process.jw_identity = original_identity
                runner.terminate_owned(process)
                for child in child_rows:
                    if case == 'cleanup-census-fault':
                        assert not any(pid == child.pid for pid, _ in signals), 'Signal sent under uncertain helper custody'
                    # Fault injection is removed. Only the restored, captured
                    # real identity may now be used for fixture cleanup.
                    if child.poll() is None or (getattr(child, 'jw_identity', None) and
                            any(row['state'] != 'Z' for row in runner.owned_group_members(child.jw_identity))):
                        runner.terminate_owned(child)
                    assert child.poll() is not None, 'Request child stranded'
                    if getattr(child, 'jw_identity', None):
                        assert not any(row['state'] != 'Z' for row in runner.owned_group_members(child.jw_identity))
                preserve(run, case)
            if case in ('headroom-already-met', 'fresh-headroom-recovered'):
                assert error is None and count[0] == 0
            else:
                assert error is not None and count[0] <= 1
                if case == 'successful-write-no-headroom':
                    assert 'NO_HEADROOM' in error and count[0] == 1
                if case == 'late-completion':
                    assert 'completed after request deadline' in error
                if case in ('profile-downgrade','admission-mutation'):
                    assert count[0]==1
                    assert not (run/'reclaim-1-attempt.json').exists(), 'Rejected binding reached reclaim write'
            assert replay.delegated_reclaim.summary['cleanup_verified'] == (case != 'cleanup-census-fault')
            metrics.append({'case': case, 'error': error, 'requests': count[0],
                            'pause_seconds': replay.flow_summary['total_pause_seconds']})
            print(json.dumps({'delegated_case': metrics[-1]}), flush=True)
            passed.append('delegated-reclaim-'+case+'-bounded-no-retry-cleanup')
    # No host migration: inject census rows and current path/birth reads only.
    own = runner.process_identity(os.getpid())
    row = dict(own, comm='lean', cgroup='0::'+str(leaf).removeprefix('/sys/fs/cgroup'))
    runner.validate_compiler_placement([row], leaf)
    bad = dict(row, cgroup='0::/injected-foreign-leaf')
    try:
        runner.validate_compiler_placement([bad], leaf)
    except RuntimeError:
        pass
    else:
        raise AssertionError('Surviving foreign compiler placement accepted')
    for bad in ({'pid': os.getpid(), 'comm': 'lake', 'uid': runner.UID,
                 'visibility_error': 'PermissionError'},
                dict(row, start_ticks=None), dict(row, cgroup=None)):
        try:
            runner.validate_compiler_placement([bad], leaf)
        except RuntimeError:
            pass
        else:
            raise AssertionError('Surviving incomplete census evidence accepted')
    with patch.object(runner, 'process_identity', side_effect=FileNotFoundError):
        runner.validate_compiler_placement([dict(row)], leaf)
    with patch.object(runner, 'process_identity', return_value=dict(own, start_ticks='0')):
        runner.validate_compiler_placement([dict(row)], leaf)
    passed.append('delegated-compiler-placement-stable-birth-escape-and-vanished-PID-dispositions')
    print(json.dumps({'delegated_reclaim_fixture': metrics}), flush=True)
    return passed


def normal_flow_checkpoint_fixture(workspace):
    """Native stage lifecycle and response faults; paused callbacks never recurse."""
    metrics = []
    for case in ('checkpoint-order', 'paused-time', 'decision-gap', 'natural-exit',
                 'live-descendant', 'guard-fault'):
        with tempfile.TemporaryDirectory(prefix='normal-flow-fixture-', dir=workspace) as directory:
            root = Path(directory); run = root/'run'; run.mkdir()
            child_ready, release_parent = root/'child-ready', root/'release-parent'
            print(json.dumps({'normal_flow_case_started': case}), flush=True)
            guard = runner.Guard(run)
            replay = runner.Replay({'workspace': str(root), 'flow_control': True}, run, guard)
            order = []; calls = [0]; depth = [0, 0]
            original_flow = replay.maybe_flow_control
            def decision(process, checkpoint):
                depth[0] += 1; depth[1] = max(depth)
                try:
                    calls[0] += 1; order.append('flow')
                    return original_flow(process, checkpoint)
                finally:
                    depth[0] -= 1
            replay.maybe_flow_control = decision
            native_reader = guard.reader
            first = [True]
            def ordinary_read():
                order.append('qualified')
                if not first[0]:
                    return
                first[0] = False
                if case == 'live-descendant':
                    deadline = time.monotonic()+3
                    while not child_ready.exists():
                        guard.check(); assert time.monotonic() < deadline; time.sleep(.01)
                    identity = replay.stages['build']['process_group_identity']
                    members = runner.owned_group_members(identity)
                    assert int(child_ready.read_text()) in {row['pid'] for row in members}
                    release_parent.write_text('child enrolled while original leader is alive')
                if case in ('decision-gap', 'natural-exit', 'live-descendant'):
                    time.sleep(1.15)
                if case == 'guard-fault':
                    def fail_closed():
                        value = native_reader(); value['root_available_bytes'] = runner.MIN_FREE-1
                        return value
                    guard.reader = fail_closed
            replay.release_qualified_read_cache = ordinary_read
            replay.release_import_readahead = lambda: order.append('mapped')
            replay.release_own_clean_cache = lambda: order.append('closed')
            if case == 'paused-time':
                replay.immutable_input_roots = [root]
                replay.flow_trigger = 1
                original_record = replay.flow_record
                def pause_record(kind, **extra):
                    original_record(kind, **extra)
                    if kind == 'paused':
                        time.sleep(1.15); guard.check()
                    if kind == 'resumed':
                        replay.flow_trigger = 2**62
                replay.flow_record = pause_record
            code = 'import time; time.sleep(2)'
            if case in ('decision-gap', 'guard-fault'):
                code = 'import time; time.sleep(60)'
            elif case == 'natural-exit':
                code = 'import time; time.sleep(.2)'
            elif case == 'live-descendant':
                code = ('import subprocess,time,pathlib\n'
                        'child=subprocess.Popen(["python3","-c","import time; time.sleep(5)"])\n'
                        'pathlib.Path('+repr(str(child_ready))+').write_text(str(child.pid))\n'
                        'deadline=time.monotonic()+5\n'
                        'while not pathlib.Path('+repr(str(release_parent))+').exists() and '
                        'time.monotonic()<deadline: time.sleep(.01)\n')
            error = None
            try:
                replay.stage('build', ['python3', '-c', code])
            except RuntimeError as exc:
                error = str(exc)
            finally:
                guard.reader = native_reader
            stage = replay.stages['build']
            print(json.dumps({'normal_flow_case_terminal': case, 'error': error,
                'exit_code': stage['exit_code'], 'identity': stage['process_group_identity'],
                'decision_checks': stage['flow_decision_checks'],
                'maximum_decision_gap': stage['maximum_flow_decision_gap_seconds'],
                'pause_seconds': replay.flow_summary['total_pause_seconds']}), flush=True)
            assert not any(row['state'] != 'Z' for row in
                           runner.owned_group_members(stage['process_group_identity']))
            assert depth[0] == 0 and depth[1] == 1
            if case == 'decision-gap':
                assert error == 'Flow decision gap exceeded 1 second', error
                assert stage['maximum_flow_decision_gap_seconds'] > 1
                assert stage['exit_code'] != 0
            elif case == 'guard-fault':
                assert error and stage['exit_code'] != 0
            elif case == 'live-descendant':
                assert error == 'Stage leader exited with live descendants', error
            else:
                assert error is None and stage['exit_code'] == 0, error
                assert stage['maximum_flow_decision_gap_seconds'] <= 1
                if case == 'checkpoint-order':
                    assert order[:7] == ['flow', 'qualified', 'flow', 'mapped', 'flow', 'closed', 'flow']
                if case == 'paused-time':
                    assert replay.flow_summary['pauses'] == 1
                    assert replay.flow_summary['total_pause_seconds'] > 1
                if case == 'natural-exit':
                    assert calls[0] == 1  # Completion never becomes a stale-gap fault.
            metrics.append({'case': case, 'exit_code': stage['exit_code'], 'error': error,
                'decision_checks': stage['flow_decision_checks'],
                'maximum_decision_gap': stage['maximum_flow_decision_gap_seconds'],
                'pause_seconds': replay.flow_summary['total_pause_seconds'], 'maximum_depth': depth[1]})
    print(json.dumps({'normal_flow_checkpoint_fixture': metrics}), flush=True)
    return ['normal-stage-flow-decisions-follow-every-guard-checkpoint',
            'paused-time-excluded-from-one-second-decision-gap-without-recursion',
            'live-decision-gap-and-host-guard-faults-cleanly-terminate-owned-group',
            'natural-completion-preserved-and-live-descendant-custody-enforced']


def epoch_fixture(workspace, scale=False):
    """Independent union/receipt oracle, including old-tail and identical pauses."""
    with tempfile.TemporaryDirectory(prefix='paused-epoch-fixture-', dir=workspace) as directory:
        root = Path(directory); inputs = root/'inputs'; inputs.mkdir()
        run = root/'run'; run.mkdir()
        guard = runner.Guard(run)
        counts = (52936, 35396, 43269) if scale else (4, 3, 2)
        total = sum(counts)
        before = guard.last
        # Sparse files provide distinct real inodes without charging half a GiB
        # of artificial data residency before the control-overhead measurement.
        # Real arriving bytes/refault/COW remain separate existing native tests.
        for index in range(total):
            folder = inputs/f'{index//512:04d}'; folder.mkdir(exist_ok=True)
            fd = os.open(folder/f'{index:06d}.olean', os.O_CREAT|os.O_EXCL|os.O_WRONLY, 0o600)
            os.ftruncate(fd, 4096); os.close(fd)
            if index % 256 == 0:
                guard.check()
        def path(index):
            return inputs/f'{index//512:04d}/{index:06d}.olean'
        ready = root/'ready'
        helper = root/'family.py'
        helper.write_text('import mmap,os,pathlib,subprocess,sys,threading,time\n'
            'root=pathlib.Path('+repr(str(inputs))+')\n'
            'n=int(sys.argv[1]); lo=int(sys.argv[2]); maps=[]\n'
            'for i in range(lo,n):\n'
            ' p=root/f"{i//512:04d}/{i:06d}.olean"\n'
            ' with p.open("rb") as f:maps.append(mmap.mmap(f.fileno(),0,access=mmap.ACCESS_COPY,trackfd=False))\n'
            'threading.Thread(target=lambda:time.sleep(240),daemon=True).start()\n'
            'if lo==0:\n'
            ' p=subprocess.Popen([sys.executable,__file__,str(n*2),str(n)])\n'
            ' while not pathlib.Path('+repr(str(ready))+').with_suffix(".child").exists():time.sleep(.01)\n'
            ' pathlib.Path('+repr(str(ready))+').write_text(str(p.pid))\n'
            'else:pathlib.Path('+repr(str(ready))+').with_suffix(".child").write_text(str(os.getpid()))\n'
            'time.sleep(240)\n')
        # Leave one historical-only file in small fixture; the real-scale
        # snapshot maps all52936 files across two owned multithread processes.
        half = counts[0]//2 if scale else 1
        process = subprocess.Popen(['python3',str(helper),str(half),'0'],start_new_session=True)
        identity = runner.capture_stage_identity(process)
        epoch = None
        evidence = Path(__file__).parent/'epoch-fixture-evidence'/('scale' if scale else 'small')
        evidence.mkdir(parents=True,exist_ok=True)
        try:
            deadline=time.monotonic()+60
            while not ready.exists():
                guard.check(); assert time.monotonic()<deadline;time.sleep(.02)
            os.killpg(process.pid,runner.signal.SIGSTOP)
            deadline=time.monotonic()+5
            while True:
                try:snapshot=runner.quiescent_group_snapshot(identity);break
                except RuntimeError:
                    assert time.monotonic()<deadline;time.sleep(.01)
            assert len(snapshot)==2 and all(len(row[2])>=2 for row in snapshot)
            replay=runner.Replay({'workspace':str(root)},run,guard)
            replay.immutable_input_roots=[inputs]
            for index in range(counts[0]):replay.recent_input_mappings[str(path(index))]=True
            # Deliberate inherited tail from the reviewer's counterexample.
            replay.advice_round_remaining=1;replay.advice_round_size=counts[0]
            replay.input_cache_advice.update(advice_rounds_completed=10,
                largest_completed_advice_round_files=counts[0],unadvised_files=0)
            def qualified():
                yield inputs,{'path':path(0).relative_to(inputs).as_posix(),'bytes':4096}
                yield None
                for index in range(counts[0],total):
                    yield inputs,{'path':path(index).relative_to(inputs).as_posix(),'bytes':4096}
            replay.qualified_read_records=qualified
            metrics=[]
            for cycle in range(2):
                replay.flow_summary['pauses']+=1
                guard.check(); initial=guard.last;max_interval=0;last=time.monotonic()
                maximum_pss=0;maximum_memory=guard.last['memory_current'];peak_resources=guard.last
                def checkpoint():
                    nonlocal max_interval,last,maximum_pss,maximum_memory,peak_resources
                    tick=time.monotonic();max_interval=max(max_interval,tick-last);last=tick
                    guard.check()
                    if guard.last['memory_current']>maximum_memory:
                        maximum_memory=guard.last['memory_current'];peak_resources=guard.last
                    for row in guard.last.get('compiler_processes',[]):
                        if row['pid']==os.getpid():
                            maximum_pss=max(maximum_pss,(row.get('smaps_rollup_bytes') or {}).get('Pss',0))
                start=time.monotonic()
                epoch=runner.PausedInputEpoch(replay,identity,snapshot,checkpoint)
                last_progress=start
                while not epoch.step():
                    if time.monotonic()-last_progress>=5:
                        progress={'phase':epoch.phase,'phase_elapsed':time.monotonic()-epoch.phase_started,
                            'elapsed_seconds':time.monotonic()-start,'stats':epoch.stats,
                            'maximum_controller_pss':maximum_pss,'peak_resources':peak_resources}
                        runner.write_json(evidence/f'cycle-{cycle+1}-progress.json',progress)
                        print(json.dumps({'epoch_progress':{k:v for k,v in progress.items() if k!='peak_resources'}}),flush=True)
                        last_progress=time.monotonic()
                    assert time.monotonic()-start<120,'Epoch120s scale target exceeded'
                assert epoch.stats['members']==total and epoch.stats['receipts']==total
                assert epoch.stats['mapping_scans']==2
                stats=dict(epoch.stats);epoch.close();epoch=None
                assert replay.input_cache_advice['unadvised_files']==0
                assert all(value is True for value in replay.recent_input_mappings.values())
                checkpoint();elapsed=time.monotonic()-start
                assert elapsed<120 and max_interval<=1.0,(elapsed,max_interval)
                prefix=run/f'paused-epoch-{cycle+1:03d}'
                manifest=prefix.with_suffix('.cohort.jsonl.gz');receipts=prefix.with_suffix('.receipts.bin')
                assert hashlib.sha256(manifest.read_bytes()).hexdigest()==stats['cohort_sha256']
                ordinals={}
                with gzip.open(manifest,'rt') as stream:
                    for line in stream:
                        e,ordinal,value,identity_hex,flags=json.loads(line)
                        assert e==cycle+1 and value not in ordinals
                        ordinals[value]=ordinal
                assert set(ordinals)=={str(path(index)) for index in range(total)}
                found=set()
                with receipts.open('rb') as stream:
                    while record:=stream.read(24):
                        e,ordinal,stamp=struct.unpack('<QQQ',record)
                        assert e==cycle+1 and ordinal not in found and stamp>=stats['started_monotonic_ns']
                        found.add(ordinal)
                assert found==set(ordinals.values())
                del ordinals,found
                assert len(replay.recent_input_mappings)==counts[0]
                metrics.append({'cycle':cycle+1,'elapsed_seconds':elapsed,'maximum_guard_interval':max_interval,
                    'initial':initial,'final':guard.last,'epoch':stats,
                    'maximum_controller_pss':maximum_pss,'peak_resources':peak_resources})
            print(json.dumps({'paused_epoch_scale' if scale else 'paused_epoch_correctness':{
                'distinct_files':total,'sparse_fixture':True,'owned_multithread_processes':2,
                'guard_before_setup':before,'cycles':metrics}}),flush=True)
        finally:
            if epoch is not None:
                failure={'phase':epoch.phase,'phase_elapsed':time.monotonic()-epoch.phase_started,
                    'stats':epoch.stats,'guard':guard.summary()}
                epoch.close(restore=False)
                runner.write_json(evidence/'failure.json',failure)
                print(json.dumps({'epoch_failure_state':failure}),flush=True)
            runner.terminate_owned(process)
            for artifact in run.glob('paused-epoch-*'):
                shutil.copyfile(artifact,evidence/artifact.name)
        return ['fresh-epoch-distinct-union-unique-post-epoch-receipts',
                'inherited-tail-and-repeated-identical-pauses-do-not-reuse-success',
                'historical-unmapped-current-mapped-qualified-overlap-and-all-threads']


def epoch_fault_fixture(workspace):
    with tempfile.TemporaryDirectory(prefix='epoch-fault-fixture-',dir=workspace) as directory:
        root=Path(directory);inputs=root/'inputs';inputs.mkdir()
        process=subprocess.Popen(['python3','-c','import time;time.sleep(120)'],start_new_session=True)
        identity=runner.capture_stage_identity(process)
        native_advice=runner.os.posix_fadvise
        try:
            os.killpg(process.pid,runner.signal.SIGSTOP)
            until=time.monotonic()+5
            while True:
                try:snapshot=runner.quiescent_group_snapshot(identity);break
                except RuntimeError:
                    assert time.monotonic()<until;time.sleep(.01)
            cases=('missing','inode','size','advice-error','symlink','outside-root',
                   'conflicting-overlap','mapped-device-overlap','mapped-inode-overlap',
                   'metadata-stat-overlap','unexpected-resume','wrong-birth','wrong-session','wrong-uid')
            for case in cases:
                run=root/case;run.mkdir();p=inputs/(case+'.olean');p.write_bytes(b'unchanged fixture')
                guard=runner.Guard(run);replay=runner.Replay({'workspace':str(root)},run,guard)
                replay.immutable_input_roots=[inputs];replay.recent_input_mappings[str(p)]=True
                replay.flow_summary['pauses']=1
                if case=='symlink':
                    alias=inputs/'alias';alias.symlink_to(p);replay.recent_input_mappings[str(alias)]=True
                if case=='outside-root':replay.recent_input_mappings[str(run/'outside')]=True
                if case=='conflicting-overlap':
                    replay.qualified_read_records=lambda:iter([(inputs,{'path':p.name,'bytes':999})])
                native_record=replay.flow_record
                def mutation(kind,**extra):
                    native_record(kind,**extra)
                    if kind!='epoch-sealed':return
                    if case=='missing':p.unlink()
                    elif case=='inode':
                        old=p.with_suffix('.preserved');p.rename(old);p.write_bytes(b'unchanged fixture')
                    elif case=='size':p.write_bytes(b'changed length')
                    elif case=='advice-error':
                        def fail(*args):raise OSError('fixture advice failed')
                        runner.os.posix_fadvise=fail
                replay.flow_record=mutation
                epoch=runner.PausedInputEpoch(replay,identity,snapshot,guard.check)
                native_identity=runner.process_identity
                try:
                    if case=='unexpected-resume':os.killpg(process.pid,runner.signal.SIGCONT)
                    if case in ('wrong-birth','wrong-session','wrong-uid'):
                        def wrong(pid):
                            value=native_identity(pid)
                            if pid==process.pid:
                                field={'wrong-birth':'start_ticks','wrong-session':'session','wrong-uid':'uid'}[case]
                                value[field]=str(int(value[field])+1) if field=='start_ticks' else value[field]+1
                            return value
                        runner.process_identity=wrong
                    try:
                        if case in ('mapped-device-overlap','mapped-inode-overlap','metadata-stat-overlap'):
                            epoch.bind(str(p),epoch.HISTORICAL)
                            info=p.stat()
                            if case=='metadata-stat-overlap':
                                wrong=epoch.STAT.pack(info.st_dev,info.st_ino,info.st_mode,info.st_uid,
                                    info.st_size,info.st_mtime_ns,info.st_ctime_ns+1)
                                epoch.bind(str(p),epoch.ORDINARY,info.st_size,wrong)
                            else:
                                mapping=(os.major(info.st_dev)+(case=='mapped-device-overlap'),
                                    os.minor(info.st_dev),info.st_ino+(case=='mapped-inode-overlap'))
                                epoch.bind(str(p),epoch.HISTORICAL,mapping_identity=mapping)
                        while not epoch.step():pass
                    except (RuntimeError,OSError):pass
                    else:raise AssertionError('Epoch fault accepted: '+case)
                    assert not epoch.stats['complete']
                finally:
                    runner.os.posix_fadvise=native_advice;runner.process_identity=native_identity
                    epoch.close(restore=False)
                    if case=='unexpected-resume':
                        os.killpg(process.pid,runner.signal.SIGSTOP)
                        until=time.monotonic()+5
                        while True:
                            try:assert runner.quiescent_group_snapshot(identity)==snapshot;break
                            except (AssertionError,RuntimeError):
                                assert time.monotonic()<until;time.sleep(.01)
            assert process.poll() is None
        finally:
            runner.os.posix_fadvise=native_advice;runner.terminate_owned(process)
    return ['epoch-fails-closed-on-'+case for case in cases]


def paused_completion_fixture(workspace):
    with tempfile.TemporaryDirectory(prefix='paused-completion-',dir=workspace) as directory:
        root=Path(directory)
        for case in ('before-quiescence','during-scan'):
            run=root/case;run.mkdir();p=run/'input.olean';p.write_bytes(b'fixture')
            process=subprocess.Popen(['python3','-c','import time;time.sleep(.2)'],start_new_session=True)
            identity=runner.capture_stage_identity(process)
            guard=runner.Guard(run);replay=runner.Replay({'workspace':str(root),'flow_control':True},run,guard)
            replay.immutable_input_roots=[run];replay.recent_input_mappings[str(p)]=True
            replay.flow_trigger=1
            native_signal=os.killpg;native_open=Path.open
            controller_cont=[];injected=False
            def boundary_signal(pgid,signum):
                if signum==runner.signal.SIGCONT:controller_cont.append(pgid)
                if case=='before-quiescence' and signum==runner.signal.SIGSTOP:
                    # Model successful stop delivery to an already-completed
                    # zombie group, then observe the actual terminal status.
                    process.wait(timeout=3);return
                return native_signal(pgid,signum)
            def exit_during_scan(value,*args,**kwargs):
                nonlocal injected
                if case=='during-scan' and value==Path('/proc')/str(process.pid)/'maps' and not injected:
                    injected=True
                    # Explicit fixture continuation and natural zero exit at
                    # the actual /proc maps-open boundary, outside controller.
                    native_signal(process.pid,runner.signal.SIGCONT)
                    process.wait(timeout=3)
                return native_open(value,*args,**kwargs)
            try:
                runner.os.killpg=boundary_signal;Path.open=exit_during_scan
                replay.maybe_flow_control(process,guard.check)
                assert process.poll()==0 and not controller_cont
                assert all(type(value) is bool for value in replay.recent_input_mappings.values())
                events=[json.loads(line) for line in (run/'flow-control.jsonl').read_text().splitlines()]
                assert any(x['kind']=='stage-completed-without-resume' for x in events)
                assert not any(x['kind']=='resumed' for x in events)
            finally:
                runner.os.killpg=native_signal;Path.open=native_open
                if process.poll() is None:runner.terminate_owned(process)
    return ['terminal-zero-at-quiescence-and-during-scan-collected-without-controller-SIGCONT']


def metadata_custody_fixture(workspace):
    with tempfile.TemporaryDirectory(prefix='metadata-custody-',dir=workspace) as directory:
        root=Path(directory);path=root/'pkg/.lake/build/lib/member.trace'
        path.parent.mkdir(parents=True);path.write_bytes(b'original metadata')
        manifest=root/'manifest.jsonl.gz';receipt=root/'qualified.json'
        def capture(**changes):
            info=path.stat()
            row={'path':path.relative_to(root).as_posix(),'class':'previously-excluded-trace',
                'uid':info.st_uid,'mode':info.st_mode,'bytes':info.st_size,'device':info.st_dev,
                'inode':info.st_ino,'mtime_ns':info.st_mtime_ns,'ctime_ns':info.st_ctime_ns,
                'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
            row.update(changes)
            with gzip.open(manifest,'wt') as stream:stream.write(json.dumps(row)+'\n')
            return {'root':str(root),'manifest':str(manifest),
                'sha256':hashlib.sha256(manifest.read_bytes()).hexdigest(),'files':1}
        config=capture();runner.qualify_metadata(config,receipt)
        assert json.loads(receipt.read_text())['content_hashes_and_stat_verified']
        failures=['stat-mutation','wrong-content-hash','wrong-class','wrong-owner','path-traversal']
        # Each configuration must bind the manifest bytes it actually tests.
        for kind in failures:
            if kind=='stat-mutation':
                path.write_bytes(b'original metadata');config=capture();path.write_bytes(b'legitimate rewrite')
            elif kind=='wrong-content-hash':config=capture(sha256='0'*64)
            elif kind=='wrong-class':config=capture(**{'class':'previously-excluded-olean-hash'})
            elif kind=='wrong-owner':config=capture(uid=0)
            else:config=capture(path='../outside.trace')
            try:runner.qualify_metadata(config,receipt)
            except RuntimeError:pass
            else:raise AssertionError('Metadata custody fault accepted: '+kind)
    return ['exact-metadata-content-stat-custody-rejects-writes-hash-class-owner-and-path-faults']


def main():
    current = runner.observe()
    runner.validate_observation(current)
    passed = root_free_threshold_fixture(current) + compiler_host_pool_fixture(current)
    for name, mutate in [
        ('wrong-host', lambda v: v.update(host='cpu-02')),
        ('wrong-worker', lambda v: v.update(uid=0)),
        ('wrong-cgroup', lambda v: v.update(cgroup='0::/system.slice/example')),
        ('disk-reserve', lambda v: v.update(root_available_bytes=runner.MIN_FREE-1)),
        ('inode-reserve', lambda v: v.update(root_available_inodes=runner.MIN_INODES-1)),
        ('read-only-filesystem', lambda v: v.update(root_read_only=True)),
        ('memory-high', lambda v: v.update(memory_current=4*2**30)),
        ('changed-host-limits', lambda v: v['limits'].update({'pids.max':'512'})),
    ]:
        changed = copy.deepcopy(current); mutate(changed)
        try:
            runner.validate_observation(changed)
        except RuntimeError:
            passed.append(name)
        else:
            raise AssertionError('Admission incorrectly accepted '+name)
    workspace = runner.ROOT/'jacobian-weyl-20261110'
    with runner.lease(runner.ROOT/'locks/host-compiler.lock'):
        assert not runner.compiler_processes()
        with tempfile.TemporaryDirectory(prefix='guard-fixture-', dir=workspace) as directory:
            root = Path(directory)
            count = [0]
            def reader():
                count[0] += 1
                value = copy.deepcopy(current)
                if count[0] >= 4:
                    value['root_available_bytes'] = runner.MIN_FREE-1
                return value
            guard = runner.Guard(root, reader=reader)
            replay = runner.Replay({'workspace':str(workspace)}, root, guard)
            assert replay.flow_trigger == 4026531840
            assert replay.flow_resume == 3892314112
            assert replay.flow_resume < replay.flow_trigger <= 4*2**30-256*2**20
            assert replay.flow_resume-3707056128 == 185257984
            assert replay.flow_pause_timeout == 180
            assert replay.flow_aggregate_timeout == 600
            assert replay.flow_summary['maximum_pauses'] == 32
            assert replay.flow_summary['early_backlog_files'] == 8192
            passed.append('calibrated-flow-policy-preserves-original-host-guard-and-finite-budgets')
            try:
                replay.stage('harmless-loop', ['python3','-c','import time; time.sleep(60)'])
            except RuntimeError as exc:
                assert 'Root reserve failed' in str(exc)
            else:
                raise AssertionError('Running command was not stopped by guard')
            stage = replay.stages['harmless-loop']
            assert stage['exit_code'] == -15
            assert not Path('/proc', str(stage['pid'])).exists()
            passed.append('storage-guard-terminates-only-owned-process-group')
        with tempfile.TemporaryDirectory(prefix='serialize-fixture-', dir=workspace) as directory:
            root = Path(directory)
            actual = root/'fake-toolchain'; (actual/'bin').mkdir(parents=True)
            fake = actual/'bin/lean'
            fake.write_text('#!/usr/bin/python3\nimport os,sys,time\n'
                'if sys.argv[1:]==["--version"]: print("fixture"); sys.exit(0)\n'
                'p='+repr(str(root/'exclusive-marker'))+'\n'
                'fd=os.open(p,os.O_CREAT|os.O_EXCL|os.O_WRONLY,0o600)\n'
                'time.sleep(0.7)\nos.close(fd)\nos.unlink(p)\n')
            fake.chmod(0o700)
            leantar = actual/'bin/leantar'
            leantar.write_text('#!/usr/bin/python3\nimport sys\nassert sys.argv[1:]==["--jobs","1","--help"]\n')
            leantar.chmod(0o700)
            replay = runner.Replay({'workspace':str(workspace)}, root, runner.Guard(root))
            replay.serialized_toolchain(actual)
            wrapper = root/'serialized-toolchain/bin/lean'
            first = subprocess.Popen([str(wrapper),'fake-input.lean'])
            second = subprocess.Popen([str(wrapper),'fake-input.lean'])
            until = time.monotonic()+3
            while not (root/'exclusive-marker').exists() and time.monotonic()<until:
                time.sleep(0.01)
            assert (root/'exclusive-marker').exists()
            query = subprocess.run([str(wrapper),'--version'],capture_output=True,text=True,timeout=0.4)
            assert query.returncode == 0 and query.stdout.strip()=='fixture'
            assert first.wait(timeout=4)==0 and second.wait(timeout=4)==0
            passed.extend(['compiler-serialization-no-overlap', 'query-does-not-wait-for-compiler-lock'])
            prefix = subprocess.check_output([str(wrapper),'--print-prefix'],text=True).strip()
            assert Path(prefix)==wrapper.parent.parent
            assert subprocess.run([str(Path(prefix)/'bin/leantar'),'--help']).returncode==0
            passed.append('overlay-prefix-selects-bounded-original-leantar')
            # A zero time budget processes one visited entry per call. The
            # cursor must eventually reach every file rather than restart.
            cache = root/'source/.lake/build'; cache.mkdir(parents=True)
            for n in range(8):
                p = cache/str(n); p.write_bytes(b'fixture')
                os.utime(p,(time.time()-3,time.time()-3))
            replay.guard.last['memory_current'] = 2*2**30
            replay.config['workspace'] = str(root)
            for _ in range(12):
                replay.release_own_clean_cache(budget=0)
            assert replay.cache_advice['files']==8
            passed.append('cache-advice-cursor-progresses-past-earlier-files')
            # A small cap exercises native advice eligibility through eviction.
            # The production-sized allocation comparison is retained separately.
            limit = runner.CACHE_ADVICE_MEMO_LIMIT
            assert limit == 8192
            historical = replay.recent_input_mappings
            historical[str(cache/'0')] = True
            historical_before = dict(historical)
            try:
                runner.CACHE_ADVICE_MEMO_LIMIT = 3
                replay.cache_advised.clear()
                replay.cache_advice['maximum_memo_entries'] = 0
                replay.cache_iterator = iter(cache/str(n) for n in range(4))
                for _ in range(4):
                    replay.release_own_clean_cache(budget=0)
                    assert len(replay.cache_advised) <= 3
                assert str(cache/'0') not in replay.cache_advised
                assert replay.cache_advice['memo_evictions'] == 1
                calls = replay.cache_advice['files']
                replay.cache_iterator = iter([cache/'2'])
                replay.release_own_clean_cache(budget=0)
                assert replay.cache_advice['files'] == calls
                (cache/'2').write_bytes(b'changed-fixture')
                os.utime(cache/'2', (time.time()-3, time.time()-3))
                for target in (cache/'2', cache/'0', cache/'4'):
                    replay.cache_iterator = iter([target])
                    replay.release_own_clean_cache(budget=0)
                    calls += 1
                    assert replay.cache_advice['files'] == calls
                    assert len(replay.cache_advised) <= 3
                assert replay.recent_input_mappings is historical
                assert dict(historical) == historical_before
                assert replay.cache_advice['maximum_memo_entries'] == 3
                assert (cache/'2').read_bytes() == b'changed-fixture'
            finally:
                runner.CACHE_ADVICE_MEMO_LIMIT = limit
                replay.cache_advised.clear()
                replay.cache_iterator = None
            passed.extend(['bounded-FIFO-memo-preserves-cursor-and-H-custody',
                'memo-eviction-and-changed-unseen-files-remain-eligible-for-native-advice'])
            (root/'source/Basic.lean').write_bytes(b'import Mathlib\r\n')
            (root/'source/Named.lean').write_bytes(b'import Mathlib.Data.Nat.Basic Mathlib.Data.Int.Basic -- comment\n')
            (root/'source/.lake/Generated.lean').write_bytes(b'import Mathlib.NotSource\n')
            assert runner.cache_module_scope(root/'source')=={
                'Mathlib','Mathlib.Data.Nat.Basic','Mathlib.Data.Int.Basic'}
            passed.append('cache-scope-includes-bare-Mathlib-CRLF-and-multiple-imports')
        with tempfile.TemporaryDirectory(prefix='decompress-fixture-', dir=workspace) as directory:
            root = Path(directory); cache=root/'cache'; cache.mkdir()
            output=root/'source/.lake/build'; output.mkdir(parents=True)
            actual=root/'native-fixture'
            actual.write_text('#!/usr/bin/python3\nimport sys,json,pathlib\n'
                'assert sys.argv[1:]==["--jobs","1","-x","--delete-corrupted","-j","-"]\n'
                'for record in json.load(sys.stdin):\n'
                ' p=pathlib.Path(record["file"])\n'
                ' if p.read_bytes()==b"fail": sys.exit(7)\n'
                ' (pathlib.Path(record["base"])/(p.name+".out")).write_bytes(p.read_bytes())\n')
            actual.chmod(0o700)
            config={'workspace':str(root),'run':str(root)}
            records=[]
            for n in range(4):
                p=cache/str(n); p.write_bytes(bytes([n])*1024)
                records.append({'file':str(p),'base':str(output)})
            fixture_observation=copy.deepcopy(current);fixture_observation['memory_current']=2**30
            def reader(): return copy.deepcopy(fixture_observation)
            args=['-x','--delete-corrupted','-j','-']
            runner.bounded_decompress(actual,config,args,io.StringIO(json.dumps(records)),batch_size=2,reader=reader)
            for record in records:
                p=Path(record['file']);assert (output/(p.name+'.out')).read_bytes()==p.read_bytes()
            log=root/('leantar-batches-'+str(os.getpid())+'.jsonl')
            rows=[json.loads(line) for line in log.read_text().splitlines()]
            batches=[row for row in rows if row['kind']=='batch-completed']
            assert len(batches)==2 and all(row['count']==2 for row in batches)
            passed.append('bounded-native-protocol-batches-preserve-output-bytes')
            (cache/'0').write_bytes(b'fail')
            try:
                runner.bounded_decompress(actual,config,args,io.StringIO(json.dumps(records)),batch_size=2,reader=reader)
            except RuntimeError as exc:
                assert 'Native decompressor failed: exit 7' in str(exc)
            else: raise AssertionError('Native decompressor failure was swallowed')
            passed.append('bounded-native-decompressor-failure-propagates')
            inputs=root/'inventory-input'; (inputs/'a').mkdir(parents=True)
            (inputs/'a/first').write_bytes(b'a');(inputs/'a.txt').write_bytes(b'b')
            (inputs/'z').write_bytes(b'c')
            expected={'files':[{'path':p.relative_to(inputs).as_posix(),'sha256':runner.digest(p),
                'bytes':p.stat().st_size} for p in sorted(inputs.rglob('*')) if p.is_file()]}
            inventory=root/'fixture-inventory.json'
            runner.write_inventory(inputs,inventory,'all')
            assert inventory.read_bytes()==(json.dumps(expected,indent=2)+'\n').encode()
            passed.append('streamed-inventory-preserves-legacy-byte-identity')
        with tempfile.TemporaryDirectory(prefix='mapped-input-fixture-', dir=workspace) as directory:
            root = Path(directory)
            path = root/'immutable.olean'
            size = 32*2**20
            with path.open('wb') as stream:
                for _ in range(32):
                    stream.write(b'K'*2**20)
                stream.flush(); os.fsync(stream.fileno())
            original_hash = runner.digest(path)
            original_stat = path.stat()
            libc = ctypes.CDLL(None, use_errno=True)
            libc.mincore.argtypes = [ctypes.c_void_p, ctypes.c_size_t, ctypes.c_void_p]
            libc.mincore.restype = ctypes.c_int
            counts = []
            with path.open('rb') as stream, mmap.mmap(stream.fileno(), 0, access=mmap.ACCESS_COPY) as mapped:
                mapped[0] = ord('Z')
                def resident_pages():
                    address = ctypes.addressof(ctypes.c_char.from_buffer(mapped))
                    vector = (ctypes.c_ubyte*(size//mmap.PAGESIZE))()
                    assert libc.mincore(address, size, vector)==0
                    return sum(value & 1 for value in vector)
                def warm_closed_input():
                    with path.open('rb') as source:
                        while source.read(2**20):
                            pass
                run = root/'fixture-run'; run.mkdir()
                replay = runner.Replay({'workspace':str(root)}, run, runner.Guard(run))
                replay.immutable_input_roots = [root]
                replay.active_pgid = os.getpgid(os.getpid())
                replay.guard.last['compiler_processes'] = [
                    {'pid':os.getpid(), 'uid':os.getuid(), 'comm':'lean'}]
                for _ in range(2):
                    warm_closed_input()
                    before = resident_pages()
                    replay.release_import_readahead(budget=2.0)
                    after = resident_pages()
                    assert before >= 8000 and after < 256, (before, after)
                    assert mapped[0]==ord('Z') and mapped[-1]==ord('K')
                    counts.append({'before_resident_pages':before,'after_resident_pages':after})
                assert replay.input_cache_advice['calls'] >= 2
                assert replay.input_cache_advice['maximum_recent_files']==1
            assert runner.digest(path)==original_hash
            assert (path.stat().st_size, path.stat().st_mtime_ns)==(original_stat.st_size, original_stat.st_mtime_ns)
            try:
                runner.advise_immutable_input(path, [root/'outside'])
            except RuntimeError as exc:
                assert 'escapes verified inputs' in str(exc)
            else: raise AssertionError('Unverified input advice accepted')
            passed.extend(['mapped-input-advice-preserves-mapped-COW-and-file-bytes',
                'unchanged-input-read-ahead-is-reclaimed-repeatedly',
                'input-advice-rejects-unverified-root'])
            print(json.dumps({'mapped_input_residency_fixture':counts,'file_sha256':original_hash}))
        with tempfile.TemporaryDirectory(prefix='mapping-scale-fixture-', dir=workspace) as directory:
            root=Path(directory);run=root/'fixture-run';run.mkdir()
            guard=runner.Guard(run)
            replay=runner.Replay({'workspace':str(root)},run,guard)
            replay.immutable_input_roots=[root]
            replay.active_pgid=os.getpgid(os.getpid())
            cold=root/'seed.olean';cold.write_bytes(b'C'*mmap.PAGESIZE)
            with cold.open('rb') as stream:os.fsync(stream.fileno())
            hot=root/'hot.olean'
            with hot.open('wb') as stream:
                for _ in range(32):stream.write(b'K'*2**20)
                stream.flush();os.fsync(stream.fileno())
            hot_hash=runner.digest(hot)
            mappings=[];hot_map=None;original_advice=runner.advise_immutable_input
            started=time.monotonic();refaults=[];progress_during_discovery=0
            try:
                for index in range(50000):
                    path=root/f'cold-{index:05d}.olean'
                    os.link(cold,path)
                    fd=os.open(path,os.O_RDONLY)
                    try:mappings.append(mmap.mmap(fd,mmap.PAGESIZE,access=mmap.ACCESS_READ,trackfd=False))
                    finally:os.close(fd)
                    if index%1024==0:guard.check()
                fd=os.open(hot,os.O_RDONLY)
                try:hot_map=mmap.mmap(fd,0,access=mmap.ACCESS_COPY,trackfd=False)
                finally:os.close(fd)
                hot_map[0]=ord('Z')
                def resident_hot():
                    address=ctypes.addressof(ctypes.c_char.from_buffer(hot_map))
                    vector=(ctypes.c_ubyte*(len(hot_map)//mmap.PAGESIZE))()
                    assert libc.mincore(address,len(hot_map),vector)==0
                    return sum(value&1 for value in vector)
                def measured_advice(path,roots):
                    if Path(path)==hot:
                        with hot.open('rb') as stream:
                            while stream.read(2**20):pass
                        before=resident_hot()
                        result=original_advice(path,roots)
                        after=resident_hot()
                        assert before>=8000 and after<256,(before,after)
                        assert hot_map[0]==ord('Z')
                        refaults.append({'before_pages':before,'after_pages':after})
                        return result
                    return original_advice(path,roots)
                runner.advise_immutable_input=measured_advice
                deadline=time.monotonic()+120
                while True:
                    guard.check()
                    guard.last['compiler_processes']=[{'pid':os.getpid(),'uid':os.getuid(),'comm':'lean'}]
                    before=replay.input_cache_advice['calls']
                    replay.release_import_readahead()
                    if replay.mapping_iterator is not None and replay.input_cache_advice['calls']>before:
                        progress_during_discovery+=1
                    stats=replay.input_cache_advice
                    if (stats['maximum_recent_files']==50001 and stats['unadvised_files']==0
                            and stats['largest_completed_advice_round_files']>=50001 and len(refaults)>=2):
                        break
                    assert time.monotonic()<deadline,'Representative mapping advisor did not complete its input round'
                assert progress_during_discovery>0
                guard.check()
                print(json.dumps({'mapping_scale_fixture':{'native_mappings':50001,
                    'progress_calls_while_discovery_pending':progress_during_discovery,
                    'advice':stats,'repeated_native_hot_file_refaults':refaults,
                    'elapsed_seconds':time.monotonic()-started,
                    'maximum_guard_check_seconds':guard.maximum_check_seconds}}))
            finally:
                runner.advise_immutable_input=original_advice
                if replay.mapping_iterator is not None:replay.mapping_iterator.close()
                if hot_map is not None:hot_map.close()
                for mapped in mappings:mapped.close()
            assert runner.digest(hot)==hot_hash
            passed.append('50001-native-mappings-discovery-does-not-starve-complete-repeated-advice-rounds')
        with tempfile.TemporaryDirectory(prefix='qualified-read-fixture-', dir=workspace) as directory:
            root=Path(directory);inputs=root/'inputs';inputs.mkdir();run=root/'run';run.mkdir()
            hot=inputs/'z-hot.lean'
            with hot.open('wb') as stream:
                for _ in range(32):stream.write(b'R'*2**20)
                stream.flush();os.fsync(stream.fileno())
            hashes=[]
            for index in range(9000):
                path=inputs/f'b-{index:05d}.olean.hash'
                with path.open('wb') as stream:
                    stream.write(b'0123456789abcdef');stream.flush();os.fsync(stream.fileno())
                hashes.append(path)
            ignored=inputs/'a-seed.trace';ignored.write_bytes(b'not-qualified')
            for index in range(5000):os.link(ignored,inputs/f'a-{index:05d}.trace')
            inventory=root/'qualified-fixture.json';runner.write_inventory(inputs,inventory,'all')
            before_stat={p.name:(p.stat().st_size,p.stat().st_mtime_ns) for p in [hot,*hashes]}
            hot_hash=runner.digest(hot)
            guard=runner.Guard(run);replay=runner.Replay({'workspace':str(root)},run,guard)
            replay.qualified_read_inventories=[(inputs,inventory)]
            def resident(path):
                with path.open('rb') as stream,mmap.mmap(stream.fileno(),0,access=mmap.ACCESS_COPY) as mapped:
                    vector=(ctypes.c_ubyte*((len(mapped)+mmap.PAGESIZE-1)//mmap.PAGESIZE))()
                    address=ctypes.addressof(ctypes.c_char.from_buffer(mapped))
                    assert libc.mincore(address,len(mapped),vector)==0
                    return sum(value&1 for value in vector)
            cycles=[];started=time.monotonic()
            for cycle in range(2):
                for index,path in enumerate([hot,*hashes]):
                    with path.open('rb') as stream:
                        while stream.read(2**20):pass
                    if index%1024==0:guard.check()
                before={'source':resident(hot),'hash':sum(resident(p) for p in hashes)}
                assert before['source']>=8000 and before['hash']==9000
                replay.restart_read_advice_round();baseline=replay.read_cache_advice['rounds_completed']
                calls=0;round_started=time.monotonic()
                while replay.read_cache_advice['rounds_completed']==baseline:
                    guard.check();replay.release_qualified_read_cache(budget=0.02);calls+=1
                    assert time.monotonic()-round_started<90
                assert replay.read_cache_advice['last_round_files']==9001
                after={'source':resident(hot),'hash':sum(resident(p) for p in hashes)}
                assert after['source']==0 and after['hash']==0,(before,after)
                cycles.append({'before_pages':before,'after_pages':after,'bounded_calls':calls,
                    'round_seconds':time.monotonic()-round_started})
            assert replay.read_cache_advice['records_scanned']==2*14002
            assert replay.read_cache_advice['maximum_call_seconds']<0.25
            assert runner.digest(hot)==hot_hash
            assert all(p.read_bytes()==b'0123456789abcdef' for p in hashes)
            assert before_stat=={p.name:(p.stat().st_size,p.stat().st_mtime_ns) for p in [hot,*hashes]}
            print(json.dumps({'qualified_read_fixture':{'files':9001,'skipped_unqualified_per_round':5001,
                'cycles':cycles,'advice':replay.read_cache_advice,'elapsed_seconds':time.monotonic()-started}}))
            passed.extend(['qualified-read-advice-streams-bounded-records-and-skips-unqualified-metadata',
                '9001-unchanged-ordinary-read-inputs-refault-and-reclaim-on-two-complete-rounds'])
        admission = {'source_commit':'fixture-source', 'toolchain_inventory_sha256':'fixture-toolchain',
                     'dependency_source_root':'fixture-dependencies'}
        receipt = {'schema':'jw-compiler-result-v1','purpose':'isolated-module-diagnostic',
            'status':'completed','exit_code':0,'build_targets':['ExoticCCR.Basic'],
            'stages':{'build':{'exit_code':0}}}
        scope = runner.artifact_reuse_scope(receipt, admission, admission)
        assert scope['kind']=='bounded-module-build-only' and scope['certification'] is False
        for mutate in [lambda r:r.update(status='failed',exit_code=1),
                       lambda r:r['stages']['build'].update(exit_code=-15)]:
            bad = copy.deepcopy(receipt);mutate(bad)
            try: runner.artifact_reuse_scope(bad,admission,admission)
            except RuntimeError: pass
            else: raise AssertionError('Failed bounded artifact receipt accepted')
        different = dict(admission,toolchain_inventory_sha256='wrong-toolchain')
        try: runner.artifact_reuse_scope(receipt,admission,different)
        except RuntimeError: pass
        else: raise AssertionError('Changed artifact compiler pin accepted')
        passed.append('bounded-artifact-reuse-preserves-success-scope-and-rejects-failure-or-pin-change')
        with tempfile.TemporaryDirectory(prefix='module-order-fixture-', dir=workspace) as directory:
            root=Path(directory);(root/'ExoticCCR').mkdir()
            (root/'lakefile.toml').write_text('defaultTargets=["ExoticCCR"]\n[[lean_lib]]\nname="ExoticCCR"\n')
            (root/'ExoticCCR.lean').write_text('import ExoticCCR.B\r\nimport ExoticCCR.A\r\n')
            (root/'ExoticCCR/A.lean').write_text('import Mathlib\n')
            (root/'ExoticCCR/B.lean').write_text('import ExoticCCR.A\n')
            (root/'ExoticCCR/Unimported.lean').write_text('import Mathlib\n')
            assert runner.project_build_order(root)==['ExoticCCR.A','ExoticCCR.B','ExoticCCR']
            (root/'ExoticCCR/A.lean').write_text('import ExoticCCR.B\n')
            try:runner.project_build_order(root)
            except RuntimeError:pass
            else:raise AssertionError('Cyclic project warmup plan accepted')
            passed.append('sequential-plan-follows-exact-default-root-closure-and-rejects-cycle')
        with tempfile.TemporaryDirectory(prefix='flow-byte-fixture-', dir=workspace) as directory:
            root=Path(directory);inputs=root/'inputs';inputs.mkdir();run=root/'run';run.mkdir()
            for index in range(12):
                path=inputs/f'{index:02d}.olean'
                with path.open('wb') as stream:
                    for _ in range(8):stream.write(bytes([index])*2**20)
                    stream.flush();os.fsync(stream.fileno())
                    os.posix_fadvise(stream.fileno(),0,0,os.POSIX_FADV_DONTNEED)
            pins={p.name:runner.digest(p) for p in inputs.iterdir()}
            helper=root/'arrival.py'
            helper.write_text('import ctypes,mmap,os,pathlib,time\n'
                'ctypes.CDLL(None).prctl(15,b"lean",0,0,0)\n'
                'root=pathlib.Path('+repr(str(inputs))+')\n'
                'maps=[]\n'
                'for cycle in range(2):\n'
                ' for p in sorted(root.iterdir()):\n'
                '  with p.open("rb") as f:\n'
                '   if cycle==0:\n'
                '    m=mmap.mmap(f.fileno(),0,access=mmap.ACCESS_COPY,trackfd=False);maps.append(m);assert m[0]==int(p.stem)\n'
                '   while f.read(2**20):pass\n'
                '  time.sleep(0.08)\n'
                'time.sleep(0.5)\n'
                'for m in maps:m.close()\n')
            guard=runner.Guard(run)
            assert int(runner.LIMITS['memory.high'])-guard.last['memory_current']>192*2**20
            replay=runner.Replay({'workspace':str(root),'flow_control':True},run,guard)
            replay.immutable_input_roots=[inputs]
            baseline=guard.last['memory_current']
            replay.flow_trigger=baseline+48*2**20
            replay.flow_resume=baseline+24*2**20
            replay.flow_pause_timeout=30
            replay.stage('build',['python3',str(helper)])
            assert replay.flow_summary['pauses']>=1
            events=[json.loads(line) for line in (run/'flow-control.jsonl').read_text().splitlines()]
            assert any(row['kind']=='resumed' for row in events)
            assert not any(row['kind']=='terminated-during-pause' for row in events)
            for p in inputs.iterdir():assert runner.digest(p)==pins[p.name]
            assert not runner.compiler_processes()
            print(json.dumps({'flow_real_byte_fixture':{'distinct_inputs':12,'input_bytes':96*2**20,
                'read_cycles':2,'test_trigger_bytes':replay.flow_trigger,'test_resume_bytes':replay.flow_resume,
                'pauses':replay.flow_summary['pauses'],'pause_seconds':replay.flow_summary['total_pause_seconds'],
                'maximum_guard_interval_seconds':replay.stages['build']['maximum_live_guard_interval_seconds'],
                'native_build_exit':replay.stages['build']['exit_code'],
                'events_before':guard.baseline['events'],'events_after':guard.last['events']}}))
            passed.append('real-distinct-file-arrival-flow-control-pauses-drains-resumes-with-unchanged-bytes')
        with tempfile.TemporaryDirectory(prefix='flow-cleanup-fixture-', dir=workspace) as directory:
            root=Path(directory)
            sentinel=subprocess.Popen(['python3','-c','import time;time.sleep(90)'],start_new_session=True)
            runner.capture_stage_identity(sentinel)
            try:
                for case in ('exception','guard','interrupt','capacity',
                             'signal-return-interrupt','pre-signal-failure','esrch-before-stop'):
                    run=root/case;run.mkdir();ready=run/'ready'
                    (run/'input.olean').write_bytes(b'K'*4096)
                    helper=run/'family.py'
                    helper.write_text('import ctypes,mmap,pathlib,subprocess,time\n'
                        'ctypes.CDLL(None).prctl(15,b"lean",0,0,0)\n'
                        'f=open('+repr(str(run/'input.olean'))+',"rb");m=mmap.mmap(f.fileno(),0,access=mmap.ACCESS_COPY);assert m[0]==75\n'
                        'p=subprocess.Popen(["python3","-c","import time;time.sleep(90)"])\n'
                        'pathlib.Path('+repr(str(ready))+').write_text(str(p.pid))\n'
                        'time.sleep(90)\n')
                    process=subprocess.Popen(['python3',str(helper)],start_new_session=True)
                    identity=runner.capture_stage_identity(process)
                    deadline=time.monotonic()+3
                    while not ready.exists():
                        assert time.monotonic()<deadline
                        time.sleep(0.01)
                    guard=runner.Guard(run)
                    replay=runner.Replay({'workspace':str(root),'flow_control':True},run,guard)
                    replay.immutable_input_roots=[root]
                    replay.active_pgid=process.pid
                    replay.flow_trigger=1
                    if case=='capacity':replay.flow_resume=1  # Deliberately unreachable test-only headroom.
                    original_record=replay.flow_record
                    def inject(kind,**extra):
                        original_record(kind,**extra)
                        if kind!='paused':return
                        if case in ('capacity','signal-return-interrupt','pre-signal-failure','esrch-before-stop'):return
                        if case=='interrupt':raise KeyboardInterrupt('fixture interrupt while stopped')
                        if case=='guard':
                            native_reader=guard.reader
                            def fail_closed():
                                value=native_reader();value['root_available_bytes']=runner.MIN_FREE-1;return value
                            guard.reader=fail_closed
                            guard.check()
                        raise RuntimeError('fixture exception while stopped')
                    replay.flow_record=inject
                    native_killpg=os.killpg
                    def signal_boundary(pgid,signum):
                        if signum==runner.signal.SIGSTOP:
                            if case=='pre-signal-failure':
                                raise OSError('fixture failure before sending SIGSTOP')
                            if case=='esrch-before-stop':
                                native_killpg(pgid,runner.signal.SIGTERM)
                                native_killpg(pgid,runner.signal.SIGCONT)
                                process.wait(timeout=3)
                                until=time.monotonic()+3
                                while any(row['state']!='Z' for row in runner.owned_group_members(identity)):
                                    assert time.monotonic()<until;time.sleep(0.01)
                                raise ProcessLookupError('fixture group completed before SIGSTOP')
                            native_killpg(pgid,signum)
                            if case=='signal-return-interrupt':
                                raise KeyboardInterrupt('fixture interrupt immediately after SIGSTOP syscall')
                            return
                        return native_killpg(pgid,signum)
                    try:
                        runner.os.killpg=signal_boundary
                        try:
                            replay.maybe_flow_control(process,guard.check)
                        except (RuntimeError,KeyboardInterrupt,OSError) as exc:
                            assert case!='esrch-before-stop'
                            if case=='capacity':assert 'Flow-control capacity:' in str(exc)
                        else:
                            assert case=='esrch-before-stop','Stopped-group cleanup fixture did not interrupt'
                        assert process.poll() is not None
                        assert not any(row['state']!='Z' for row in runner.owned_group_members(identity))
                        assert sentinel.poll() is None
                        assert runner.process_identity(sentinel.pid)['state'] not in ('T','t')
                        events=[json.loads(line) for line in (run/'flow-control.jsonl').read_text().splitlines()]
                        request=next(row for row in events if row['kind']=='pause-requested')
                        assert len(request['members'])>=2
                        expected='stage-completed-before-pause' if case=='esrch-before-stop' else 'terminated-during-pause'
                        assert any(row['kind']==expected for row in events)
                    finally:
                        runner.os.killpg=native_killpg
                        # A regression in the behavior under test must not
                        # leave its own stopped fixture family behind.
                        if any(row['state']!='Z' for row in runner.owned_group_members(identity)):
                            runner.terminate_owned(process)
                bad=copy.deepcopy(sentinel.jw_identity)
                bad['leader_start_ticks']=str(int(bad['leader_start_ticks'])+1)
                try:runner.owned_group_members(bad)
                except RuntimeError:pass
                else:raise AssertionError('Wrong process birth identity accepted')
                assert sentinel.poll() is None
            finally:runner.terminate_owned(sentinel)
            passed.extend(['flow-exception-guard-interrupt-cleanup-leaves-no-stopped-descendants',
                'flow-control-rejects-wrong-birth-and-preserves-other-owned-group',
                'completed-paused-input-drain-without-required-headroom-terminates-without-retry',
                'signal-return-interrupt-pre-signal-failure-and-ESRCH-preserve-owned-cleanup'])
        passed.extend(normal_flow_checkpoint_fixture(workspace))
        passed.extend(epoch_fixture(workspace))
        passed.extend(epoch_fault_fixture(workspace))
        passed.extend(paused_completion_fixture(workspace))
        passed.extend(metadata_custody_fixture(workspace))
        passed.extend(epoch_fixture(workspace, scale=True))
        passed.extend(delegated_reclaim_fixture(workspace))
        passed.extend(pause_allocation_policy_fixture(workspace))
        passed.extend(pause_allocation_deadline_fixture(workspace))
    print(json.dumps({'status':'PASS','tests':passed,'no_lean_invoked':True}))


if __name__ == '__main__':
    if sys.argv[1:] == ['--deeper-profile-policy-fixture']:
        selected=deeper_profile_fixture()
        print(json.dumps({'status':'PASS','scope':'deeper-profile-policy-only',
            'tests':selected,'no_lean_invoked':True,'no_cgroup_reclaim_invoked':True,
            'eagain_measurement':'preserved native v04 receipt; no retry'}))
    elif sys.argv[1:] == ['--wider-interface-fixture']:
        runner.validate_observation(runner.observe())
        workspace=runner.ROOT/'jacobian-weyl-20261110'
        with runner.lease(runner.ROOT/'locks/host-compiler.lock'):
            assert not runner.compiler_processes()
            selected=wider_profile_fixture(workspace)+delegated_reclaim_fixture(workspace,wider=True,interface_sizing=True)
        print(json.dumps({'status':'PASS','scope':'focused-wider-interface-fixture',
            'tests':selected,'no_lean_invoked':True,'positive_sizing':'explicit-captured-v07-interface-only',
            'captured_policy_parent_bytes':3989532672,'computed_request_bytes':533426176,
            'minimum_actual_parent_leaf_mincore_relief_each_bytes':524288000,
            'actual_production_deficit_or_lean_fit_validated':False,
            'lineage':'Prior native15/22/75 unchanged paths reused; current profile/payload and affected lifecycle cases rerun. Forced fixture inputs are separately recorded; production runner unchanged.'}))
    elif sys.argv[1:] == ['--wider-profile-delta']:
        runner.validate_observation(runner.observe())
        workspace=runner.ROOT/'jacobian-weyl-20261110'
        with runner.lease(runner.ROOT/'locks/host-compiler.lock'):
            assert not runner.compiler_processes()
            selected=wider_profile_fixture(workspace)+delegated_reclaim_fixture(workspace,wider=True)
        print(json.dumps({'status':'PASS','scope':'focused-wider-refill-profile-delta',
            'tests':selected,'no_lean_invoked':True,'positive_sizing':'actual-parent-deficit-only',
            'lineage':'Prior native15 allocation/deadline,22 deficit/leaf/lifecycle and75 unchanged59/131601 evidence reused explicitly; current profile/payload and affected native lifecycle cases rerun.'}))
    elif sys.argv[1:] == ['--pause-allocation-delta']:
        runner.validate_observation(runner.observe())
        workspace = runner.ROOT/'jacobian-weyl-20261110'
        with runner.lease(runner.ROOT/'locks/host-compiler.lock'):
            assert not runner.compiler_processes()
            selected = pause_allocation_policy_fixture(workspace)+pause_allocation_deadline_fixture(workspace)
        print(json.dumps({'status': 'PASS', 'scope': 'focused-pause-allocation-delta',
            'tests': selected, 'no_lean_invoked': True, 'no_cgroup_reclaim_invoked': True,
            'lineage': 'Prior native22 current deficit policy and native75 unchanged ownership/epoch paths reused; this gate exercises only selected allocation and deadline intersections.'}))
    elif sys.argv[1:] == ['--reclaim-policy-delta']:
        runner.validate_observation(runner.observe())
        with runner.lease(runner.ROOT/'locks/host-compiler.lock'):
            assert not runner.compiler_processes()
            selected = deficit_policy_fixture()+delegated_reclaim_fixture(runner.ROOT/'jacobian-weyl-20261110')
        print(json.dumps({'status':'PASS','scope':'focused-deficit-reclaim-delta',
            'tests':selected,'no_lean_invoked':True,'lineage':'Prior native75 terminal d3f374abbf2128af8841c0c97b9d16d92d1b59761a1c7724aebe4ba0a165a50b; unchanged original59 and131601 epoch paths reused, affected delegated cases rerun'}))
    elif sys.argv[1:] == ['--epoch-diagnostic']:
        runner.validate_observation(runner.observe())
        workspace=runner.ROOT/'jacobian-weyl-20261110'
        with runner.lease(runner.ROOT/'locks/host-compiler.lock'):
            assert not runner.compiler_processes()
            selected=epoch_fault_fixture(workspace)+paused_completion_fixture(workspace)+metadata_custody_fixture(workspace)
            print(json.dumps({'focused_boundary_fault_tests':'PASS','tests':selected}),flush=True)
            selected+=epoch_fixture(workspace,scale=True)
        print(json.dumps({'status':'PASS','scope':'focused-epoch-diagnostic','tests':selected,'no_lean_invoked':True}))
    else:
        assert not sys.argv[1:]
        main()
