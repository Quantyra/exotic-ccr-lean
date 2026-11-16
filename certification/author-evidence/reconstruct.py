"""Reconstruct the initially frozen author candidates without running Lean.

Only writes .lean.txt artifacts into a new output directory. The repository's
Lean source files are never written. No network, credentials, or compiler use.
"""
from pathlib import Path
import argparse
import hashlib
import json

parser = argparse.ArgumentParser()
parser.add_argument('--output-dir', required=True)
args = parser.parse_args()
base = Path(__file__).resolve().parent
output = Path(args.output_dir).resolve()
assert not output.exists(), 'Use a new output directory'
rendering = base / 'rendering'
provenance = json.loads((rendering / 'provenance.json').read_text(encoding='utf8'))
candidate_r2 = (rendering / 'unitary-corrected.lean.txt').read_bytes()
candidate_r3 = (rendering / 'symmetry-stage.lean.txt').read_text(encoding='utf8')
for filename in ['core-append.lean.txt', 'operators-append.lean.txt']:
    append = (rendering / filename).read_text(encoding='utf8')
    assert candidate_r3.count('\nend ExoticCCR') == 1
    candidate_r3 = candidate_r3.replace('\nend ExoticCCR', append + '\nend ExoticCCR')
payloads = {
    'ExoticCCR/TheoremFContinuum.lean': candidate_r2,
    'ExoticCCR/TheoremCAnalytic.lean': candidate_r3.encode('utf8'),
}
for filename, data in payloads.items():
    assert hashlib.sha256(data).hexdigest() == provenance['candidate_hashes'][filename], filename
output.mkdir()
for filename, data in payloads.items():
    (output / (Path(filename).name + '.txt')).write_bytes(data)
print(json.dumps({'reconstructed': provenance['candidate_hashes'], 'compiled': False}, indent=2))
