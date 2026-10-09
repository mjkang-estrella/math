"""Author-side sealing; reviewers run verify.py, not this script."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[3]
S = ROOT / 'frontier/sources/i36_harmonic_analysis_discovery'
X = ROOT / 'frontier/experiments/i36_harmonic_analysis_discovery'
excluded = {S / 'artifact-seal.json', X / 'verification.json'}
files = [ROOT / 'frontier/iterations/i36-harmonic-analysis-discovery.md']
files += [p for directory in (S, X) for p in directory.rglob('*')
          if p.is_file() and p not in excluded and '__pycache__' not in p.parts]
rows = []
for p in sorted(files):
    b = p.read_bytes()
    rows.append({'path': str(p.relative_to(ROOT)), 'bytes': len(b),
                 'sha256': hashlib.sha256(b).hexdigest()})
seal = {'scope': 'I36 report and owned evidence; excludes this seal and verifier output.',
        'pin': 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb', 'files': rows}
(S / 'artifact-seal.json').write_text(json.dumps(seal, indent=2) + '\n')
print(json.dumps({'sealed_files': len(rows)}))
