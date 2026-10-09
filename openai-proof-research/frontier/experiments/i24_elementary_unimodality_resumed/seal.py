"""Explicit sealing command for the completed resumed scope only."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[3]
SOURCE = ROOT/'frontier/sources/i24_elementary_unimodality_resumed'
EXPERIMENT = ROOT/'frontier/experiments/i24_elementary_unimodality_resumed'
REPORT = ROOT/'frontier/iterations/i24-elementary-unimodality-resumed.md'
SEAL = EXPERIMENT/'artifact-seal.json'


def main():
    cp = json.loads((SOURCE/'inputs/frontier/experiments/i24-interrupted-checkpoint.json').read_text())
    for name, row in cp['files'].items():
        b = (ROOT/name).read_bytes()
        assert hashlib.sha256(b).hexdigest() == row['sha256'] and len(b) == row['bytes'], name
    files = {REPORT}
    for directory in (SOURCE, EXPERIMENT):
        files.update(p for p in directory.rglob('*') if p.is_file() and p != SEAL)
    rows = []
    for path in sorted(files):
        b = path.read_bytes()
        rows.append({'path': str(path.relative_to(ROOT)), 'bytes': len(b),
                     'sha256': hashlib.sha256(b).hexdigest()})
    payload = {'schema': 1, 'status': 'COMPLETED_SCOPED_GAP',
               'note': 'Seal excludes itself; inherited raw evidence is transitively bound by the frozen checkpoint and verified without rewriting.',
               'artifacts': rows}
    SEAL.write_text(json.dumps(payload, indent=2)+'\n')
    print(json.dumps({'sealed_artifacts': len(rows), 'inherited_files_unchanged': len(cp['files'])}))


if __name__ == '__main__':
    main()
