"""Authenticate frozen inputs; original review code, MIT, Myeongjin Kang."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[3]
FROZEN = HERE.parent / 'fresh-substantial-discovery-r2'
records = []
for name in ('input-manifest.json', 'output-manifest.json'):
    manifest = json.loads((FROZEN / name).read_text())
    for entry in manifest['files']:
        data = (FROZEN / entry['path']).read_bytes()
        actual = hashlib.sha256(data).hexdigest()
        record = {'manifest': name, 'path': entry['path'], 'bytes': len(data),
                  'sha256': actual, 'ok': len(data) == entry['bytes'] and actual == entry['sha256']}
        records.append(record)
        assert record['ok'], record
data = (FROZEN / 'candidate.md').read_bytes()
assert len(data) == 23029
assert hashlib.sha256(data).hexdigest() == '2a078a07142986c93845f4855496db14e41ee2590adc17720727b19145dd1c8b'
out = {'all_ok': True, 'entries_checked': len(records), 'records': records}
(HERE / 'checks/authentication.json').write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps({'all_ok': True, 'entries_checked': len(records)}))
