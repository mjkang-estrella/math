"""Read-only final artifact authentication; not a mathematical proof checker.
Copyright (c) 2026 Myeongjin Kang. MIT License.
"""
from pathlib import Path
import hashlib, json

HERE = Path(__file__).resolve().parent
manifest = json.loads((HERE / 'outputs.json').read_text())
assert manifest['manifest_excludes_itself'] is True
expected = set()
for record in manifest['files']:
    rel = Path(record['path'])
    assert not rel.is_absolute() and '..' not in rel.parts
    assert rel.as_posix() not in expected, f'duplicate: {rel}'
    expected.add(rel.as_posix())
    data = (HERE / rel).read_bytes()
    assert len(data) == record['bytes'], f'length: {rel}'
    assert hashlib.sha256(data).hexdigest() == record['sha256'], f'SHA256: {rel}'
actual = {f.relative_to(HERE).as_posix() for f in HERE.rglob('*')
          if f.is_file() and f.name != 'outputs.json'
          and 'tmp' not in f.relative_to(HERE).parts
          and '__pycache__' not in f.relative_to(HERE).parts}
assert actual == expected, f'inventory mismatch: {actual ^ expected}'
print(json.dumps({'status': 'PASS for output bytes only',
                  'file_count': len(expected),
                  'mathematical_or_review_verdict': False}))
