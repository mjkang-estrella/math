"""Check artifact integrity and finite algebra; not a mathematical proof verifier."""
from pathlib import Path
import hashlib
import json
import shutil
import subprocess
import tempfile

root = Path(__file__).resolve().parent
manifest = json.loads((root / 'outputs.json').read_text())
repository = root.parents[3]
input_status = 'not available outside original repository'
if (repository / 'AGENTS.md').exists():
    inputs = json.loads((root / 'inputs.json').read_text())
    for record in inputs:
        path = repository / record['path']
        data = path.read_bytes()
        assert len(data) == record['bytes'], str(path)
        assert hashlib.sha256(data).hexdigest() == record['sha256'], str(path)
    input_status = f'PASS: {len(inputs)} inputs'
for record in manifest['files']:
    path = root / record['path']
    data = path.read_bytes()
    assert len(data) == record['bytes'], str(path)
    assert hashlib.sha256(data).hexdigest() == record['sha256'], str(path)
with tempfile.TemporaryDirectory(prefix='ball-slab-verify-') as directory:
    script = Path(directory) / 'checks.py'
    shutil.copy2(root / 'checks/checks.py', script)
    subprocess.run(['python3', str(script)], check=True, capture_output=True)
    assert script.with_suffix('.json').read_bytes() == (root / 'checks/checks.json').read_bytes()
log = (root / 'output/pdf/main.log').read_text()
assert not any(word in log for word in ['Warning', 'Overfull', 'Underfull', 'undefined'])
assert len(list((root / 'qa').glob('page-*.png'))) == 9
print(json.dumps({'artifact_integrity': 'PASS', 'files': len(manifest['files']),
                  'source_inputs': input_status,
                  'exact_supporting_checks': 'PASS', 'mathematical_certificate': False}))
