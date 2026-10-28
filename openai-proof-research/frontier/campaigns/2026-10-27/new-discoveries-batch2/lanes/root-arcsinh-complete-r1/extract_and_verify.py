#!/usr/bin/env python3
"""Check a fresh archive extraction and invoke its actual source verifier."""
from pathlib import Path
import hashlib, json, shutil, subprocess, tempfile, zipfile

base = Path(__file__).resolve().parent
archive = base / 'packet/arcsinh-positive-paper-proof.zip'
receipt = json.loads((archive.parent / 'archive.json').read_text())
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(archive) == receipt['sha256']
out = base / 'extracted-replay'
out.mkdir(exist_ok=True)
with tempfile.TemporaryDirectory(prefix='arcsinh-review-extracted-') as tmp:
    tmp = Path(tmp)
    with zipfile.ZipFile(archive) as z:
        for info in z.infolist():
            assert not info.filename.startswith('/') and '..' not in Path(info.filename).parts
        z.extractall(tmp)
    candidate = tmp / 'arcsinh-positive'
    assert sha(candidate / 'MANIFEST.json') == receipt['manifest_sha256']
    manifest = json.loads((candidate / 'MANIFEST.json').read_text())
    for name, expected in manifest.items():
        assert sha(candidate / name) == expected, name
    result = subprocess.run(['python3', 'verify_candidate.py'], cwd=candidate,
        capture_output=True, text=True)
    (out / 'run.log').write_text(result.stdout + result.stderr)
    assert result.returncode == 0, (result.returncode, result.stdout, result.stderr)
    for p in (candidate / 'verification').iterdir():
        shutil.copy2(p, out / p.name)
    # The compiler produces logs, never edits the proof sources or paper.
    for name, expected in manifest.items():
        if not name.startswith('verification/'):
            assert sha(candidate / name) == expected, name
    audit = json.loads((out / 'audit.json').read_text())
    assert audit['declarations'] == 19 and audit['modules'] == 5
    report = {'status': 'PASS fresh extracted strict replay; acceptance pending',
        'archive_sha256': sha(archive), 'files_verified': len(manifest),
        'declarations': 19, 'modules': 5, 'audit_sha256': sha(out / 'audit.json'),
        'checks_sha256': sha(out / 'Checks.log'), 'original_receipt_identical':
            (out / 'audit.json').read_bytes() == (base / 'candidate/verification/audit.json').read_bytes()}
    (out / 'extracted-receipt.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))
