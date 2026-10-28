#!/usr/bin/env python3
"""Build a deterministic review archive; this makes no acceptance decision."""
from pathlib import Path
import hashlib, json, zipfile

base = Path(__file__).resolve().parent
candidate = base / 'candidate'
files = sorted(p for p in candidate.rglob('*') if p.is_file() and p.name != 'MANIFEST.json')
assert all(p.suffix not in {'.olean', '.ilean'} for p in files)
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest = {str(p.relative_to(candidate)): sha(p) for p in files}
(candidate / 'MANIFEST.json').write_text(json.dumps(manifest, indent=2) + '\n')
files = sorted([*files, candidate / 'MANIFEST.json'])
out = base / 'packet'
out.mkdir(exist_ok=True)
archive = out / 'arcsinh-positive-paper-proof.zip'
with zipfile.ZipFile(archive, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as z:
    for p in files:
        info = zipfile.ZipInfo('arcsinh-positive/' + p.relative_to(candidate).as_posix(),
            date_time=(2026, 10, 28, 0, 0, 0))
        info.create_system = 3
        info.external_attr = 0o100644 << 16
        info.compress_type = zipfile.ZIP_DEFLATED
        z.writestr(info, p.read_bytes(), compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)
receipt = {'status': 'review archive only; no acceptance', 'files': len(files),
    'archive': archive.name, 'sha256': sha(archive), 'manifest_sha256': sha(candidate / 'MANIFEST.json'),
    'fixed_zip_timestamp': '2026-10-28T00:00:00', 'candidate_oleans_included': False}
(out / 'archive.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt, indent=2))
