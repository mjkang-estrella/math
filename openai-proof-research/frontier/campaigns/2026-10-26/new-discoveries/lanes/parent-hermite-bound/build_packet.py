#!/usr/bin/env python3
"""Build the reviewed Hermite packet and verify an empty extraction destination."""
from pathlib import Path
import hashlib
import io
import json
import zipfile

ROOT = Path(__file__).resolve().parents[2]
CANDIDATE = ROOT / 'candidates/hermite'
PACKET = ROOT / 'candidate-packets/346243-hermite-envelope-proof.zip'
EXTRACT = ROOT / 'build/hermite-packet-audit-v1'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def archive_bytes(payload):
    out = io.BytesIO()
    with zipfile.ZipFile(out, 'w', zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for name, data in sorted(payload.items()):
            info = zipfile.ZipInfo('hermite/' + name, (2026, 10, 27, 0, 0, 0))
            info.external_attr = 0o100644 << 16
            archive.writestr(info, data, compress_type=zipfile.ZIP_DEFLATED,
                             compresslevel=9)
    return out.getvalue()


def main():
    frozen = json.loads((CANDIDATE / 'reviewed-parent-hashes.json').read_text())
    locations = json.loads((CANDIDATE / 'reviewed-file-locations.json').read_text())
    assert len(frozen) == 105 and set(frozen) == set(locations)
    for name, digest in frozen.items():
        assert sha((CANDIDATE / locations[name]).read_bytes()) == digest, name
    assert (CANDIDATE / 'verification/parent-audit.json').read_bytes() == (
        CANDIDATE / 'verification/independent-audit.json').read_bytes()
    audit = json.loads((CANDIDATE / 'verification/parent-audit.json').read_text())
    assert audit['status'] == 'PASS' and audit['declarations'] == 162
    assert len(audit['modules']) == 17
    for item in audit['modules']:
        assert sha((CANDIDATE / item['path']).read_bytes()) == item['sha256']
    qa = json.loads((CANDIDATE / 'paper-qa.json').read_text())
    assert qa['pages'] == 3 and qa['build_issues'] == []
    assert sha((CANDIDATE / 'main.tex').read_bytes()) == qa['tex_sha256']
    assert sha((CANDIDATE / 'paper.pdf').read_bytes()) == qa['pdf_sha256']
    names = []
    for path in sorted(CANDIDATE.rglob('*')):
        if not path.is_file():
            continue
        name = path.relative_to(CANDIDATE)
        if name.parts[0] == 'build' or '__pycache__' in name.parts:
            continue
        if str(name) in ['acceptance.json', 'MANIFEST.json']:
            continue
        assert path.suffix not in ['.olean', '.ilean', '.pyc'], name
        names.append(str(name))
    payload = {name: (CANDIDATE / name).read_bytes() for name in names}
    manifest = {name: sha(data) for name, data in payload.items()}
    payload['MANIFEST.json'] = (json.dumps(manifest, indent=2) + '\n').encode()
    data = archive_bytes(payload)
    assert data == archive_bytes(payload), 'Deterministic rebuild mismatch'
    assert not EXTRACT.exists(), 'Use a new empty extraction destination'
    assert not PACKET.exists(), 'Do not overwrite an existing packet'
    PACKET.parent.mkdir(exist_ok=True)
    PACKET.write_bytes(data)
    with zipfile.ZipFile(PACKET) as archive:
        assert archive.testzip() is None
        assert sorted(archive.namelist()) == sorted('hermite/' + n for n in payload)
        for name, value in payload.items():
            assert archive.read('hermite/' + name) == value, name
        archive.extractall(EXTRACT)
    extracted = EXTRACT / 'hermite'
    assert json.loads((extracted / 'MANIFEST.json').read_text()) == manifest
    for name, digest in manifest.items():
        assert sha((extracted / name).read_bytes()) == digest, name
    result = {'status': 'PASS: deterministic archive/readback/manifest; Lean replay pending',
              'packet': str(PACKET.relative_to(ROOT)), 'sha256': sha(data),
              'members': len(payload), 'extracted': str(extracted)}
    (EXTRACT / 'readback.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
