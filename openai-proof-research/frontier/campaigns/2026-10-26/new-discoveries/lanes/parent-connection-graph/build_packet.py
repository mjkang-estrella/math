#!/usr/bin/env python3
"""Deterministic exact-byte graph theorem packet; extracted Lean replay is separate."""
from pathlib import Path
import hashlib
import json
import zipfile

ROOT = Path(__file__).resolve().parents[2]
CANDIDATE = ROOT / 'candidates/connection-graph'
PACKET = ROOT / 'candidate-packets/2601-18071-connection-graph-proof.zip'
EXTRACT = ROOT / 'build/connection-graph-packet-audit-v1'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    frozen = json.loads((CANDIDATE / 'final-review-hashes.json').read_text())
    for name, digest in frozen.items():
        assert sha((CANDIDATE / name).read_bytes()) == digest, name
    assert (CANDIDATE / 'verification/parent-audit.json').read_bytes() == (
        CANDIDATE / 'verification/independent-audit.json').read_bytes()
    names = ['README.md', 'PROOF.md', 'FORMAL-PROGRESS.md', 'candidate.json',
             'provenance.json', 'main.tex', 'paper.pdf', 'final-review-hashes.json',
             'frozen-parent-hashes.json']
    for folder in ['formal', 'reviews', 'verification', 'scripts', 'sources']:
        names.extend(str(p.relative_to(CANDIDATE))
                     for p in sorted((CANDIDATE / folder).iterdir()) if p.is_file())
    assert len(names) == len(set(names))
    assert not any(Path(n).suffix in ['.olean', '.ilean', '.pyc'] for n in names)
    payload = {name: (CANDIDATE / name).read_bytes() for name in sorted(names)}
    manifest = {name: sha(value) for name, value in payload.items()}
    payload['MANIFEST.json'] = (json.dumps(manifest, indent=2) + '\n').encode()
    assert not EXTRACT.exists(), 'Use a new empty extraction destination'
    PACKET.parent.mkdir(exist_ok=True)
    with zipfile.ZipFile(PACKET, 'w', zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for name, data in sorted(payload.items()):
            info = zipfile.ZipInfo('connection-graph/' + name, (2026, 10, 26, 0, 0, 0))
            info.external_attr = 0o100644 << 16
            archive.writestr(info, data, compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)
    with zipfile.ZipFile(PACKET) as archive:
        assert archive.testzip() is None
        assert sorted(archive.namelist()) == sorted('connection-graph/' + n for n in payload)
        for name, data in payload.items():
            assert archive.read('connection-graph/' + name) == data, name
        archive.extractall(EXTRACT)
    extracted = EXTRACT / 'connection-graph'
    assert json.loads((extracted / 'MANIFEST.json').read_text()) == manifest
    for name, digest in manifest.items():
        assert sha((extracted / name).read_bytes()) == digest, name
    result = {'status': 'PASS: exact archive readback and manifest hashes; Lean replay pending',
              'packet': str(PACKET.relative_to(ROOT)), 'sha256': sha(PACKET.read_bytes()),
              'members': len(payload), 'extracted': str(extracted)}
    (EXTRACT / 'readback.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
