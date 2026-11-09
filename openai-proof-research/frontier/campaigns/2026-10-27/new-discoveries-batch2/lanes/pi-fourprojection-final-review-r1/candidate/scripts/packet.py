#!/usr/bin/env python3
"""Deterministic certificate archive plus fresh extracted replay; no acceptance."""
from pathlib import Path
import hashlib
import io
import json
import shutil
import subprocess
import sys
import zipfile

ROOT = Path(__file__).resolve().parents[1]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    manifest = json.loads((ROOT / 'candidate.json').read_text())
    paths = [ROOT / 'candidate.json', ROOT / 'SUMMARY.md', ROOT / 'README.md',
             ROOT / 'PROOF.md', ROOT / 'main.tex', ROOT / 'paper.pdf', ROOT / 'paper-qa.json',
             ROOT / 'component-provenance.json', ROOT / 'final-review-hashes.json', ROOT / '.gitignore',
             ROOT / 'verification/pins.json', ROOT / 'verification/verify_candidate.py',
             ROOT / 'scripts/packet.py']
    paths += [ROOT / 'formal' / (m['module'] + '.lean') for m in manifest['modules']]
    paths += sorted((ROOT / 'sources').glob('*')) + sorted((ROOT / 'reviews').glob('*.md'))
    paths += sorted((ROOT / 'renders').glob('*.png'))
    # An explicit file list excludes local objects, caches and previous receipts.
    hashes = {str(p.relative_to(ROOT)): digest(p) for p in sorted(paths)}
    hashes_bytes = (json.dumps(hashes, indent=2) + '\n').encode()
    entries = {str(p.relative_to(ROOT)): p.read_bytes() for p in paths}
    entries['SHA256SUMS.json'] = hashes_bytes
    packet_dir = ROOT / 'packet'
    packet_dir.mkdir(exist_ok=True)
    archive = packet_dir / 'fourprojection-paper-proof.zip'
    def serialize():
        buf = io.BytesIO()
        with zipfile.ZipFile(buf, 'w', zipfile.ZIP_DEFLATED, compresslevel=9) as z:
            for name, data in sorted(entries.items()):
                info = zipfile.ZipInfo(name, (1980, 1, 1, 0, 0, 0))
                info.compress_type = zipfile.ZIP_DEFLATED
                info.create_system = 3
                info.external_attr = 0o100644 << 16
                z.writestr(info, data, compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)
        return buf.getvalue()
    data = serialize()
    if data != serialize():
        raise RuntimeError('Repeated serialization differs')
    archive.write_bytes(data)
    extracted = ROOT / 'build/extracted-packet'
    if extracted.exists():
        shutil.rmtree(extracted)
    extracted.mkdir(parents=True)
    with zipfile.ZipFile(archive) as z:
        for member in z.infolist():
            target = (extracted / member.filename).resolve()
            if not target.is_relative_to(extracted.resolve()):
                raise RuntimeError('Archive path escapes extraction directory')
        z.extractall(extracted)
    frozen = json.loads((extracted / 'SHA256SUMS.json').read_text())
    for name, expected in frozen.items():
        if digest(extracted / name) != expected:
            raise RuntimeError('Extracted hash mismatch: ' + name)
    command = [sys.executable, str(extracted / 'verification/verify_candidate.py'),
               str(extracted)]
    result = subprocess.run(command, text=True, capture_output=True)
    (ROOT / 'verification/extracted-replay.log').write_text(result.stdout + result.stderr)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    audit = json.loads((extracted / 'build/verified/audit.json').read_text())
    receipt = {
        'status': 'PASS_EXTRACTED_REPLAY',
        'source_endpoint_complete': manifest['source_endpoint_complete'],
        'discovery_accepted': False,
        'deterministic_bytes_repeated': True,
        'paper_included': True,
        'archive_sha256': digest(archive),
        'archive_files': len(entries),
        'extracted_declarations': audit['declarations'],
        'extracted_axioms': audit['axioms'],
        'extracted_audit_sha256': digest(extracted / 'build/verified/audit.json'),
        'qualification': manifest['qualification'],
    }
    (ROOT / 'verification/packet-result.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
