#!/usr/bin/env python3
"""Deterministic source packet plus fresh extracted replay; no acceptance."""
from pathlib import Path
from io import BytesIO
import hashlib
import json
import shutil
import subprocess
import tempfile
import zipfile

BASE = Path(__file__).resolve().parent
sha = lambda data: hashlib.sha256(data).hexdigest()
names = [
    'PROOF.md', 'README.md', 'SOURCE-COMPARISON.md', 'main.tex', 'paper.pdf',
    'paper-qa.json', 'provenance.json', 'component-bindings.json',
    'parent-type-audit.json', 'pins.json', 'verify_candidate.py', 'build_packet.py',
]
names += [str(p.relative_to(BASE)) for p in sorted((BASE/'formal').glob('*.lean'))]
names += ['formal/run_lean.py']
for folder in ['sources', 'reviews', 'verification']:
    names += [str(p.relative_to(BASE)) for p in sorted((BASE/folder).rglob('*'))
              if p.is_file()]
assert len(names) == len(set(names))
assert not any(n.endswith('.olean') for n in names)
payload = {n: (BASE/n).read_bytes() for n in sorted(names)}
manifest = json.dumps({n: sha(data) for n, data in payload.items()},
                      indent=2, sort_keys=True).encode() + b'\n'
(BASE/'MANIFEST.json').write_bytes(manifest)
payload['MANIFEST.json'] = manifest

def archive_bytes():
    out = BytesIO()
    with zipfile.ZipFile(out, 'w', compression=zipfile.ZIP_DEFLATED,
                         compresslevel=9) as archive:
        for name, data in sorted(payload.items()):
            info = zipfile.ZipInfo(name, (2026, 10, 28, 0, 0, 0))
            info.create_system = 3
            info.external_attr = 0o100644 << 16
            info.compress_type = zipfile.ZIP_DEFLATED
            archive.writestr(info, data, compress_type=zipfile.ZIP_DEFLATED,
                             compresslevel=9)
    return out.getvalue()

data = archive_bytes()
assert data == archive_bytes(), 'independent rebuild differs'
packet = BASE/'packet/mittag-modulus-paper-proof.zip'
packet.parent.mkdir(exist_ok=True)
packet.write_bytes(data)
out = BASE/'packet-extracted-replay'
out.mkdir(exist_ok=True)
with tempfile.TemporaryDirectory(prefix='mittag-packet-extracted-') as temp:
    target = Path(temp)
    with zipfile.ZipFile(BytesIO(data)) as archive:
        assert set(archive.namelist()) == set(payload)
        for info in archive.infolist():
            assert not Path(info.filename).is_absolute()
            assert '..' not in Path(info.filename).parts
        archive.extractall(target)
    for name, digest in json.loads((target/'MANIFEST.json').read_text()).items():
        assert sha((target/name).read_bytes()) == digest, name
    result = subprocess.run(['python3', 'verify_candidate.py'], cwd=target,
                            capture_output=True, text=True)
    (out/'run.log').write_text(result.stdout+result.stderr)
    assert result.returncode == 0, (result.returncode, result.stdout, result.stderr)
    for name in ['audit.json', 'Checks.log']:
        assert (target/'verification'/name).read_bytes() == (BASE/'verification'/name).read_bytes()
    for p in (target/'verification').iterdir():
        if p.is_file():
            shutil.copy2(p, out/p.name)
    # Every source and baseline receipt must remain unchanged by replay.
    for name, digest in json.loads(manifest).items():
        assert sha((target/name).read_bytes()) == digest, name
receipt = {
    'status': 'PASS fresh extracted replay; candidate credit 0',
    'packet_sha256': sha(data), 'manifest_sha256': sha(manifest),
    'payload_files': len(payload)-1, 'archive_entries': len(payload),
    'independent_rebuild_byte_identical': True,
    'fresh_extracted_source_replay': True, 'modules': 17,
    'public_declarations': 155, 'allowed_axioms': ['Classical.choice','Quot.sound','propext'],
    'audit_byte_identical': True, 'checks_byte_identical': True,
    'no_local_oleans': True, 'acceptance': False,
}
(BASE/'packet/receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')
frozen = {n: sha((BASE/n).read_bytes()) for n in sorted(payload)}
frozen['packet/mittag-modulus-paper-proof.zip'] = sha(data)
frozen['packet/receipt.json'] = sha((BASE/'packet/receipt.json').read_bytes())
(BASE/'final-review-hashes.json').write_text(json.dumps(frozen, indent=2)+'\n')
print(json.dumps(receipt, indent=2))
