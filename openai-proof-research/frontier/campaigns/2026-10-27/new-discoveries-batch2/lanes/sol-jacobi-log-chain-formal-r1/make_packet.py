#!/usr/bin/env python3
"""Create a deterministic source/evidence review packet without local build artifacts."""
import gzip
import hashlib
import io
import json
import tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def main():
    fixed = ['SUMMARY.md', 'provenance.json', 'build-order.json', 'declarations.json',
             'inputs-before.json', 'inputs-after.json', 'source-manifest.json',
             'formal-source.tar.gz', 'replay.py', 'make_packet.py',
             'verification/fresh/receipt.json']
    paths = {ROOT / name for name in fixed}
    paths.update((ROOT / 'formal').glob('*.lean'))
    paths.update([ROOT / 'formal/run_lean.py', ROOT / 'formal/guard.py'])
    paths.update((ROOT / 'inputs/frozen-root').glob('*.lean'))
    paths.update((ROOT / 'verification/fresh/logs').glob('*'))
    # Include failed incremental Lean diagnostics so the final source is clean.
    paths.update((ROOT / 'formal/logs').glob('*'))
    contents = {str(p.relative_to(ROOT)): p.read_bytes() for p in sorted(paths) if p.is_file()}
    assert all(not n.endswith(('.olean', '.ilean', '.c', '.o')) for n in contents)
    manifest = {name: hashlib.sha256(data).hexdigest() for name, data in sorted(contents.items())}
    manifest_bytes = (json.dumps(manifest, indent=2) + '\n').encode()
    (ROOT / 'packet-manifest.json').write_bytes(manifest_bytes)
    contents['packet-manifest.json'] = manifest_bytes
    buffer = io.BytesIO()
    with tarfile.open(fileobj=buffer, mode='w', format=tarfile.USTAR_FORMAT) as archive:
        for name, data in sorted(contents.items()):
            member = tarfile.TarInfo(name)
            member.size = len(data)
            member.mode = 0o644
            member.uid = member.gid = member.mtime = 0
            archive.addfile(member, io.BytesIO(data))
    packet = ROOT / 'component-packet.tar.gz'
    with packet.open('wb') as stream:
        with gzip.GzipFile(filename='', fileobj=stream, mode='wb', mtime=0) as compressed:
            compressed.write(buffer.getvalue())
    digest = hashlib.sha256(packet.read_bytes()).hexdigest()
    (ROOT / 'packet-sha256.txt').write_text(digest + '  component-packet.tar.gz\n')
    print(digest)


if __name__ == '__main__':
    main()
