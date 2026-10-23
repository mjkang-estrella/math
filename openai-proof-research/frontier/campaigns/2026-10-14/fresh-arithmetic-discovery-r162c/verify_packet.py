"""Read-only packet verification; expected detached hashes are mandatory inputs."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def require(condition, message):
    if not condition:
        raise ValueError(message)

def main():
    ap = argparse.ArgumentParser()
    for name in ('packet', 'manifest', 'report', 'final-sha256',
                 'manifest-sha256', 'report-sha256'):
        ap.add_argument('--' + name, required=True)
    a = ap.parse_args()
    packet, manifest, report = map(Path, (a.packet, a.manifest, a.report))
    for path, expected in ((packet/'FINAL.md', a.final_sha256),
                           (manifest, a.manifest_sha256),
                           (report, a.report_sha256)):
        require(not path.is_symlink(), 'symlink anchor')
        require(len(expected) == 64 and sha(path) == expected, 'detached anchor mismatch: '+str(path))
    data = json.loads(manifest.read_text())
    require(data['schema'] == 1, 'unknown schema')
    expected_paths = set()
    total = 0
    for entry in data['files']:
        rel = PurePosixPath(entry['path'])
        require(not rel.is_absolute() and '..' not in rel.parts and str(rel) == entry['path'], 'unsafe path')
        require(str(rel) not in expected_paths, 'duplicate path')
        expected_paths.add(str(rel))
        path = packet / rel
        ancestor = packet
        require(not ancestor.is_symlink(), 'symlink packet')
        for component in rel.parts:
            ancestor = ancestor / component
            require(not ancestor.is_symlink(), 'symlink member')
        require(path.is_file(), 'missing member: '+str(rel))
        require(path.stat().st_size == entry['bytes'], 'size mismatch: '+str(rel))
        require(sha(path) == entry['sha256'], 'digest mismatch: '+str(rel))
        total += entry['bytes']
    actual = set()
    for path in packet.rglob('*'):
        require(not path.is_symlink(), 'symlink in packet')
        if path.is_file():
            actual.add(path.relative_to(packet).as_posix())
    require(actual == expected_paths, 'packet inventory mismatch')
    require('FINAL.md' in expected_paths, 'FINAL missing from manifest')
    print(json.dumps({'artifact_check':'matched', 'files':len(actual), 'bytes':total}))

if __name__ == '__main__':
    main()
