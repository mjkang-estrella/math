"""Read-only verifier for this review's own exact selection and detached anchors."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat
import sys

FORMAT = 'structural-r210-contribution-r1-selection-v1'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def inventory(packet):
    entries = {}

    def visit(path, relative):
        info = path.lstat()
        mode = format(stat.S_IMODE(info.st_mode), '04o')
        if stat.S_ISDIR(info.st_mode):
            entries[relative] = {'type': 'directory', 'mode': mode}
            for entry in sorted(os.scandir(path), key=lambda item: item.name):
                child = entry.name if relative == '.' else relative + '/' + entry.name
                visit(Path(entry.path), child)
        elif stat.S_ISREG(info.st_mode):
            entries[relative] = {'type': 'file', 'mode': mode,
                                 'bytes': info.st_size, 'sha256': digest(path)}
        else:
            raise ValueError('Symlink or non-regular entry: ' + relative)

    visit(packet, '.')
    return entries


def verify(packet, manifest, manifest_sha256, final_sha256, report, report_sha256):
    require(digest(manifest) == manifest_sha256, 'Detached MANIFEST mismatch')
    selected = json.loads(manifest.read_text())
    require(selected['format'] == FORMAT, 'Wrong manifest format')
    expected = selected['entries']
    require(len({item['path'] for item in expected}) == len(expected), 'Duplicate path')
    for item in expected:
        name = PurePosixPath(item['path'])
        require(not name.is_absolute() and '..' not in name.parts, 'Unsafe path')
        require(str(name) == item['path'], 'Noncanonical path')
    observed = inventory(packet)
    require(set(observed) == {item['path'] for item in expected}, 'Exact selection mismatch')
    for item in expected:
        actual = observed[item['path']]
        required = {key: value for key, value in item.items() if key not in ('path', 'rights')}
        require(actual == required, 'Bytes/type/mode mismatch: ' + item['path'])
        private = item['path'] == 'private' or item['path'].startswith('private/')
        prescribed_mode = ('0700' if private else '0755') if actual['type'] == 'directory' else ('0600' if private else '0644')
        require(actual['mode'] == prescribed_mode, 'Protection mode mismatch: ' + item['path'])
    final = selected['final']
    require(final == 'FINAL.md' and observed[final]['type'] == 'file', 'Missing exact FINAL')
    require(observed[final]['sha256'] == final_sha256, 'Detached FINAL mismatch')
    require(not report.resolve().is_relative_to(packet.resolve()), 'REPORT must be outside packet')
    require(stat.S_ISREG(report.lstat().st_mode), 'REPORT must be regular')
    require(stat.S_IMODE(report.lstat().st_mode) == 0o644, 'REPORT mode mismatch')
    require(digest(report) == report_sha256, 'Detached REPORT mismatch')
    return {'verification': 'exact selected bytes, types, modes and all detached anchors match',
            'files': sum(item['type'] == 'file' for item in observed.values()),
            'directories': sum(item['type'] == 'directory' for item in observed.values()),
            'FINAL_SHA256': final_sha256, 'MANIFEST_SHA256': manifest_sha256,
            'REPORT_SHA256': report_sha256, 'mathematical_gate': False}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('packet', 'manifest', 'manifest-sha256', 'final-sha256', 'report', 'report-sha256'):
        parser.add_argument('--' + name, required=True)
    args = parser.parse_args()
    try:
        result = verify(Path(args.packet), Path(args.manifest), args.manifest_sha256,
                        args.final_sha256, Path(args.report), args.report_sha256)
        print(json.dumps(result, indent=2))
    except Exception as error:
        print(str(error), file=sys.stderr)
        sys.exit(1)
