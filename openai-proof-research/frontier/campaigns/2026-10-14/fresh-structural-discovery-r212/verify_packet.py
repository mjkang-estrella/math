"""Read-only exact-selection verifier. Supply detached anchors explicitly.
Artifact integrity only; no mathematical correctness or contribution gate.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import stat
import sys

OUTSIDE_FILES = {'private/MANIFEST.json', 'REPORT.md', 'ANCHORS.json'}
OUTSIDE_DIRECTORY = 'private/seal-controls'

def digest(path):
    with path.open('rb') as stream:
        h = hashlib.sha256()
        for chunk in iter(lambda: stream.read(1048576), b''):
            h.update(chunk)
        return h.hexdigest()

def inventory(root):
    files, directories = {}, {}
    def visit(folder):
        with os.scandir(folder) as entries:
            for entry in sorted(entries, key=lambda e: e.name):
                path = Path(entry.path)
                rel = path.relative_to(root).as_posix()
                info = entry.stat(follow_symlinks=False)
                if stat.S_ISLNK(info.st_mode):
                    raise ValueError('symlink: ' + rel)
                if stat.S_ISDIR(info.st_mode):
                    if rel == OUTSIDE_DIRECTORY:
                        continue
                    directories[rel] = stat.S_IMODE(info.st_mode)
                    visit(path)
                elif stat.S_ISREG(info.st_mode):
                    if rel not in OUTSIDE_FILES:
                        files[rel] = info
                else:
                    raise ValueError('nonregular entry: ' + rel)
    visit(root)
    return files, directories

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root', required=True)
    for label in ('final', 'manifest', 'report'):
        p.add_argument('--' + label + '-sha256', required=True)
    a = p.parse_args()
    root = Path(a.root).absolute()
    if root.is_symlink() or not root.is_dir():
        raise ValueError('root must be a real directory')
    anchors = [('FINAL.md', a.final_sha256, 0o644),
               ('private/MANIFEST.json', a.manifest_sha256, 0o600),
               ('REPORT.md', a.report_sha256, 0o644)]
    for rel, expected, mode in anchors:
        if len(expected) != 64 or any(c not in '0123456789abcdef' for c in expected):
            raise ValueError('explicit lowercase SHA256 required: ' + rel)
        path = root / rel
        info = path.lstat()
        if not stat.S_ISREG(info.st_mode) or stat.S_IMODE(info.st_mode) != mode:
            raise ValueError('anchor type/mode mismatch: ' + rel)
        if digest(path) != expected:
            raise ValueError('detached anchor mismatch: ' + rel)
    manifest = json.loads((root / 'private/MANIFEST.json').read_text())
    if manifest['schema'] != 'r212-exact-selection-v1':
        raise ValueError('schema mismatch')
    if set(manifest['outside_files']) != OUTSIDE_FILES or manifest['outside_directory'] != OUTSIDE_DIRECTORY:
        raise ValueError('outside selection mismatch')
    if stat.S_IMODE(root.stat().st_mode) != manifest['root_mode']:
        raise ValueError('root mode mismatch')
    files, directories = inventory(root)
    expected = {}
    for item in manifest['files']:
        rel = item['path']
        if rel in expected or Path(rel).is_absolute() or '..' in Path(rel).parts:
            raise ValueError('unsafe/duplicate selected path')
        expected[rel] = item
    if set(files) != set(expected):
        raise ValueError('exact selection mismatch: added=' + str(sorted(set(files)-set(expected)))
                         + '; missing=' + str(sorted(set(expected)-set(files))))
    if directories != manifest['directories']:
        raise ValueError('directory selection/mode mismatch')
    for rel, info in files.items():
        item = expected[rel]
        if info.st_size != item['bytes'] or stat.S_IMODE(info.st_mode) != item['mode']:
            raise ValueError('size/mode mismatch: ' + rel)
        if digest(root / rel) != item['sha256']:
            raise ValueError('content mismatch: ' + rel)
    # ANCHORS.json is a convenience carrier, never the source of trusted anchors.
    carrier = root / 'ANCHORS.json'
    info = carrier.lstat()
    if not stat.S_ISREG(info.st_mode) or stat.S_IMODE(info.st_mode) != 0o644:
        raise ValueError('anchor carrier type/mode mismatch')
    carrier_data = json.loads(carrier.read_text())
    if carrier_data != {'FINAL.md': a.final_sha256,
                        'private/MANIFEST.json': a.manifest_sha256,
                        'REPORT.md': a.report_sha256}:
        raise ValueError('anchor carrier disagrees with explicit anchors')
    print(json.dumps({'artifact_integrity': 'verified', 'selected_files': len(files),
                      'selected_bytes': sum(x.st_size for x in files.values()),
                      'mathematical_gate': False}, sort_keys=True))

if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, KeyError, TypeError) as error:
        print('VERIFICATION FAILED: ' + str(error), file=sys.stderr)
        raise SystemExit(1)
