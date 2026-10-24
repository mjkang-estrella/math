"""Read-only exact-selection, bytes and modes verifier; all three detached anchors required."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat

OUTSIDE = {'MANIFEST.json': 0o600, 'FINAL.md': None, 'REPORT.md': 0o644, 'ANCHORS.json': 0o600}
# FINAL is a selected payload file, not an outside file.
OUTSIDE.pop('FINAL.md')
SCHEMA = 'structural221-contribution-r1-exact-selection-v1'

def require(ok, message):
    if not ok:
        raise ValueError(message)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def inventory(root):
    require(root.is_dir() and not root.is_symlink(), 'invalid root')
    dirs = {'': stat.S_IMODE(root.stat().st_mode)}
    files = {}
    for base, names, leaves in os.walk(root, followlinks=False):
        for name in names + leaves:
            p = Path(base) / name
            rel = p.relative_to(root).as_posix()
            mode = p.lstat().st_mode
            require(not stat.S_ISLNK(mode), 'symlink: ' + rel)
            if stat.S_ISDIR(mode):
                dirs[rel] = stat.S_IMODE(mode)
            else:
                require(stat.S_ISREG(mode), 'nonregular file: ' + rel)
                files[rel] = p
    return files, dirs

def check_entries(root, manifest, outside=None):
    # The optional outside set is for tiny copied controls and the pre-REPORT payload check only.
    # The public CLI always requires all three outside files.
    if outside is None:
        outside = set(OUTSIDE)
    files, dirs = inventory(root)
    entries = manifest['files']
    expected = {e['path']: e for e in entries}
    require(len(expected) == len(entries), 'duplicate file')
    for name in expected:
        p = PurePosixPath(name)
        require(not p.is_absolute() and '..' not in p.parts and str(p) == name, 'unsafe path')
    require(not (set(expected) & set(OUTSIDE)), 'outside file included in payload')
    require(set(files) == set(expected) | set(outside), 'exact file selection differs')
    dd = manifest['directories']
    want_dirs = {e['path']: e['mode'] for e in dd}
    require(len(want_dirs) == len(dd) and dirs == want_dirs, 'exact directories or modes differ')
    for name, e in expected.items():
        p = files[name]
        require(p.stat().st_size == e['bytes'], 'size: ' + name)
        require(stat.S_IMODE(p.stat().st_mode) == e['mode'], 'mode: ' + name)
        require(sha(p) == e['sha256'], 'hash: ' + name)
    for name in outside:
        if name in OUTSIDE:
            require(stat.S_IMODE(files[name].stat().st_mode) == OUTSIDE[name], 'outside mode: ' + name)
    return {'selected_files': len(expected), 'directories': len(dirs)}

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', type=Path, required=True)
    ap.add_argument('--final-sha', required=True)
    ap.add_argument('--manifest-sha', required=True)
    ap.add_argument('--report-sha', required=True)
    args = ap.parse_args()
    root = args.root.absolute()
    inventory(root)
    anchors = {'FINAL.md': args.final_sha, 'MANIFEST.json': args.manifest_sha,
               'REPORT.md': args.report_sha}
    for name, h in anchors.items():
        require(len(h) == 64 and all(c in '0123456789abcdef' for c in h), 'malformed anchor')
        require(sha(root/name) == h, 'detached anchor: ' + name)
    manifest = json.loads((root/'MANIFEST.json').read_bytes())
    require(manifest['schema'] == SCHEMA, 'schema mismatch')
    result = check_entries(root, manifest)
    require(json.loads((root/'ANCHORS.json').read_bytes()) == anchors, 'anchor record mismatch')
    result.update({'artifact_check': 'passed', 'anchors_checked': list(anchors),
                   'full_correctness': 'UNDISCHARGED', 'mathematical_gate': 'none'})
    print(json.dumps(result, sort_keys=True))

if __name__ == '__main__':
    main()
