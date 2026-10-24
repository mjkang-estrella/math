"""Read-only exact-selection/mode verification; three detached anchors are mandatory."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat

OUTSIDE = {'MANIFEST.json', 'REPORT.md', 'ANCHORS.json'}
OUTSIDE_MODES = {'MANIFEST.json': 0o600, 'REPORT.md': 0o644, 'ANCHORS.json': 0o600}
SCHEMA = 'structural-r221-proof-r1-exact-selection-v1'

def require(ok, message):
    if not ok:
        raise ValueError(message)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def inventory(root):
    require(stat.S_ISDIR(root.lstat().st_mode), 'root must be a real directory')
    files, dirs = {}, {'': stat.S_IMODE(root.lstat().st_mode)}
    for base, children, leaves in os.walk(root, followlinks=False):
        for name in children + leaves:
            path = Path(base) / name
            key = path.relative_to(root).as_posix()
            mode = path.lstat().st_mode
            require(not stat.S_ISLNK(mode), 'symlink: ' + key)
            if stat.S_ISDIR(mode):
                dirs[key] = stat.S_IMODE(mode)
            else:
                require(stat.S_ISREG(mode), 'nonregular: ' + key)
                files[key] = path
    return files, dirs

def check_selection(root, manifest):
    files, dirs = inventory(root)
    selected = {}
    for row in manifest['files']:
        name = row['path']
        pp = PurePosixPath(name)
        require(not pp.is_absolute() and '..' not in pp.parts and pp.as_posix() == name, 'unsafe path')
        require(name not in selected and name not in OUTSIDE, 'duplicate/outside payload path')
        selected[name] = row
    require(set(files) - OUTSIDE == set(selected), 'exact file selection differs')
    expected_dirs = {row['path']: row['mode'] for row in manifest['directories']}
    require(len(expected_dirs) == len(manifest['directories']) and dirs == expected_dirs,
            'directory selection or mode differs')
    for name, row in selected.items():
        p = files[name]
        require(p.stat().st_size == row['bytes'], 'byte count: ' + name)
        require(stat.S_IMODE(p.stat().st_mode) == row['mode'], 'mode: ' + name)
        require(digest(p) == row['sha256'], 'digest: ' + name)
    for name in set(files) & OUTSIDE:
        require(stat.S_IMODE(files[name].stat().st_mode) == OUTSIDE_MODES[name], 'outside mode: ' + name)
    return {'selected_files': len(selected), 'directories': len(dirs)}

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root', type=Path, required=True)
    p.add_argument('--final-sha', required=True)
    p.add_argument('--manifest-sha', required=True)
    p.add_argument('--report-sha', required=True)
    a = p.parse_args()
    root = a.root.absolute()
    files, _ = inventory(root)
    require(OUTSIDE <= set(files), 'missing outside file')
    anchors = {'FINAL.md': a.final_sha, 'MANIFEST.json': a.manifest_sha, 'REPORT.md': a.report_sha}
    for name, h in anchors.items():
        require(len(h) == 64 and all(x in '0123456789abcdef' for x in h), 'invalid explicit anchor')
        require(digest(root / name) == h, 'detached anchor: ' + name)
    manifest = json.loads((root / 'MANIFEST.json').read_bytes())
    require(manifest['schema'] == SCHEMA, 'schema')
    require(manifest['outside_selected_packet'] == sorted(OUTSIDE), 'outside selection')
    result = check_selection(root, manifest)
    require(json.loads((root / 'ANCHORS.json').read_bytes()) == anchors, 'anchor record differs')
    result.update(artifact_verification='passed', anchors_checked=list(anchors), mathematical_evidence=False)
    print(json.dumps(result, sort_keys=True))

if __name__ == '__main__':
    main()
