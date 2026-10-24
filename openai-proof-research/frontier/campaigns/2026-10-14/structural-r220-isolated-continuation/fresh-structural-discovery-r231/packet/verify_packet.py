"""Read-only byte/mode/selection verification. This is not mathematical review."""
from pathlib import Path, PurePosixPath
import argparse, hashlib, json, os, stat

def sha(data):
    return hashlib.sha256(data).hexdigest()

def actual_files(root):
    files = set()
    for base, dirs, names in os.walk(root, followlinks=False):
        for name in dirs + names:
            p = Path(base) / name
            if p.is_symlink():
                raise ValueError('symlink in packet: ' + str(p))
        for name in names:
            p = Path(base) / name
            if not stat.S_ISREG(p.stat().st_mode):
                raise ValueError('nonregular file: ' + str(p))
            files.add(p.relative_to(root).as_posix())
    return files

def verify_entries(root, entries, excluded=frozenset()):
    expected = {x['path'] for x in entries}
    if len(expected) != len(entries):
        raise ValueError('duplicate selection entry')
    if actual_files(root) - set(excluded) != expected:
        raise ValueError('exact selection mismatch')
    for e in entries:
        rel = PurePosixPath(e['path'])
        if rel.is_absolute() or '..' in rel.parts or rel.as_posix() != e['path']:
            raise ValueError('unsafe relative path')
        p = root / e['path']
        data = p.read_bytes()
        if len(data) != e['bytes'] or sha(data) != e['sha256']:
            raise ValueError('bytes/hash mismatch: ' + e['path'])
        if format(stat.S_IMODE(p.stat().st_mode), '04o') != e['mode']:
            raise ValueError('mode mismatch: ' + e['path'])
    return len(entries)

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--packet', type=Path, required=True)
    ap.add_argument('--report', type=Path, required=True)
    ap.add_argument('--final-sha256', required=True)
    ap.add_argument('--manifest-sha256', required=True)
    ap.add_argument('--report-sha256', required=True)
    a = ap.parse_args()
    for p, expected in [(a.packet/'FINAL.md',a.final_sha256),
                        (a.packet/'MANIFEST.json',a.manifest_sha256),
                        (a.report,a.report_sha256)]:
        if len(expected) != 64 or sha(p.read_bytes()) != expected:
            raise ValueError('explicit detached anchor mismatch: '+str(p))
    if a.packet.is_symlink() or a.report.is_symlink():
        raise ValueError('symlink at explicit anchor')
    manifest = json.loads((a.packet/'MANIFEST.json').read_bytes())
    count = verify_entries(a.packet, manifest['entries'], {'MANIFEST.json'})
    if format(stat.S_IMODE((a.packet/'MANIFEST.json').stat().st_mode), '04o') != '0444':
        raise ValueError('manifest mode mismatch')
    if format(stat.S_IMODE(a.report.stat().st_mode), '04o') != '0444':
        raise ValueError('outside report mode mismatch')
    dirs = {'.': format(stat.S_IMODE(a.packet.stat().st_mode), '04o')}
    for base, names, _ in os.walk(a.packet, followlinks=False):
        for name in names:
            d = Path(base)/name
            dirs[d.relative_to(a.packet).as_posix()] = format(stat.S_IMODE(d.stat().st_mode), '04o')
    if dirs != manifest['directories']:
        raise ValueError('directory selection/mode mismatch')
    authenticated = json.loads((a.packet/'private/source-authentication.json').read_bytes())
    tree = json.loads((a.packet/'private/tree-selection.json').read_bytes())
    blobs = {e['path']:e for e in tree if e['type']=='blob'}
    if len(authenticated) != 17 or len({e['path'] for e in authenticated}) != 17 or len(blobs) != 17 or len(tree) != 20:
        raise ValueError('wrong canonical selection count')
    for e in authenticated:
        data = (a.packet/e['local']).read_bytes()
        blob = hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        match = blobs.get(e['path'], blobs.get(e['path'].removeprefix('preprints/')))
        if match is None or blob != e['git_blob'] or blob != match['sha']:
            raise ValueError('canonical blob mismatch: '+e['path'])
        if sha(data) != e['sha256'] or len(data) != e['bytes']:
            raise ValueError('canonical byte mismatch: '+e['path'])
    print(json.dumps({'artifact_only':True,'selected_files':count,
                      'authenticated_canonical_blobs':17,
                      'explicit_detached_anchors':'matched',
                      'exact_selection_bytes_modes':'matched',
                      'mathematical_review':'not performed'},indent=2))

if __name__ == '__main__':
    main()
