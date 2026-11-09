"""Read-only exact-selection and detached-anchor verifier. No mathematical gate."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat
import sys
sys.dont_write_bytecode = True

def digest(b):
    return hashlib.sha256(b).hexdigest()

def inventory(root):
    files, dirs = {}, {}
    def visit(p, rel):
        s = p.lstat()
        if not stat.S_ISDIR(s.st_mode) or p.is_symlink():
            raise ValueError('non-directory or symlink: ' + rel)
        dirs[rel] = format(stat.S_IMODE(s.st_mode), '04o')
        for e in sorted(os.scandir(p), key=lambda z: z.name):
            q = Path(e.path)
            rp = e.name if rel == '.' else rel + '/' + e.name
            es = q.lstat()
            if stat.S_ISLNK(es.st_mode):
                raise ValueError('symlink: ' + rp)
            if stat.S_ISDIR(es.st_mode):
                visit(q, rp)
            elif stat.S_ISREG(es.st_mode):
                b = q.read_bytes()
                files[rp] = {'path': rp, 'bytes': len(b), 'sha256': digest(b),
                             'mode': format(stat.S_IMODE(es.st_mode), '04o')}
            else:
                raise ValueError('special file: ' + rp)
    visit(root, '.')
    return files, dirs

def main():
    p = argparse.ArgumentParser(description=__doc__)
    for x in ('root', 'manifest', 'final', 'report', 'manifest-sha256', 'final-sha256', 'report-sha256'):
        p.add_argument('--' + x, required=True)
    a = p.parse_args()
    root = Path(a.root)
    for name in ('manifest_sha256', 'final_sha256', 'report_sha256'):
        h = getattr(a, name)
        if len(h) != 64 or any(c not in '0123456789abcdef' for c in h):
            raise ValueError('invalid explicit anchor: ' + name)
    mp, rp = Path(a.manifest), Path(a.report)
    if mp.is_symlink() or rp.is_symlink():
        raise ValueError('detached artifact is a symlink')
    mb, rb = mp.read_bytes(), rp.read_bytes()
    if digest(mb) != a.manifest_sha256:
        raise ValueError('detached MANIFEST hash mismatch')
    if digest(rb) != a.report_sha256:
        raise ValueError('detached REPORT hash mismatch')
    m = json.loads(mb)
    if m['schema'] != 1:
        raise ValueError('unsupported schema')
    paths = [x['path'] for x in m['files']]
    if len(paths) != len(set(paths)):
        raise ValueError('duplicate file selection')
    for s in paths + [a.final]:
        q = PurePosixPath(s)
        if q.is_absolute() or '..' in q.parts or s != q.as_posix() or s == '.':
            raise ValueError('unsafe/noncanonical relative path: ' + s)
    actual, dirs = inventory(root)
    wanted = {x['path']: x for x in m['files']}
    if set(actual) != set(wanted):
        raise ValueError('exact file selection mismatch')
    if dirs != m['directories']:
        raise ValueError('directory selection/mode mismatch')
    for s in sorted(wanted):
        if actual[s] != wanted[s]:
            raise ValueError('file digest/size/mode mismatch: ' + s)
    if a.final != m['final'] or a.final not in actual:
        raise ValueError('FINAL selection mismatch')
    if actual[a.final]['sha256'] != a.final_sha256:
        raise ValueError('detached FINAL hash mismatch')
    print(json.dumps({'artifact_verification': 'matched', 'files': len(actual),
                      'directories': len(dirs), 'mathematical_grade': 'not_assigned'}))

if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, OSError, json.JSONDecodeError) as e:
        print('artifact verification rejected: ' + str(e), file=sys.stderr)
        sys.exit(1)
