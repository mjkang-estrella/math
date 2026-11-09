#!/usr/bin/env python3
"""Read-only inspection helper for polar-review-r1.

Usage:
  inspect.py ls DIR [MAXDEPTH]     list files (size, sha256) under DIR
  inspect.py hash OUTJSON PATH...  sha256 every file under PATHs, write JSON (refuses to overwrite)
  inspect.py grep PATTERN FILE...  regex search in named files only (no recursion)
"""
import hashlib, json, os, re, sys

def sha(p):
    h = hashlib.sha256()
    with open(p, 'rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''):
            h.update(b)
    return h.hexdigest()

def walk(root, maxdepth=99):
    root = os.path.abspath(root)
    if os.path.isfile(root):
        yield root
        return
    base = root.count(os.sep)
    for d, ds, fs in os.walk(root):
        ds.sort()
        if d.count(os.sep) - base >= maxdepth:
            ds[:] = []
        for f in sorted(fs):
            yield os.path.join(d, f)

cmd = sys.argv[1]
if cmd == 'ls':
    md = int(sys.argv[3]) if len(sys.argv) > 3 else 99
    for p in walk(sys.argv[2], md):
        try:
            print(f"{os.path.getsize(p):>10} {sha(p)[:16]} {os.path.relpath(p, sys.argv[2])}")
        except OSError as e:
            print('ERR', p, e)
elif cmd == 'hash':
    out = sys.argv[2]
    if os.path.exists(out):
        sys.exit('refusing to overwrite ' + out)
    res = {}
    for root in sys.argv[3:]:
        for p in walk(root):
            res[p] = sha(p)
    with open(out, 'x') as f:
        json.dump(res, f, indent=1, sort_keys=True)
    print(len(res), 'files hashed ->', out)
elif cmd == 'grep':
    pat = re.compile(sys.argv[2])
    for fn in sys.argv[3:]:
        with open(fn, errors='replace') as f:
            for i, line in enumerate(f, 1):
                if pat.search(line):
                    print(f"{fn}:{i}: {line.rstrip()[:300]}")
else:
    sys.exit('unknown cmd')
