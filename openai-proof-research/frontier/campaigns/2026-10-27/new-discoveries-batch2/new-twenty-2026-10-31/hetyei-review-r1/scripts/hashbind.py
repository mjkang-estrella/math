#!/usr/bin/env python3
"""Read-only: list files under given paths with size and sha256.
Usage: hashbind.py OUT.json PATH [PATH ...]
Refuses to overwrite OUT.json. Directories walked recursively (no symlink follow)."""
import hashlib, json, os, sys

def h(p):
    d = hashlib.sha256()
    with open(p, 'rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            d.update(chunk)
    return d.hexdigest()

def main():
    out = sys.argv[1]
    if os.path.exists(out):
        sys.exit('refusing to overwrite ' + out)
    rec = {}
    for root in sys.argv[2:]:
        if os.path.isfile(root):
            rec[root] = [os.path.getsize(root), h(root)]
            continue
        for dp, dns, fns in os.walk(root, followlinks=False):
            dns.sort()
            for fn in sorted(fns):
                p = os.path.join(dp, fn)
                if os.path.islink(p) or not os.path.isfile(p):
                    rec[p] = ['nonregular', None]
                    continue
                rec[p] = [os.path.getsize(p), h(p)]
    with open(out, 'x') as f:
        json.dump(rec, f, indent=1, sort_keys=True)
    for k in sorted(rec):
        print(rec[k][0], (rec[k][1] or '')[:16], k)
    print('files', len(rec))

main()
