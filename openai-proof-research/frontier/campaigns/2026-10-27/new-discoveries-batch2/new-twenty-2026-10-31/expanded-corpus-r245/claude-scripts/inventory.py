"""List files under a directory with size and sha256 (read-only)."""
import hashlib
import os
import sys

root = sys.argv[1]
maxdepth = int(sys.argv[2]) if len(sys.argv) > 2 else 99
for dp, dns, fns in os.walk(root):
    depth = dp[len(root):].count(os.sep)
    dns.sort()
    if depth >= maxdepth:
        dns[:] = []
    for fn in sorted(fns):
        p = os.path.join(dp, fn)
        try:
            st = os.stat(p)
            h = hashlib.sha256()
            if st.st_size < 50_000_000:
                with open(p, 'rb') as f:
                    for b in iter(lambda: f.read(1 << 20), b''):
                        h.update(b)
                hx = h.hexdigest()
            else:
                hx = 'skipped-large'
            print(f"{st.st_size:>10} {hx[:16]} {os.path.relpath(p, root)}")
        except OSError as e:
            print('ERR', p, e)
