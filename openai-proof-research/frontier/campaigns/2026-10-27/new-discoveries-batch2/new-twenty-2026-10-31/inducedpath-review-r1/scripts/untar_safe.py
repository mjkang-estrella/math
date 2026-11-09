import sys, tarfile, os
src, dst = sys.argv[1], sys.argv[2]
assert os.path.isdir(dst) and not os.listdir(dst)
with tarfile.open(src, "r:*") as t:
    t.extractall(dst, filter="data")
for r, d, f in os.walk(dst):
    for x in f:
        p = os.path.join(r, x); print(os.path.getsize(p), os.path.relpath(p, dst))
