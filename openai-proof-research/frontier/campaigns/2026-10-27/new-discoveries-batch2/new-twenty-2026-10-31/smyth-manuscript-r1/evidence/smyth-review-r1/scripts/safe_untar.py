import sys, tarfile, os, hashlib
src, dst = sys.argv[1], sys.argv[2]
os.makedirs(dst, exist_ok=False)
with tarfile.open(src, 'r:gz') as t:
    for m in t.getmembers():
        print(m.name, m.size, m.type)
    t.extractall(dst, filter='data')
for root, _, fs in os.walk(dst):
    for f in fs:
        p = os.path.join(root, f)
        print(hashlib.sha256(open(p,'rb').read()).hexdigest(), os.path.relpath(p, dst))
