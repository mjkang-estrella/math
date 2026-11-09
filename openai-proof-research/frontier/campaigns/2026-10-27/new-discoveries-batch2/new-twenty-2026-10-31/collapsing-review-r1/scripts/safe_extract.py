"""Safe extraction: refuse absolute paths, '..', symlinks, duplicates; target must be new and empty.
Usage: python3 -I safe_extract.py ZIP DEST"""
import sys, os, zipfile, stat, hashlib, json
z, dest = sys.argv[1], sys.argv[2]
assert os.path.isdir(dest) and not os.listdir(dest), "dest must be empty"
seen = set(); out = {}
with zipfile.ZipFile(z) as zf:
    for info in zf.infolist():
        n = info.filename
        assert not n.startswith("/") and ".." not in n.split("/") and "\\" not in n, n
        assert n not in seen, n; seen.add(n)
        mode = info.external_attr >> 16
        assert not stat.S_ISLNK(mode), n
        if n.endswith("/"): continue
        assert not n.endswith(".olean") and not n.endswith(".ilean"), n
        p = os.path.join(dest, n)
        os.makedirs(os.path.dirname(p), exist_ok=True)
        data = zf.read(info)
        with open(p, "xb") as f: f.write(data)
        out[n] = hashlib.sha256(data).hexdigest()
print(json.dumps(out, indent=1))
