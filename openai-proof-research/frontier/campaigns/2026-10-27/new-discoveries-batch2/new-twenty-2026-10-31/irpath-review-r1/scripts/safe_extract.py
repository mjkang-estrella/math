"""Safely extract an arXiv e-print (tar.gz, or single gzip file) into a FRESH directory.
Regular files only; rejects absolute paths, '..', links, devices. Usage: safe_extract.py BODY OUTDIR"""
import sys, os, tarfile, gzip, io, json, hashlib
body, out = sys.argv[1], sys.argv[2]
os.makedirs(out)  # must not exist
raw = open(body, "rb").read()
data = gzip.decompress(raw) if raw[:2] == b"\x1f\x8b" else raw
res = {}
try:
    tf = tarfile.open(fileobj=io.BytesIO(data))
    for m in tf.getmembers():
        n = m.name
        if not m.isfile() or n.startswith("/") or ".." in n.split("/"):
            res[n] = "SKIPPED"; continue
        p = os.path.join(out, n.replace("/", "__"))
        b = tf.extractfile(m).read()
        with open(p, "xb") as f: f.write(b)
        res[n] = hashlib.sha256(b).hexdigest()
except tarfile.ReadError:
    p = os.path.join(out, "main.tex")
    with open(p, "xb") as f: f.write(data)
    res["main.tex(single)"] = hashlib.sha256(data).hexdigest()
print(json.dumps(res, indent=1))
