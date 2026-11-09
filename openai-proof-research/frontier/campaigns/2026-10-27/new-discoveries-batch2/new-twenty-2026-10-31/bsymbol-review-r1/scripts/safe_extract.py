# Safe extraction of the author ZIP: reject absolute paths, '..', symlinks; record hashes.
import sys, zipfile, pathlib, hashlib, json, stat
zp, out = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2])
out.mkdir(parents=True, exist_ok=False)
rec = {"zip": str(zp), "zip_sha256": hashlib.sha256(zp.read_bytes()).hexdigest(), "entries": []}
with zipfile.ZipFile(zp) as z:
    for i in z.infolist():
        name = i.filename
        mode = (i.external_attr >> 16)
        assert not name.startswith("/") and ".." not in pathlib.PurePosixPath(name).parts, name
        assert not stat.S_ISLNK(mode), name
        if name.endswith("/"): continue
        data = z.read(i)
        dst = out / name; dst.parent.mkdir(parents=True, exist_ok=True); dst.write_bytes(data)
        rec["entries"].append({"name": name, "bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()})
print(json.dumps(rec, indent=1))
