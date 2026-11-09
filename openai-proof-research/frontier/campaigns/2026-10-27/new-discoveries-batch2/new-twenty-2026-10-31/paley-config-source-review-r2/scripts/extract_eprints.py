"""Safely extract verified r1 eprint.bin archives into OUTDIR/<id>/ (gzip single file or tar). Usage: python3 -I extract_eprints.py R1DOWNLOADS OUTDIR"""
import gzip, io, os, sys, tarfile, hashlib, json
src, out = sys.argv[1], sys.argv[2]; rec = {}
for d in sorted(os.listdir(src)):
    if not d.startswith("arxiv-"): continue
    raw = open(os.path.join(src, d, "eprint.bin"), "rb").read()
    data = gzip.decompress(raw) if raw[:2] == b"\x1f\x8b" else raw
    od = os.path.join(out, d); os.makedirs(od, exist_ok=True); files = {}
    try:
        tf = tarfile.open(fileobj=io.BytesIO(data))
        for m in tf.getmembers():
            if not m.isfile(): continue
            name = os.path.normpath(m.name)
            if name.startswith("..") or os.path.isabs(name) or not name.endswith((".tex", ".bbl", ".bib", ".sty", ".json")): continue
            b = tf.extractfile(m).read(); p = os.path.join(od, name.replace("/", "__"))
            open(p, "wb").write(b); files[name] = hashlib.sha256(b).hexdigest()
    except tarfile.ReadError:
        open(os.path.join(od, "main.tex"), "wb").write(data); files["main.tex"] = hashlib.sha256(data).hexdigest()
    rec[d] = files
json.dump(rec, open(os.path.join(out, "extraction.json"), "w"), indent=1); print(json.dumps(rec, indent=1))
