"""Render every page of a PDF to PNG with poppler's pdftoppm (run as a child of this capped process).

Usage: python3 -I scripts/render.py PDF OUTDIR [DPI]
Writes OUTDIR/page-<n>.png and OUTDIR/render-receipt.json (pages, sizes, sha256).
"""
import sys
sys.dont_write_bytecode = True
import subprocess, os, json, hashlib, glob, time, re

pdf, outdir = sys.argv[1], sys.argv[2]
dpi = sys.argv[3] if len(sys.argv) > 3 else "110"
os.makedirs(outdir, exist_ok=False)
t0 = time.time()
r = subprocess.run(["pdftoppm", "-r", dpi, "-png", pdf, os.path.join(outdir, "page")],
                   capture_output=True, text=True, timeout=90)
pngs = sorted(glob.glob(os.path.join(outdir, "page-*.png")), key=lambda p: int(re.findall(r"(\d+)\.png$", p)[0]))
rec = {"pdf": pdf, "pdf_sha256": hashlib.sha256(open(pdf, "rb").read()).hexdigest(), "dpi": int(dpi),
       "returncode": r.returncode, "stderr": r.stderr[-2000:], "secs": round(time.time() - t0, 2),
       "pages": [{"png": os.path.basename(p), "bytes": os.path.getsize(p),
                  "sha256": hashlib.sha256(open(p, "rb").read()).hexdigest()} for p in pngs]}
with open(os.path.join(outdir, "render-receipt.json"), "x") as f:
    json.dump(rec, f, indent=1)
print(json.dumps({"returncode": r.returncode, "pages": len(pngs), "stderr": r.stderr[-500:]}))
