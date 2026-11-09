"""Convert sources/*.pdf to sources/text/*.txt with pdftotext -layout (never overwrite).
Usage: pdftext.py LANE_DIR"""
import sys, pathlib, subprocess, hashlib
D = pathlib.Path(sys.argv[1]).resolve()
T = D / 'sources' / 'text'
T.mkdir(exist_ok=True)
for p in sorted((D / 'sources').glob('*.pdf')):
    out = T / (p.stem + '.txt')
    if out.exists():
        continue
    r = subprocess.run(['pdftotext', '-layout', str(p), str(out)], capture_output=True, timeout=60)
    print(p.name, r.returncode, out.stat().st_size if out.exists() else None,
          hashlib.sha256(out.read_bytes()).hexdigest() if out.exists() else None)
