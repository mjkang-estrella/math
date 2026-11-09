# sha256 manifest of every lane file (excluding the manifest itself and __pycache__).
import hashlib, json, pathlib, sys, datetime
D = pathlib.Path(sys.argv[1]); out = {}
for p in sorted(D.rglob('*')):
    if p.is_file() and '__pycache__' not in p.parts and p.name != 'MANIFEST.json':
        out[str(p.relative_to(D))] = dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(), bytes=p.stat().st_size)
(D / 'MANIFEST.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), files=out), indent=1) + '\n')
print(len(out), 'files')
