"""Write outputs/artifact-hashes.json: sha256 of every file under sources/, scripts/, logs/, outputs/ (except
itself) plus all fetch receipts (url, status, utc).  Usage: finalize_hashes.py LANE_DIR OUTNAME"""
import sys, pathlib, hashlib, json
D = pathlib.Path(sys.argv[1]).resolve(); out = D / 'outputs' / sys.argv[2]
files = {}
for sub in ('sources', 'scripts', 'logs', 'outputs', 'lean-draft', 'raw'):
    for p in sorted((D / sub).rglob('*')) if (D / sub).exists() else []:
        if p.is_file() and p != out:
            files[str(p.relative_to(D))] = {'sha256': hashlib.sha256(p.read_bytes()).hexdigest(), 'bytes': p.stat().st_size}
receipts = {}
for p in sorted((D / 'sources').glob('*.receipt.json')):
    r = json.loads(p.read_text())
    receipts[p.name] = {k: r.get(k) for k in ('url', 'utc', 'status', 'final_url', 'sha256', 'bytes', 'error', 'challenge')}
with open(out, 'x') as f:
    json.dump({'files': files, 'receipts': receipts}, f, indent=1)
print('files', len(files), 'receipts', len(receipts))
