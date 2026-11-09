from pathlib import Path
import hashlib,zipfile,json
R=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/percolation-formal-r5')
a=(R.parent/'percolation-formal-r4/source-only.zip').read_bytes()
assert hashlib.sha256(a).hexdigest()=='9d25c3347aad2ca49799def30fb28e3fac171c6b680369f7f23046e0db38731e'
(R/'inherited-source.zip').write_bytes(a)
with zipfile.ZipFile(R/'inherited-source.zip') as z:
 assert all(not Path(n).is_absolute() and '..' not in Path(n).parts for n in z.namelist())
 z.extractall(R/'packet')
 manifest={n:hashlib.sha256(z.read(n)).hexdigest() for n in z.namelist() if n.startswith('src/')}
assert len(manifest)==443
(R/'inherited-source-comparison.json').write_text(json.dumps(manifest,indent=2))
(R/'normalized-progress.json').write_text((R.parent/'percolation-formal-r4/normalized-progress.json').read_text())
for name in ['normalized.cnf','normalized-trimmed.json']:
 src=R.parent/'percolation-formal-r3'/name
 assert hashlib.sha256(src.read_bytes()).digest()==hashlib.sha256((R/'packet'/name).read_bytes()).digest()
print('Safely extracted and hash-checked 443 inherited sources and both certificates.')
