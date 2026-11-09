from pathlib import Path
import hashlib,json,shutil
L=Path(__file__).resolve().parent
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
rows=json.loads((L/'freeze.json').read_text());C=L.parent/'sol-floor-sums-certificate-r2';R=L.parent/'sol-floor-sums-certificate-formal-r2'
sources=[C/'frozen/sources/wong-current.txt',C/'frozen/sources/pong11.txt',C/'inspect.py',C/'mapping.py']
sources += [R/p.name for p in (L/'frozen/extra').glob('*.log')]
for f in sources:
 d=L/'frozen/extra'/f.name;h=sha(f)
 if not d.exists():shutil.copyfile(f,d)
 assert sha(f)==h==sha(d)
 rows.append(dict(original=str(f),copy=str(d.relative_to(L)),sha256=h))
(L/'freeze.json').write_text(json.dumps(rows,indent=2)+'\n')
print('streaming frozen',len(sources))
