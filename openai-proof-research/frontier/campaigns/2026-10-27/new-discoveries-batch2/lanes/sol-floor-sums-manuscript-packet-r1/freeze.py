from pathlib import Path
import hashlib,json,shutil,tarfile
L=Path(__file__).resolve().parent; B=L.parent.parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
def freeze(p,rel):
 q=L/'frozen'/rel;q.parent.mkdir(parents=True,exist_ok=True)
 h=sha(p);shutil.copyfile(p,q);assert sha(q)==h==sha(p)
 rows.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=h))
for n in ['ledger.json','prior-campaign-context.json','AGENTS.md']:
 p=B/n; q=L/'administrative'/n;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
src=L.parent/'sol-floor-sums-dag-assembly-formal-r3'
for p in src.glob('*.tar.gz'):
 assert sha(p)=='17ba800adb3154f5c3929ef076c47b9d1f0adaace1576793faa4154ff19be13f'
 freeze(p,Path('input')/p.name)
for name in ['sol-floor-sums-dag-assembly-formal-r3','sol-floor-sums-full-formal-review-r4','sol-floor-sums-source-prior-review-r2','sol-floor-sums-source-formal-r1','sol-floor-sums-certificate-r2']:
 for p in (L.parent/name).iterdir():
  if p.is_file() and p.suffix in ['.md','.json','.py'] and p.stat().st_size<3000000:
   freeze(p,Path(name)/p.name)
(L/'bindings.json').write_text(json.dumps(rows,indent=2)+'\n')
print('frozen',len(rows));print('\n'.join(str(p.relative_to(L)) for p in (L/'frozen/input').iterdir()))
