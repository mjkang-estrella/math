from pathlib import Path
import hashlib,json,shutil
L=Path(__file__).resolve().parent
B=L.parent.parent
rows=[]
for lane in ['sol-floor-sums-certificate-formal-r2','sol-floor-sums-source-formal-r1','sol-floor-sums-certificate-r2','sol-floor-sums-certificate-preliminary-review-r1']:
 p=L.parent/lane
 for f in sorted(p.iterdir()):
  if f.is_file() and (f.suffix in ['.md','.py','.json','.sh','.lean','.gz'] or f.name=='run.sh'):
   if f.name.endswith('.log.gz'):continue
   data=f.read_bytes();h=hashlib.sha256(data).hexdigest()
   dest=L/'frozen'/lane/f.name;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
   assert hashlib.sha256(f.read_bytes()).hexdigest()==h==hashlib.sha256(dest.read_bytes()).hexdigest()
   rows.append(dict(original=str(f),copy=str(dest.relative_to(L)),sha256=h))
for name in ['AGENTS.md','ledger.json','prior-campaign-context.json']:
 dest=L/'administrative'/name;dest.parent.mkdir(exist_ok=True);shutil.copyfile(B/name,dest)
(L/'freeze.json').write_text(json.dumps(rows,indent=2)+'\n')
print('frozen',len(rows))
