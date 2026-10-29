from pathlib import Path
import hashlib,json,re,datetime
L=Path(__file__).parent;R=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research');terms=re.compile(rb'boxed.mesh|2609.13764|bruhat.{0,30}degree|degree.{0,30}bruhat|strict.interleav|heilbronn|sudermann|critical.triangles',re.I)
count=0;hitfiles=[]
with (L/'duplicate-expanded.jsonl').open('w') as out:
 for p in R.rglob('*'):
  if not p.is_file() or L in p.parents:continue
  rel=str(p.relative_to(R))
  if not (p.name.lower() in ['summary.md','discovery.md','findings.md','proof.md','ledger.json','next.md'] or 'review' in rel.lower() and p.suffix.lower() in ['.md','.json','.txt']):continue
  h=hashlib.sha256();hits=[];tail=b'';offset=0
  with p.open('rb') as f:
   while True:
    b=f.read(65536)
    if not b:break
    h.update(b);c=tail+b
    for m in terms.finditer(c):
     if len(hits)<12:hits.append({'offset':offset-len(tail)+m.start(),'context':c[max(0,m.start()-150):m.end()+200].decode(errors='replace')})
    tail=c[-512:];offset+=len(b)
  count+=1;row={'path':rel,'bytes':offset,'sha256':h.hexdigest(),'hits':hits};out.write(json.dumps(row)+'\n')
  if hits:hitfiles.append({'path':rel,'hits':hits})
(L/'duplicate-expanded-summary.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':count,'terms':terms.pattern.decode(),'hit_files':hitfiles,'limit':'all selected files streamed in entirety; displayed contexts capped at12 per file'},indent=2));print('FILES',count,'HITFILES',len(hitfiles));print(json.dumps(hitfiles)[:22000])
