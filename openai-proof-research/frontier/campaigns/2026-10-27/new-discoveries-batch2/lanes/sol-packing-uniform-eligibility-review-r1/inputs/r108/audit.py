from pathlib import Path
import re,json,hashlib,datetime
L=Path(__file__).parent; R=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
t=re.compile(rb'2610.03785|2610.00498|star.forming|Sahbi|2610.29846|Blitvi|pattern.cover|moment.sequence',re.I)
n=0;nh=0
with (L/'duplicate-stream.jsonl').open('w') as out, (L/'duplicate-hits.jsonl').open('w') as hits:
 for p in R.rglob('*'):
  if not p.is_file() or L in p.parents:continue
  rel=str(p.relative_to(R)); low=rel.lower()
  if not (p.name.lower() in ['summary.md','discovery.md','findings.md','proof.md','ledger.json','next.md'] or p.name.startswith('SCREENED-OUT') or ('review' in low or 'tools/scripts/agent/openproblem' in low) and p.suffix.lower() in ['.md','.json','.txt','.lean','.tex','.yaml','.py']):continue
  h=hashlib.sha256();tail=b'';offset=0;ms=[]
  with p.open('rb') as f:
   for b in iter(lambda:f.read(65536),b''):
    h.update(b);c=tail+b
    for m in t.finditer(c):
     if len(ms)<15:ms.append({'offset':offset-len(tail)+m.start(),'text':c[max(0,m.start()-120):m.end()+240].decode(errors='replace')})
    tail=c[-512:];offset+=len(b)
  row={'path':rel,'bytes':offset,'sha256':h.hexdigest()};out.write(json.dumps(row)+'\n');n+=1
  if ms:row['matches']=ms;hits.write(json.dumps(row)+'\n');nh+=1
(L/'duplicate-summary.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':n,'hitfiles':nh,'regex':t.pattern.decode(),'scope':'all dates; reviewtree text, embedded SCREENED-OUT and agent/openproblem notes; term triage only'},indent=2));print(n,nh)
