from pathlib import Path
import subprocess,json,re,hashlib
O=Path(__file__).resolve().parent;ROOT=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns');r=json.loads((O/'records.json').read_text());args=['rg','-l','-F']
for i,x in r.items():args+=['-e',i,'-e',x['title']]
args+=['--glob','*.json','--glob','*.md','--glob','*.txt','--glob','!reservation.json','--glob','!**/corpus/**','--glob','!**/sources/**','--glob','!**/raw/**','--glob','!**/deps/**','--glob','!**/literal-records.json','--glob','!**/records.json',str(ROOT)]
p=subprocess.run(args,capture_output=True,text=True,timeout=100);rows=[]
for name in p.stdout.splitlines():
 q=Path(name)
 if O in q.parents:continue
 t=q.read_text(errors='replace');matches=[]
 for i,x in r.items():
  m=re.search(r'(?<![\d.])'+i+r'(?!\d)',t)
  if x['title'] in t or m:
   pos=m.start() if m else t.index(x['title']);matches.append({'id':i,'context':t[max(0,pos-150):pos+240]})
 if matches:rows.append({'path':name,'sha256':hashlib.sha256(q.read_bytes()).hexdigest(),'matches':matches})
(O/'history-extended.json').write_text(json.dumps({'command':args,'returncode':p.returncode,'stderr':p.stderr,'files':rows},indent=2,ensure_ascii=False)+'\n');print(json.dumps(rows,ensure_ascii=False,indent=2))
