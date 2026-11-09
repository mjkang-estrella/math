import pathlib,requests,json,hashlib,datetime,sys
D=pathlib.Path(__file__).resolve().parent; S=D/'sources';S.mkdir(exist_ok=True)
jobs=[('openai-head.json','https://api.github.com/repos/OpenAI/math/commits/HEAD'),('omega-head.json','https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD')]+[(a+'.pdf','https://arxiv.org/pdf/'+a) for a in sys.argv[1:]]
rs=[]
for name,url in jobs:
 try:
  r=requests.get(url,timeout=24);b=r.content;(S/name).write_bytes(b);o={'url':url,'status':r.status_code,'sha256':hashlib.sha256(b).hexdigest(),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':name,'bytes':len(b)}
  if name.endswith('head.json') and r.ok:o['head']=r.json()['sha']
  if name.endswith('.pdf') and b.startswith(b'%PDF'):
   import subprocess
   subprocess.run(['pdftotext','-layout',str(S/name),str(S/name.replace('.pdf','.txt'))],check=True)
 except Exception as e:o={'url':url,'error':str(e),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 rs.append(o);print(o,flush=True)
with open(D/'receipts.jsonl','a') as f:
 for o in rs:f.write(json.dumps(o)+'\n')
