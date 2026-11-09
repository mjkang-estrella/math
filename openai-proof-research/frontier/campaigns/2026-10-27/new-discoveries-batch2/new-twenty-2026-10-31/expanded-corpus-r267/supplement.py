exec(open(__file__.replace('supplement.py','fetch.py')).read().split('d=json.loads')[0])
import os
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
jobs=[('378613-later','https://arxiv.org/pdf/2002.11205'),('registry-omega','https://raw.githubusercontent.com/the-omega-institute/trureturing/HEAD/README.md'),('registry-pool','https://raw.githubusercontent.com/Vilin97/lean-pool/HEAD/LeanPool/projects.yml'),('registry-openai','https://raw.githubusercontent.com/openai/math/HEAD/CONTENTS.md')]
for name,url in jobs:
 r=dict(name=name,url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  z=requests.get(url,timeout=9);r.update(status=z.status_code,bytes=len(z.content),sha256=hashlib.sha256(z.content).hexdigest());f=p/'sources'/(name+('.pdf' if name=='378613-later' else '.txt'));f.write_bytes(z.content);r['file']=str(f)
  if z.content.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(f),str(f.with_suffix('.txt'))],timeout=12,check=True)
 except Exception as e:r['error']=str(e)
 with (p/'receipts.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
 print(r,flush=True)
