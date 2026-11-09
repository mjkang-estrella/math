from pathlib import Path
import json,hashlib,urllib.request,urllib.error,subprocess,datetime,concurrent.futures
O=Path(__file__).resolve().parent
rows=json.loads((O/'assigned-records.json').read_text());(O/'sources').mkdir(exist_ok=True)
def one(x):
 r=x['record'];id=r['mathdb_id'];a=r['source_url'].rsplit('/',1)[-1];url='https://arxiv.org/pdf/'+a;p=O/'sources'/f'{id}.pdf';t=p.with_suffix('.txt'); d=dict(mathdb_id=id,url=url,requested_at=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'MathResearch/1.0 (primary source study)'})
  with urllib.request.urlopen(req,timeout=25) as f:z=f.read();d['final_url']=f.url;d['status']=f.status
  p.write_bytes(z);d['pdf']=dict(path=str(p),size=len(z),sha256=hashlib.sha256(z).hexdigest()); assert z.startswith(b'%PDF'), 'not PDF'
  # PDF bound in durable metadata before extraction; no content searches until index written.
  (O/'sources'/f'{id}.binding.json').write_text(json.dumps(d,indent=2)+'\n')
  subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True,timeout=20)
  z=t.read_bytes();d['text']=dict(path=str(t),size=len(z),sha256=hashlib.sha256(z).hexdigest());d['result']='retained'
 except Exception as e:d['result']='HOLD';d['error']=type(e).__name__+': '+str(e)
 (O/'sources'/f'{id}.binding.json').write_text(json.dumps(d,indent=2)+'\n');return d
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool: results=list(pool.map(one,rows))
(O/'source-bindings.json').write_text(json.dumps(results,indent=2)+'\n')
print([(d['mathdb_id'],d['result'],d.get('error')) for d in results])
