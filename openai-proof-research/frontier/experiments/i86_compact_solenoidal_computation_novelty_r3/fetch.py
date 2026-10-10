import json,pathlib,hashlib,datetime,urllib.request,urllib.error,concurrent.futures,subprocess
R=pathlib.Path(__file__).resolve().parents[3];S=R/'frontier/sources/i86_compact_solenoidal_computation_novelty_r3';P=S/'primary';P.mkdir(exist_ok=True)
old=R/'frontier/sources/i80_geometric_flows_computation_discovery'
req=[]
for n in ['primary-requests.json','primary-more-requests.json']:
 for x in json.loads((old/n).read_text()):
  if x['name'] not in ['stolarski-abs','stolarski-v1','bohm']:req.append(x)
# Refresh current version PDFs as well as fixed prior-version URLs.
for name,id in [('beltrami','2111.03559'),('gavrilov','1810.08020'),('clv','1903.11699')]:req.append({'name':name+'-current','url':'https://arxiv.org/pdf/'+id})
def fetch(x):
 d={'name':x['name'],'url':x['url'],'started':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  try:r=urllib.request.urlopen(urllib.request.Request(x['url'],headers={'User-Agent':'I86 independent mathematics comparison'}),timeout=35)
  except urllib.error.HTTPError as e:r=e
  b=r.read();d.update(status=r.status,final_url=r.url,headers=dict(r.headers),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
  # Reuse exact immutable bytes, retaining fresh HTTP envelope.
  if x.get('sha256')==d['sha256']:d['path']=x['path'];d['reused']=True
  else:
   p=P/(x['name']+('.pdf' if b.startswith(b'%PDF') else '.html'));p.write_bytes(b);d['path']=str(p.relative_to(R));d['reused']=False
  if b.startswith(b'%PDF'):
   if d['reused'] and 'conversion' in x:d['conversion']=x['conversion']
   else:
    out=P/(x['name']+'.txt');c=subprocess.run(['pdftotext','-layout',str(R/d['path']),str(out)],capture_output=True);d['conversion']={'text':str(out.relative_to(R)),'sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'returncode':c.returncode,'stderr':c.stderr.decode()}
 except Exception as e:d['error']=repr(e)
 d['finished']=datetime.datetime.now(datetime.timezone.utc).isoformat();return d
with concurrent.futures.ThreadPoolExecutor(max_workers=5) as ex:out=list(ex.map(fetch,req))
(S/'primary-responses.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps([{k:v for k,v in d.items() if k in ['name','status','error','reused','path']} for d in out],indent=2))
