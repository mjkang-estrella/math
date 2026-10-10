"""One-time evidence fetch. Never rerun after sealing."""
from pathlib import Path
import urllib.request,urllib.error,hashlib,json,datetime,subprocess,re
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i41_rademacher_fair_start_warming';D=S/'literature'
assert not (S/'artifact-seal.json').exists()
def get(name,url):
 assert not (D/name).exists()
 r={'name':name,'url':url,'requested_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-source-verification/1.0'}),timeout=45) as f:
   b=f.read();r.update(status=f.status,final_url=f.url,headers=dict(f.headers))
 except urllib.error.HTTPError as e:
  b=e.read();r.update(status=e.code,error=str(e))
 except Exception as e:
  b=str(e).encode();r.update(status=None,error=str(e))
 (D/name).write_bytes(b);r.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest());(D/(name+'.response.json')).write_text(json.dumps(r,indent=2)+'\n')
 if name.endswith('.pdf') and b.startswith(b'%PDF-'):
  z=subprocess.run(['pdftotext','-layout',str(D/name),str(D/(name+'.txt'))],capture_output=True,text=True)
  (D/(name+'.pdftotext.json')).write_text(json.dumps({'returncode':z.returncode,'stderr':z.stderr},indent=2)+'\n')
 print(name,r['status'],len(b),flush=True)
versions=[{'name':'pei','id':'2609.14273','version':1},{'name':'asl','id':'2607.08160','version':1},{'name':'duhuang','id':'2607.02172','version':2},{'name':'diffusions','id':'2006.13167','version':2},{'name':'chatterjee','id':'math/0508519','version':3}]
for v in versions:
 get(v['name']+'-current.html','https://arxiv.org/abs/'+v['id'])
 get(v['name']+'-v'+str(v['version'])+'.pdf','https://arxiv.org/pdf/'+v['id']+'v'+str(v['version']))
(D/'versions.json').write_text(json.dumps(versions,indent=2)+'\n')
selected=json.loads((S/'selected-pinned.json').read_text())
for ending in ['04-warming.tex','05-gaussian-limits.tex','07-history-cutoffs.tex','08-clock-scores.tex','09-replacement.tex','05-gradient.tex','06-microscopic.tex']:
 row=next(x for x in selected if x['path'].endswith('/'+ending));get('pinned-'+ending,row['url'])
