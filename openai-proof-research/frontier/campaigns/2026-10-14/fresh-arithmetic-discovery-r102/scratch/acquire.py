from pathlib import Path
import json,hashlib,urllib.request,concurrent.futures,datetime
R=Path(__file__).resolve().parents[1]; project=R.parents[3]
t=json.loads((project/'sources/preprints-tree.json').read_text())
keys=['Reconstruction-from-Milnor-K-theory-modulo-the-characteristic','Reconstruction-of-Function-Fields-from-Mod-ell-Milnor-K-Theory','The-Bogomolov-Pop-reconstruction-theorem']
a=[x for x in t['tree'] if x['type']=='blob' and x['path'].endswith(('.tex','.bib')) and any(k in x['path'] for k in keys)]
def one(x):
 url='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+x['path'];o={'path':x['path'],'url':url,'expected_blob':x['sha'],'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=40) as res:b=res.read();o['final_url']=res.url
  h=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert h==x['sha'];assert len(b)==x['size'];p=R/'private/acquisitions'/x['path'];p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
  o.update(sha256=hashlib.sha256(b).hexdigest(),git_blob=h,bytes=len(b),local=str(p.relative_to(R)),lines=len(b.splitlines()),status='authenticated')
 except Exception as e:o.update(status='failure',error=str(e))
 return o
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as e:out=list(e.map(one,a))
(R/'private/acquisitions/register.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps([{'path':x['path'],'status':x['status'],'lines':x.get('lines'),'error':x.get('error')} for x in out],indent=2))
