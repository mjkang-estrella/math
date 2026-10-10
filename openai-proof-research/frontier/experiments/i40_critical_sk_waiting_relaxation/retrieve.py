"""One-time immutable HTTP acquisition; no overwrites."""
from pathlib import Path
import urllib.request,urllib.error,json,hashlib,re,datetime,subprocess
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i40_critical_sk_waiting_relaxation';D=S/'literature';D.mkdir(exist_ok=True)
assert not (S/'artifact-seal.json').exists()
def get(name,url):
 p=D/name;assert not p.exists()
 req=urllib.request.Request(url,headers={'User-Agent':'research-evidence/1.0'})
 record={'name':name,'url':url,'requested_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(req,timeout=45) as resp:
   body=resp.read();record.update(status=resp.status,final_url=resp.url,headers=dict(resp.headers))
 except Exception as e:
  body=str(e).encode();record.update(status=None,error=repr(e))
 p.write_bytes(body);record.update(bytes=len(body),sha256=hashlib.sha256(body).hexdigest());(D/(name+'.response.json')).write_text(json.dumps(record,indent=2)+'\n');print(name,record['status'],len(body),flush=True)
 return body,record
versions=[]
for name,ident in [('langevin','1911.08001'),('diffusions','2006.13167'),('wang','2608.22159'),('billoire','1105.1902'),('chatterjee','math/0508213')]:
 body,rec=get(name+'-current.html','https://arxiv.org/abs/'+ident)
 vs=re.findall(rb'\[v(\d+)\]',body)
 if rec['status']==200 and vs:
  v=max(map(int,vs));versions.append({'name':name,'id':ident,'version':v});pdf,rr=get(name+'-v'+str(v)+'.pdf','https://arxiv.org/pdf/'+ident+'v'+str(v))
  if rr['status']==200:
   out=subprocess.run(['pdftotext','-layout',str(D/rr['name']),str(D/(rr['name']+'.txt'))],capture_output=True,text=True)
   (D/(rr['name']+'.pdftotext.json')).write_text(json.dumps({'returncode':out.returncode,'stdout':out.stdout,'stderr':out.stderr},indent=2)+'\n')
(S/'literature/versions.json').write_text(json.dumps(versions,indent=2)+'\n')
rows=json.loads((S/'selected-pinned.json').read_text())
for ending in ['04-warming.tex','05-gaussian-limits.tex','09-replacement.tex','06-microscopic.tex','05-gradient.tex','cap-entropy.tex','introduction.tex']:
 hits=[r for r in rows if r['path'].endswith('/'+ending)]
 row=hits[0];body,rr=get('pinned-'+ending,row['url'])
 if rr['status']==200:assert hashlib.sha256(body).hexdigest()==row['sha256']
