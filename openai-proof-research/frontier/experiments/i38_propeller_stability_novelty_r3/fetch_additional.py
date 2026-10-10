from pathlib import Path
import requests,json,re,hashlib,datetime,subprocess
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i38_propeller_stability_novelty_r3/literature'
out=[]
def fetch(name,url):
 r=requests.get(url,timeout=45);b=r.content;(S/name).write_bytes(b)
 out.append(dict(name=name,request={'method':'GET','url':url},retrieved_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status=r.status_code,final_url=r.url,headers=dict(r.headers),bytes=len(b),sha256=hashlib.sha256(b).hexdigest()))
 if b.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(S/name),str(S/Path(name).with_suffix('.txt'))],check=True)
 return r.text
for name,id in [('levrard','1801.03742'),('legouic-paris','1801.09419')]:
 html=fetch(name+'-current.html','https://arxiv.org/abs/'+id)
 vs=re.findall(r'\[v(\d+)\]',html);version=max(map(int,vs))
 fetch(name+'-v'+str(version)+'.pdf','https://arxiv.org/pdf/'+id+'v'+str(version))
(S/'additional-manifest.json').write_text(json.dumps(out,indent=2)+'\n');print([(x['name'],x['status']) for x in out])
