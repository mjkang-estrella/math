from pathlib import Path
import urllib.request,urllib.error,json,hashlib,datetime,subprocess
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i80_geometric_flows_computation_discovery';P=S/'primary';P.mkdir(exist_ok=True)
items=[('stolarski-abs','https://arxiv.org/abs/1905.00087'),('stolarski-v1','https://arxiv.org/pdf/1905.00087v1'),('dgmp-abs','https://arxiv.org/abs/2507.07696'),('dgmp-latest','https://arxiv.org/pdf/2507.07696'),('bohm','https://www.numdam.org/item/10.24033/bsmf.2345.pdf')]
log=[]
for name,url in items:
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'Research-source-verification/1.0'});res=urllib.request.urlopen(req,timeout=45);b=res.read();status=res.status;final=res.url;headers=dict(res.headers)
 except urllib.error.HTTPError as e:b=e.read();status=e.code;final=e.url;headers=dict(e.headers)
 except Exception as e:log.append(dict(name=name,url=url,error=repr(e)));continue
 ext='.pdf' if b.startswith(b'%PDF') else '.html';p=P/(name+ext);p.write_bytes(b);row=dict(name=name,url=url,final_url=final,status=status,headers=headers,path=str(p.relative_to(R)),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),retrieved=datetime.datetime.now(datetime.timezone.utc).isoformat())
 if ext=='.pdf':
  txt=p.with_suffix('.txt');r=subprocess.run(['pdftotext','-layout',str(p),str(txt)],capture_output=True,text=True);row['conversion']=dict(command=['pdftotext','-layout'],returncode=r.returncode,stderr=r.stderr,text=str(txt.relative_to(R)),sha256=hashlib.sha256(txt.read_bytes()).hexdigest() if txt.exists() else None)
 log.append(row);print(name,status,len(b),flush=True)
(S/'primary-requests.json').write_text(json.dumps(log,indent=2)+'\n')
