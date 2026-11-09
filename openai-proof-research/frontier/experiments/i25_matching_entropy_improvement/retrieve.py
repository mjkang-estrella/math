from pathlib import Path
import urllib.request,hashlib,json,datetime,subprocess
s=Path('frontier/sources/i25_matching_entropy_improvement');out=s/'literature';out.mkdir(exist_ok=True)
papers=[('gurvits','1106.2844v11'),('cube-ideal','2505.14497v1'),('entropy-optimization','1304.8108v1'),('girth-bethe','2609.02017v1'),('dong-jain','2609.11049v1')]
manifest=[]
for name,v in papers:
 for typ in ['abs','pdf']:
  url=f'https://arxiv.org/{typ}/{v}';p=out/(name+('.html' if typ=='abs' else '.pdf'))
  try:
   with urllib.request.urlopen(url,timeout=45) as r:b=r.read();final=r.url
   p.write_bytes(b);manifest.append(dict(name=name,version=v,url=url,final_url=final,path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),retrieved_utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))
   if typ=='pdf':
    q=p.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(p),str(q)],check=True);bb=q.read_bytes();manifest.append(dict(name=name,derived_from=str(p),path=str(q),bytes=len(bb),sha256=hashlib.sha256(bb).hexdigest()))
   print(name,typ,len(b),flush=True)
  except Exception as exc:manifest.append(dict(name=name,url=url,error=str(exc)));print(name,typ,str(exc),flush=True)
 (out/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
