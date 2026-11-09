from pathlib import Path
import requests,json,hashlib,datetime
R=Path(__file__).resolve().parents[1];(R/'sources').mkdir(exist_ok=True)
urls={str(n):'https://arxiv.org/pdf/'+a for n,a in [(327375,'1402.7158'),(327422,'1403.1845'),(333447,'1606.07597'),(337098,'1709.06187'),('lu','1803.08653')]}
out=json.loads((R/'source-provenance.json').read_text())
for name,url in urls.items():
 e={'key':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  q=requests.get(url,timeout=22);b=q.content;e.update(status=q.status_code,final_url=q.url,sha256=hashlib.sha256(b).hexdigest(),size=len(b),version='URL as retrieved; PDF metadata/version not yet audited')
  p=R/'sources'/(name+('.pdf' if b.startswith(b'%PDF') else '.response'));p.write_bytes(b);e['path']=str(p.relative_to(R))
  challenge=any(s in b[:200000].lower() for s in [b'proof-of-work',b'verify you are human',b'captcha',b'cf-chl-',b'javascript challenge',b'anubis'])
  e['usable']=q.status_code==200 and not challenge;e['challenge']=challenge
 except Exception as ex:e['error']=str(ex);e['usable']=False
 out.append(e);(R/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n');print(name,e.get('status'),e.get('usable'),flush=True)
