from pathlib import Path
import requests,json,hashlib,datetime
R=Path(__file__).resolve().parents[1];(R/'sources').mkdir(exist_ok=True)
urls={'wow100':'http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html','wow133':'https://cms.dt.uh.edu/faculty/delavinae/research/wowII/'}
for n,a in [(318661,'0906.3529'),(320851,'1012.3127'),(321668,'1106.0631'),(325282,'1304.0873'),(326185,'1308.5412'),(326508,'1310.3426'),(327330,'1402.4981'),(327375,'1402.4356'),(328554,'1408.2398'),(329290,'1411.6138'),(334049,'1609.04195'),(340501,'1809.08594'),(341325,'1812.04052'),(341738,'1901.11339'),(343315,'1907.09797')]:urls[str(n)]='https://arxiv.org/pdf/'+a
out=[]
for name,url in urls.items():
 e={'key':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  q=requests.get(url,timeout=22);b=q.content;e.update(status=q.status_code,final_url=q.url,sha256=hashlib.sha256(b).hexdigest(),size=len(b),version='URL as retrieved; PDF metadata/version not yet audited')
  p=R/'sources'/(name+('.pdf' if b.startswith(b'%PDF') else '.response'));p.write_bytes(b);e['path']=str(p.relative_to(R))
  challenge=any(s in b[:200000].lower() for s in [b'proof-of-work',b'verify you are human',b'captcha',b'cf-chl-',b'javascript challenge',b'anubis'])
  e['usable']=q.status_code==200 and not challenge;e['challenge']=challenge
 except Exception as ex:e['error']=str(ex);e['usable']=False
 out.append(e);(R/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n');print(name,e.get('status'),e.get('usable'),flush=True)
