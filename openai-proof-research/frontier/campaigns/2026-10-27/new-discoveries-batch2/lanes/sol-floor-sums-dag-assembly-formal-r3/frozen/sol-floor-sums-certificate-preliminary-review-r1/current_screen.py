from pathlib import Path
import urllib.request,urllib.parse,hashlib,json,datetime,xml.etree.ElementTree as ET
L=Path(__file__).resolve().parent;D=L/'current';D.mkdir(exist_ok=True)
out=[]
for i,q in enumerate(['ti:"Curious Bounds for Floor Function Sums"','all:Jacobsthal AND all:floor AND (all:bound OR all:conjecture)']):
 url='https://export.arxiv.org/api/query?'+urllib.parse.urlencode({'search_query':q,'max_results':15,'sortBy':'lastUpdatedDate','sortOrder':'descending'})
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'query':q}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'MathematicalCertificateReview/1.0'}),timeout=20) as response:
   r['status']=response.status;body=response.read(1500001);assert len(body)<=1500000
  p=D/f'{i}.xml';p.write_bytes(body);r['sha256']=hashlib.sha256(body).hexdigest();assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256']
  assert not any(t in body[:10000].lower() for t in [b'captcha',b'challenge-platform'])
  root=ET.fromstring(p.read_bytes());ns={'a':'http://www.w3.org/2005/Atom'}
  r['entries']=[{k:e.findtext('a:'+k,namespaces=ns) for k in ['id','title','published','updated','summary']} for e in root.findall('a:entry',ns)]
 except Exception as e:r['failure']=repr(e)
 out.append(r)
 if r.get('status') in [403,429] or 'challenge' in r.get('failure','').lower():break
(L/'current-screen.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
