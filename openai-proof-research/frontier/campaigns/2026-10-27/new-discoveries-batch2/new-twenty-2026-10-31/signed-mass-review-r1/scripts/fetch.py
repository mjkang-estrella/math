from pathlib import Path
import urllib.request,urllib.error,hashlib,json,datetime,sys
D=Path(__file__).resolve().parents[1]
for label,url in [
('v1','https://arxiv.org/html/2504.09840v1'),
('v2','https://arxiv.org/html/2504.09840v2'),
('openai-head','https://api.github.com/repos/openai/math/commits/HEAD'),
('trureturing-head','https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD'),
('jones','https://citeseerx.ist.psu.edu/document?doi=fc2ab430fe42bd05e14fc4ad7ad7025b4c09e814&repid=rep1&type=pdf')]:
 if (D/'receipts'/(label+'.json')).exists():
  print('Existing receipt; no retry',label,flush=True);continue
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  r=urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical independent review'}),timeout=25); data=r.read();rec.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data));(D/'receipts'/label).write_bytes(data)
 except urllib.error.HTTPError as e:rec.update(status=e.code,error=str(e))
 except Exception as e:rec.update(error=str(e))
 (D/'receipts'/(label+'.json')).write_text(json.dumps(rec,indent=2));print(rec,flush=True)
