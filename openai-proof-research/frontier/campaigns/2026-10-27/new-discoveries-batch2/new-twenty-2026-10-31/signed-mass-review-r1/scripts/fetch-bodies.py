from pathlib import Path
import urllib.request,urllib.error,hashlib,json,datetime,sys
D=Path(__file__).resolve().parents[1]
for label,url in [
('constrained2016','https://arxiv.org/pdf/1602.05464'),
('constrained2020','https://www.viam.science.tsu.ge/publishing/proceedings/vol70/Giorgadze_Khiimshiashvili.pdf'),
('signed-line','https://arxiv.org/html/2608.28376'),
('harlow','https://www.mit.edu/~harlow/combinedlectures.pdf'),
('published-zahl','https://link.springer.com/article/10.1007/s00526-026-03270-z')]:
 if (D/'receipts'/(label+'.json')).exists():
  print('Existing receipt; no retry',label,flush=True);continue
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  r=urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical independent review'}),timeout=25); data=r.read();rec.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data));(D/'receipts'/label).write_bytes(data)
 except urllib.error.HTTPError as e:rec.update(status=e.code,error=str(e))
 except Exception as e:rec.update(error=str(e))
 (D/'receipts'/(label+'.json')).write_text(json.dumps(rec,indent=2));print(rec,flush=True)
