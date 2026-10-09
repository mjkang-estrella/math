from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import requests,hashlib,json,datetime
S=Path(__file__).resolve().parents[2]/'sources/i21_signed_saxl_dominance/literature';S.mkdir(exist_ok=True)
urls=[('bb-current','https://arxiv.org/abs/2202.03066'),('bb-v3','https://arxiv.org/html/2202.03066v3'),('bb-published','https://alco.centre-mersenne.org/articles/10.5802/alco.294/'),('ikenmeyer-current','https://arxiv.org/abs/1410.6549'),('ikenmeyer-v2','https://arxiv.org/pdf/1410.6549v2'),('bessenrodt-critical-current','https://arxiv.org/abs/1704.00707'),('bessenrodt-critical-published','https://alco.centre-mersenne.org/articles/10.5802/alco.19/')]
def get(x):
 name,url=x
 try:
  r=requests.get(url,timeout=45);r.raise_for_status();b=r.content;ext='.pdf' if b.startswith(b'%PDF') else '.html'; p=S/(name+ext);p.write_bytes(b)
  return dict(name=name,url=url,final_url=r.url,status=r.status_code,bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),file=p.name,retrieved=datetime.datetime.now(datetime.timezone.utc).isoformat())
 except Exception as ex:return dict(name=name,url=url,error=str(ex))
a=list(ThreadPoolExecutor(max_workers=5).map(get,urls));(S/'manifest.json').write_text(json.dumps(a,indent=2)+'\n');print(json.dumps(a,indent=2))
