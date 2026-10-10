"""One-time evidence acquisition; not called by verifier."""
from pathlib import Path
import requests,json,hashlib,datetime,subprocess,concurrent.futures
R=Path(__file__).resolve().parents[3]; S=R/'frontier/sources/i39_quantum_spectral_discovery'; L=S/'literature';L.mkdir(exist_ok=True)
items={'tasaki':'2407.17041','indices':'2609.34119','moon':'1804.04750','michalakis':'1109.1588','local':'1501.04571','ge-eisert':'1411.2995','sk-wpi':'2607.08160'}
def get(item):
 name,url=item;dest=L/name
 if dest.exists():raise RuntimeError('Refuse overwrite '+str(dest))
 row={'name':name,'url':url,'requested_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  r=requests.get(url,timeout=45);dest.write_bytes(r.content);row.update(status=r.status_code,final_url=r.url,headers=dict(r.headers),bytes=len(r.content),sha256=hashlib.sha256(r.content).hexdigest())
  if r.content.startswith(b'%PDF'):
   subprocess.run(['pdftotext','-layout',str(dest),str(dest)+'.txt'],check=True);row['text']=name+'.txt'
 except Exception as e:row['error']=repr(e)
 (L/(name+'.response.json')).write_text(json.dumps(row,indent=2));return row
if __name__=='__main__':
 tasks=[(k+'-current.html','https://arxiv.org/abs/'+v) for k,v in items.items()]
 with concurrent.futures.ThreadPoolExecutor(max_workers=7) as e:
  for x in e.map(get,tasks):print(x['name'],x.get('status'),x.get('error'))
