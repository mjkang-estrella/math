from pathlib import Path
import urllib.request,datetime,hashlib,json,sys
D=Path(__file__).resolve().parents[1]
def fetch(name,url):
 receipt={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'retry':False}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical source verification (public read-only)'}),timeout=35) as r:
   data=r.read(30*1024*1024);receipt.update(status=r.status,final_url=r.url,headers=dict(r.headers));(D/'sources'/name).write_bytes(data);receipt.update(sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
 except Exception as e:receipt['error']=str(e)
 (D/'receipts'/(name+'.json')).write_text(json.dumps(receipt,indent=2));print(name,receipt.get('status'),receipt.get('error',''))
if __name__=='__main__':fetch(*sys.argv[1:])
