from pathlib import Path
import urllib.request, urllib.error, json, hashlib, datetime, sys
out=Path(__file__).resolve().parents[1]/'prior'
def fetch(url,name):
 receipt={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'mathematical-prior-art-research'}),timeout=30) as r:
   b=r.read(); receipt.update(status=r.status,final_url=r.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()); (out/name).write_bytes(b)
 except Exception as e: receipt['error']=str(e)
 (out/(name+'.receipt.json')).write_text(json.dumps(receipt,indent=2)); print(receipt,flush=True)
 return json.loads((out/name).read_text()) if 'sha256' in receipt and name.endswith('.json') else None
if __name__=='__main__': fetch(sys.argv[1],sys.argv[2])
