import urllib.request,urllib.error,hashlib,json,datetime,concurrent.futures
from pathlib import Path
P=Path(__file__).resolve().parent

def fetch(pair):
 name,url=pair; now=datetime.datetime.now(datetime.timezone.utc).isoformat()
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'MathResearch/1.0'}),timeout=22) as r: data=r.read(15000000); status=r.status; final=r.url
 except urllib.error.HTTPError as e: data=e.read();status=e.code;final=e.url
 except Exception as e: data=str(e).encode();status='ERROR';final=url
 (P/(name+'.body')).write_bytes(data)
 receipt=dict(url=url,utc=now,status=status,final_url=final,bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
 (P/(name+'.receipt.json')).write_text(json.dumps(receipt,indent=2));return receipt
if __name__=='__main__':
 import sys
 pairs=json.loads(Path(sys.argv[1]).read_text())
 with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
  for r in ex.map(fetch,pairs):print(json.dumps(r))
