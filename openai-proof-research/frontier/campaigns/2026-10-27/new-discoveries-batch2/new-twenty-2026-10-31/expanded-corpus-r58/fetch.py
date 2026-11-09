from pathlib import Path
import requests,datetime,hashlib,json,subprocess,sys
O=Path(__file__).resolve().parent/'sources'; O.mkdir(exist_ok=True)
for name,url in [tuple(x.split('=',1)) for x in sys.argv[1:]]:
 p=O/(name+'.bin'); receipt={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  r=requests.get(url,timeout=22); p.write_bytes(r.content); receipt.update(status=r.status_code,final_url=r.url,sha256=hashlib.sha256(r.content).hexdigest(),bytes=len(r.content))
  if r.ok and r.content.startswith(b'%PDF'): subprocess.run(['pdftotext','-layout',str(p),str(O/(name+'.txt'))],timeout=12,check=True)
 except Exception as e: receipt['error']=str(e)
 (O/(name+'.receipt.json')).write_text(json.dumps(receipt,indent=2)+'\n'); print(name,receipt,flush=True)
