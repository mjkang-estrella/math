from pathlib import Path
import requests,hashlib,json,datetime,sys
r=Path(__file__).resolve().parent
for name,u in zip(sys.argv[1::2],sys.argv[2::2]):
 try:
  x=requests.get(u,timeout=15); (r/(name+'.body')).write_bytes(x.content); d={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':u,'final_url':x.url,'status':x.status_code,'file':name+'.body','sha256':hashlib.sha256(x.content).hexdigest()}; print(name,x.status_code,len(x.content),flush=True)
 except Exception as e: d={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':u,'error':str(e)}; print(name,str(e),flush=True)
 with (r/'http-receipts.jsonl').open('a') as f:f.write(json.dumps(d)+'\n')
