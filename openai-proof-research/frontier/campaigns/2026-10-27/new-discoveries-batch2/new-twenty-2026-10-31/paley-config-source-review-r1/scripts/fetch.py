# usage: python3 -I fetch.py URL OUTFILE  -> appends receipt to logs/http-receipts.jsonl ; no retries
import sys,hashlib,json,datetime,urllib.request,urllib.error,os
url,out=sys.argv[1],sys.argv[2]
rec={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url,'file':out}
req=urllib.request.Request(url,headers={'User-Agent':'Mozilla/5.0 (research review; single request, no retry)','Accept':'*/*'})
try:
    with urllib.request.urlopen(req,timeout=60) as r:
        data=r.read(60_000_000); rec['status']=r.status; rec['final_url']=r.geturl(); rec['content_type']=r.headers.get('Content-Type')
        open(out,'wb').write(data); rec['bytes']=len(data); rec['sha256']=hashlib.sha256(data).hexdigest()
except urllib.error.HTTPError as e:
    rec['status']=e.code; rec['error']=str(e)
except Exception as e:
    rec['status']=None; rec['error']=repr(e)
os.makedirs('logs',exist_ok=True)
open('logs/http-receipts.jsonl','a').write(json.dumps(rec)+'\n'); print(json.dumps(rec))
