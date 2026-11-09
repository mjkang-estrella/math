import sys,urllib.request,hashlib,json,datetime,pathlib
url,dest=sys.argv[1],pathlib.Path(sys.argv[2])
rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':str(dest)}
try:
    req=urllib.request.Request(url,headers={'User-Agent':'research-fetch/1.0'})
    with urllib.request.urlopen(req,timeout=25) as f: data=f.read(); rec.update(status=f.status,final_url=f.url)
    dest.write_bytes(data); rec.update(sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
except Exception as e: rec['error']=repr(e)[:300]
print(json.dumps(rec))
with open(pathlib.Path(__file__).resolve().parents[1]/'outputs/http.jsonl','a') as fh: fh.write(json.dumps(rec)+'\n')
