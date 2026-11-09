import json,hashlib,sys,time,urllib.request,datetime,pathlib,subprocess
D=pathlib.Path(__file__).resolve().parents[1]
def get(url,dest):
    rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
    try:
        req=urllib.request.Request(url,headers={'User-Agent':'research-fetch/1.0'})
        with urllib.request.urlopen(req,timeout=40) as r:
            b=r.read(); rec.update(status=r.status,final_url=r.geturl(),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
            dest.write_bytes(b)
    except urllib.error.HTTPError as e: rec.update(status=e.code,error=str(e))
    except Exception as e: rec.update(status=None,error=repr(e))
    pathlib.Path(str(dest)+'.receipt.json').write_text(json.dumps(rec,indent=2)+'\n'); print(json.dumps(rec)); return rec
for spec in sys.argv[1:]:
    name,url=spec.split('=',1)
    r=get(url,D/'sources'/name)
    if r.get('status')==200 and name.endswith('.pdf'):
        subprocess.run(['pdftotext','-layout',str(D/'sources'/name),str(D/'sources'/(name[:-4]+'.txt'))],timeout=60)
    if r.get('status') in (403,429): print('STOP on',r['status']); break
    time.sleep(3)
