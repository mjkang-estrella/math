import subprocess,hashlib,json,datetime,pathlib,sys
out=pathlib.Path(sys.argv[1]); out.mkdir(exist_ok=True)
reqs=[(n,u) for n,u in (a.split('=',1) for a in sys.argv[2:])]
rec=out/'receipts.json'; R=json.loads(rec.read_text()) if rec.exists() else []
for name,url in reqs:
    f=out/(name+'.body'); t=datetime.datetime.now(datetime.timezone.utc).isoformat()
    r=subprocess.run(['curl','-sS','-L','-A','research-fetch/1.0','-o',str(f),'-w','%{http_code}',url],capture_output=True,text=True)
    h=hashlib.sha256(f.read_bytes()).hexdigest() if f.exists() else None
    R.append({'name':name,'url':url,'utc':t,'http':r.stdout,'sha256':h,'bytes':f.stat().st_size if f.exists() else 0,'note':'single request, not retried'})
    print(name,r.stdout,h)
rec.write_text(json.dumps(R,indent=1))
