import sys,subprocess,hashlib,json,datetime,pathlib
out=pathlib.Path(sys.argv[1]); out.mkdir(exist_ok=True)
rec=out/'receipts.json'; R=json.loads(rec.read_text()) if rec.exists() else []
for aid in sys.argv[2:]:
    url=f'https://export.arxiv.org/pdf/{aid}'
    fn=out/(aid.replace('/','_')+'.pdf')
    t=datetime.datetime.now(datetime.timezone.utc).isoformat()+'Z'
    r=subprocess.run(['curl','-sSL','-A','research-fetch/1.0 (mj.kang)','-o',str(fn),'-w','%{http_code}',url],capture_output=True,text=True)
    code=r.stdout.strip()
    h=hashlib.sha256(fn.read_bytes()).hexdigest() if fn.exists() else None
    subprocess.run(['pdftotext','-layout',str(fn),str(fn.with_suffix('.txt'))],capture_output=True)
    R.append({'arxiv':aid,'url':url,'http':code,'utc':t,'sha256':h,'bytes':fn.stat().st_size if fn.exists() else 0})
    print(aid,code,h)
rec.write_text(json.dumps(R,indent=1))
