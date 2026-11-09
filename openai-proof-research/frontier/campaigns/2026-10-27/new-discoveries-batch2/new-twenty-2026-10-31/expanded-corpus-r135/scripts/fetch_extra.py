import urllib.request,json,hashlib,pathlib,datetime,subprocess,sys
D=pathlib.Path(__file__).resolve().parents[1]
name,url=sys.argv[1],sys.argv[2]
rp=D/'sources/receipts-extra.json'; rec=json.loads(rp.read_text()) if rp.exists() else []
r={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
try:
 with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source verification'}),timeout=25) as f:
  b=f.read(); r.update(status=f.status,final_url=f.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),ctype=f.headers.get('content-type'))
 ext='.pdf' if b.startswith(b'%PDF') else '.html'
 p=D/'sources'/(name+ext); p.write_bytes(b); r['saved']=p.name
 if ext=='.pdf': subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
except Exception as e: r['error']=str(e)
rec.append(r); rp.write_text(json.dumps(rec,indent=2)+'\n'); print(r)
