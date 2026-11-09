import urllib.request,pathlib,json,datetime,hashlib,subprocess,sys
D=pathlib.Path(__file__).resolve().parents[1];name,url=sys.argv[1:];r={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
try:
 with urllib.request.urlopen(url,timeout=20) as f:b=f.read();r['status']=f.status
 p=D/'sources'/name;p.write_bytes(b);r.update(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
 if b.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(p),str(p)+'.txt'],capture_output=True,timeout=20)
except Exception as e:r['error']=str(e)
(D/'sources'/f'{name}.receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(r)
