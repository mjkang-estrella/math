import sys,pathlib,urllib.request,json,datetime,hashlib,subprocess
D=pathlib.Path(__file__).resolve().parents[1];name,url=sys.argv[1:];p=D/'sources'/name;p.mkdir(parents=True,exist_ok=False);r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
try:
 with urllib.request.urlopen(url,timeout=20) as f:b=f.read();r.update(status=f.status,sha256=hashlib.sha256(b).hexdigest());(p/'raw').write_bytes(b)
 if b.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(p/'raw'),str(p/'text.txt')])
except Exception as e:r['error']=str(e)
(p/'receipt.json').write_text(json.dumps(r,indent=2));print(r)
