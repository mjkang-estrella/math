import pathlib,json,urllib.request,hashlib,datetime,subprocess
p=pathlib.Path(__file__).parent;r=json.loads((p/'http.json').read_text());url='https://lean.up.railway.app/papers/lcmgcd-negone-v1.pdf';x={'name':'lcmgcd-known.pdf','url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
try:
 with urllib.request.urlopen(url,timeout=25) as f:b=f.read();x.update(status=f.status,final_url=f.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
 (p/'sources/lcmgcd-known.pdf').write_bytes(b);subprocess.run(['pdftotext','-layout',str(p/'sources/lcmgcd-known.pdf'),str(p/'sources/lcmgcd-known.txt')],check=True)
except Exception as e:x['error']=str(e)
r.append(x);(p/'http.json').write_text(json.dumps(r,indent=2))
