import pathlib,urllib.request,json,hashlib,datetime,subprocess
L=pathlib.Path(__file__).resolve().parent;url='https://rdlyons.pages.iu.edu/prbtree/book_online.pdf';r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
try:
 with urllib.request.urlopen(url,timeout=35) as f:b=f.read();r.update(status=f.status,final_url=f.url)
 p=L/'lyons-peres.pdf';p.write_bytes(b);r.update(size=len(b),sha256=hashlib.sha256(b).hexdigest());(L/'classical-bindings.json').write_text(json.dumps(r,indent=2)+'\n')
 t=L/'lyons-peres.txt';subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True);b=t.read_bytes();r['derivative']={'path':str(t),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
except Exception as e:r['failure']=str(e)
(L/'classical-bindings.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
