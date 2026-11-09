import urllib.request,pathlib,sys,hashlib,datetime,json,subprocess
L=pathlib.Path(__file__).resolve().parents[1]; rec=[]
for name,url in zip(sys.argv[1::2],sys.argv[2::2]):
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=30) as f:d=f.read();r.update(status=f.status,final_url=f.url,sha256=hashlib.sha256(d).hexdigest(),bytes=len(d));(L/'sources'/name).write_bytes(d)
  if name.endswith('.pdf'):subprocess.run(['pdftotext','-layout',str(L/'sources'/name),str(L/'sources'/name.replace('.pdf','.txt'))],timeout=15)
 except Exception as e:r['error']=str(e)
 rec.append(r);print(r)
p=L/'sources/extra-receipts.json';old=json.loads(p.read_text()) if p.exists() else [];p.write_text(json.dumps(old+rec,indent=2))
