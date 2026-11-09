import pathlib,json,urllib.request,datetime,hashlib,sys,subprocess
D=pathlib.Path(__file__).resolve().parents[1]
for label,url in zip(sys.argv[1::2],sys.argv[2::2]):
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=15) as f:b=f.read();r.update(status=f.status,final_url=f.url,sha256=hashlib.sha256(b).hexdigest())
  (D/f'sources/{label}').write_bytes(b)
  if b.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(D/f'sources/{label}'),str(D/f'sources/{label}.txt')],check=True)
 except Exception as e:r['error']=str(e)
 (D/f'sources/{label}.receipt.json').write_text(json.dumps(r,indent=2)); print(label,r,flush=True)
