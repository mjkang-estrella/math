import pathlib,json,urllib.request,datetime,hashlib,sys,subprocess
D=pathlib.Path(__file__).resolve().parents[1]
rows=json.loads((D/'extracted.json').read_text())
for i in sys.argv[1:]:
 o=rows[i]; a=o['source_url'].split('/')[-1]; url='https://arxiv.org/pdf/'+a
 r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url}
 try:
  with urllib.request.urlopen(url,timeout=18) as f:
   b=f.read();r.update(status=f.status,final_url=f.url,sha256=hashlib.sha256(b).hexdigest())
  (D/f'sources/{i}.pdf').write_bytes(b)
  if b.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(D/f'sources/{i}.pdf'),str(D/f'sources/{i}.txt')],check=True)
 except Exception as e:r['error']=str(e)
 (D/f'sources/{i}.receipt.json').write_text(json.dumps(r,indent=2)+'\n')
 print(i,r,flush=True)
