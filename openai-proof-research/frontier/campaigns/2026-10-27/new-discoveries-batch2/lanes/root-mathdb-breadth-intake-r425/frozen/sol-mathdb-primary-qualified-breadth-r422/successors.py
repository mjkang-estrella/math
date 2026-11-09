import pathlib,urllib.request,urllib.error,json,subprocess,hashlib
O=pathlib.Path(__file__).parent;out=[]
for tag,u in [('beligiannis','https://myweb.uoi.gr/abeligia/vGorenstein_final.pdf'),('adjoint','https://arxiv.org/pdf/math/0505315')]:
 try:
  with urllib.request.urlopen(u,timeout=25) as f:b=f.read(8000000)
  p=O/'primary'/(tag+'.pdf');p.write_bytes(b);subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
  out.append({'url':u,'file':str(p.relative_to(O)),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)})
 except Exception as e:out.append({'url':u,'error':str(e)});break
(O/'successor-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
