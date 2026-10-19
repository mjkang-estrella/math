"""Retrieve explicit primary versions, retaining original-rights bodies privately."""
import pathlib,urllib.request,hashlib,json,subprocess
R=pathlib.Path(__file__).resolve().parents[2];D=R/'packet/private/primary';D.mkdir(exist_ok=True)
items=[('pixton1207','https://arxiv.org/pdf/1207.1918v1'),('graber-pandharipande','https://arxiv.org/pdf/math/0104057v2'),('janda-pixton','https://arxiv.org/pdf/1304.0026v2'),('raufi','https://arxiv.org/pdf/1211.2948v2')]
log=[]
for name,url in items:
 try:
  r=urllib.request.urlopen(url,timeout=50);b=r.read(); assert b.startswith(b'%PDF');p=D/(name+'.pdf');p.write_bytes(b)
  t=p.with_suffix('.txt');s=subprocess.run(['pdftotext','-layout',str(p),str(t)],capture_output=True,text=True)
  assert s.returncode==0
  log.append({'name':name,'url':url,'final_url':r.url,'pdf':str(p.relative_to(R)),'pdf_sha256':hashlib.sha256(b).hexdigest(),'text':str(t.relative_to(R)),'text_sha256':hashlib.sha256(t.read_bytes()).hexdigest(),'extraction_stderr':s.stderr,'success':True})
  print(name,len(b),len(t.read_text().splitlines()))
 except Exception as e:log.append({'name':name,'url':url,'success':False,'error':str(e)});print(name,str(e))
(R/'packet/private/primary-provenance.json').write_text(json.dumps(log,indent=2)+'\n')
