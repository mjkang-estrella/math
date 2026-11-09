from pathlib import Path
import urllib.request,hashlib,json,subprocess
r=Path(__file__).resolve().parents[1]; reg=[]
for name,url in [('buck2609v1','https://arxiv.org/pdf/2609.23685v1'),('forni-moll2510v1','https://arxiv.org/pdf/2510.18128v1'),('gabdurakhmanov-kokarev2112v2','https://arxiv.org/pdf/2112.13419v2')]:
 try:
  b=urllib.request.urlopen(url,timeout=50).read();assert b.startswith(b'%PDF')
  p=r/'packet/private/primary'/f'{name}.pdf';p.write_bytes(b)
  q=p.with_suffix('.txt');c=['pdftotext','-layout',str(p),str(q)];z=subprocess.run(c,capture_output=True,text=True)
  rec={'name':name,'url':url,'success':True,'pdf':str(p.relative_to(r/'packet')),'pdf_sha256':hashlib.sha256(b).hexdigest(),'text':str(q.relative_to(r/'packet')),'text_sha256':hashlib.sha256(q.read_bytes()).hexdigest(),'extraction':c,'returncode':z.returncode,'stderr':z.stderr};print(name,len(b),flush=True)
 except Exception as e:rec={'name':name,'url':url,'success':False,'error':repr(e)};print(rec,flush=True)
 reg.append(rec);(r/'packet/public/primary-register.json').write_text(json.dumps(reg,indent=2)+'\n')
