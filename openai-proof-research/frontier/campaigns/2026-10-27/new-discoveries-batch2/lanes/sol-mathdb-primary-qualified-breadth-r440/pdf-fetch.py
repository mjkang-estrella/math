from pathlib import Path
import json,re,urllib.request,hashlib,subprocess
R=Path(__file__).resolve().parent; out=[]
for p in sorted((R/'sources').glob('*.html')):
 u=re.findall(r'https://content.ems.press/[^"\s<>]*?\.pdf',p.read_text())[0]
 try:
  with urllib.request.urlopen(u,timeout=30) as f:b=f.read();status=f.status
  q=p.with_suffix('.pdf');q.write_bytes(b)
  z=subprocess.run(['pdftotext','-layout',str(q),str(p.with_suffix('.txt'))],capture_output=True,text=True)
  out.append({'url':u,'path':str(q.relative_to(R)),'status':status,'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'pdftotext_exit':z.returncode})
 except Exception as e:out.append({'url':u,'failure':str(e)})
(R/'pdf-provenance.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
