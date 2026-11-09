from pathlib import Path
import urllib.request,json,hashlib,subprocess
R=Path(__file__).resolve().parent;out=[]
for name,u in [('bloch','https://arxiv.org/pdf/1408.1030'),('induniv','https://web.math.princeton.edu/~nalon/PDFS/induniv5.pdf')]:
 try:
  with urllib.request.urlopen(u,timeout=35) as f:b=f.read();status=f.status;final=f.url
  p=R/'sources'/(name+'.pdf');p.write_bytes(b);z=subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],capture_output=True)
  out.append({'url':u,'final_url':final,'path':str(p.relative_to(R)),'status':status,'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'pdftotext_exit':z.returncode})
 except Exception as e:out.append({'url':u,'failure':str(e)})
(R/'successor-provenance.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
