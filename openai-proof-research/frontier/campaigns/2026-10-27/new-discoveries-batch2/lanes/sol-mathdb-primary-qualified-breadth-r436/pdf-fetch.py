from pathlib import Path
import urllib.request,json,re,hashlib,subprocess
O=Path(__file__).parent;logs=[]
for p in sorted((O/'sources').glob('*.html')):
 url=re.search(r'<meta name="citation_pdf_url" content="([^"]+)"',p.read_text())[1]
 try:
  with urllib.request.urlopen(url,timeout=20) as r:b=r.read(6000000);status=r.status;final=r.url
  assert b.startswith(b'%PDF');dest=p.with_suffix('.pdf');dest.write_bytes(b)
  subprocess.run(['pdftotext','-layout',str(dest),str(p.with_suffix('.txt'))],check=True,timeout=15)
  logs.append({'url':url,'final_url':final,'status':status,'path':str(dest.relative_to(O)),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b),'text_extracted':True,'full_body_inspected':False})
 except Exception as e:logs.append({'url':url,'failure':str(e)});break
(O/'pdf-provenance.json').write_text(json.dumps(logs,indent=2)+'\n');print(json.dumps(logs,indent=2))
