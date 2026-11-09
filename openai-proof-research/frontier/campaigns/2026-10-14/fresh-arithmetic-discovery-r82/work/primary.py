from pathlib import Path
import json,hashlib,urllib.request,subprocess,sys
b=Path(__file__).resolve().parents[1]; rec=b/'packet/private/primary-provenance.json'; records=json.loads(rec.read_text()) if rec.exists() else []
for name,url in zip(sys.argv[1::2],sys.argv[2::2]):
 p=b/'packet/private/primary'/name
 try:
  with urllib.request.urlopen(url,timeout=45) as r:data=r.read(); final=r.url
  if not data.startswith(b'%PDF'):raise ValueError('not a PDF')
  p.with_suffix('.pdf').write_bytes(data)
  c=subprocess.run(['pdftotext','-layout',str(p.with_suffix('.pdf')),str(p.with_suffix('.txt'))],capture_output=True,text=True,check=True)
  records.append({'name':name,'request_url':url,'final_url':final,'pdf_path':str(p.with_suffix('.pdf').relative_to(b/'packet')),'text_path':str(p.with_suffix('.txt').relative_to(b/'packet')),'pdf_sha256':hashlib.sha256(data).hexdigest(),'text_sha256':hashlib.sha256(p.with_suffix('.txt').read_bytes()).hexdigest(),'extraction_stderr':c.stderr,'status':'success'})
  print(name,len(data),'lines',len(p.with_suffix('.txt').read_text().splitlines()))
 except Exception as e:records.append({'name':name,'request_url':url,'status':'failure','error':str(e)});print(name,str(e))
rec.write_text(json.dumps(records,indent=2)+'\n')
