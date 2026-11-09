from pathlib import Path
import json,re,urllib.request,hashlib,subprocess
R=Path(__file__).resolve().parent;out=[]
for e in json.loads((R/'downloads.json').read_text()):
 if not e.get('path','').endswith('.html'):continue
 b=(R/e['path']).read_text();u=re.findall(r'https://content.ems.press/[^"\s<>]*\.pdf',b)[0].rstrip('\\');x={'url':u,'name':e['name']}
 try:
  with urllib.request.urlopen(u,timeout=25) as f:data=f.read(15000000);x['status']=f.status
  p=R/'sources'/(e['name']+'.pdf');p.write_bytes(data);x.update(path=str(p.relative_to(R)),sha256=hashlib.sha256(data).hexdigest(),size=len(data))
 except Exception as ex:x['error']=str(ex)
 out.append(x);print(x['name'],x.get('status',x.get('error')))
(R/'body-downloads.json').write_text(json.dumps(out,indent=2)+'\n')
for p in (R/'sources').glob('*.pdf'):subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
