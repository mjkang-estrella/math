from pathlib import Path
import urllib.request,hashlib,json,subprocess
R=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r116');D=R/'packet/private/primary';D.mkdir(exist_ok=True)
items=[('milne1972','https://www.jmilne.org/math/articles/1972a.pdf'),('milneADT','https://www.jmilne.org/math/Books/ADT.pdf'),('dokchitser','https://pure.mpg.de/pubman/item/item_3122955_1/component/file_3122956/dokchitser_birch_2010.pdf')];out=[]
for name,url in items:
 try:
  b=urllib.request.urlopen(url,timeout=45).read();assert b.startswith(b'%PDF');p=D/(name+'.pdf');p.write_bytes(b);q=D/(name+'.txt');z=subprocess.run(['pdftotext','-layout',str(p),str(q)],capture_output=True,text=True);out.append({'name':name,'url':url,'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'extract_sha256':hashlib.sha256(q.read_bytes()).hexdigest(),'extract_status':z.returncode,'stderr':z.stderr});print(name,len(b),len(q.read_bytes()))
 except Exception as e:out.append({'name':name,'url':url,'failure':repr(e)});print(name,repr(e))
(R/'packet/primary-identities.json').write_text(json.dumps(out,indent=2))
