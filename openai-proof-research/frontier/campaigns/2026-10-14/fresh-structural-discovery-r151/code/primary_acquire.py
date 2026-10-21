from pathlib import Path
import urllib.request,hashlib,json,subprocess,concurrent.futures
P=Path.cwd();R=P/'frontier/campaigns/2026-10-14/fresh-structural-discovery-r151';assert P==Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
D=R/'private/primary';D.mkdir(exist_ok=True)
items=[('FSZ','https://arxiv.org/pdf/2507.09507v1'),('ABHM','https://arxiv.org/pdf/2609.19118v1'),('KW','https://arxiv.org/pdf/1201.4764v1')]
def get(item):
 name,url=item
 try:
  b=urllib.request.urlopen(url,timeout=45).read();assert b.startswith(b'%PDF')
  p=D/(name+'.pdf');p.write_bytes(b);subprocess.run(['pdftotext','-layout',str(p),str(D/(name+'.txt'))],check=True,timeout=30)
  s=(D/(name+'.txt')).read_bytes()
  return {'name':name,'url':url,'pdf_size':len(b),'pdf_sha256':hashlib.sha256(b).hexdigest(),'text_sha256':hashlib.sha256(s).hexdigest(),'text_lines':len(s.splitlines())}
 except Exception as e:return {'name':name,'url':url,'failure':str(e)}
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as ex:rec=list(ex.map(get,items))
(D/'receipts.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec,indent=2))
