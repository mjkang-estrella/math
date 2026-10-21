from pathlib import Path
import urllib.request,hashlib,json,subprocess
out=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r121/packet/private/primary');out.mkdir(exist_ok=True)
items=[('harari-stix-2011','https://www.imo.universite-paris-saclay.fr/~david.harari/articles/finidesc.pdf'),('stoll-revised','https://mathe2.uni-bayreuth.de/stoll/papers/covers-revised.pdf'),('stoll-errata-2017','https://msp.org/ant/2007/1-4/ant-v1-n4-x01-Errata-FiniteDescent.pdf'),('stix-1203.3236v3','https://arxiv.org/pdf/1203.3236v3'),('betts-stix-2204.13674v1','https://arxiv.org/pdf/2204.13674v1')]
records=[]
for name,url in items:
 try:
  b=urllib.request.urlopen(url,timeout=45).read();assert b.startswith(b'%PDF')
  p=out/(name+'.pdf');p.write_bytes(b);q=out/(name+'.txt')
  subprocess.run(['pdftotext','-layout',str(p),str(q)],check=True)
  records.append({'url':url,'file':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'text':str(q),'text_sha256':hashlib.sha256(q.read_bytes()).hexdigest()})
  print(name,len(b),flush=True)
 except Exception as e:records.append({'url':url,'error':str(e)});print(name,'FAILED',str(e),flush=True)
(out.parent/'primary-identities.json').write_text(json.dumps(records,indent=2))
