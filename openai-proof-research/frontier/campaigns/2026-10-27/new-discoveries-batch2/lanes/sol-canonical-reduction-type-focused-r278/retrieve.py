from pathlib import Path
import urllib.request,urllib.parse,hashlib,json,datetime,subprocess,xml.etree.ElementTree as E
L=Path(__file__).resolve().parent;(L/'sources').mkdir(exist_ok=True)
jobs=[('versions.xml','https://export.arxiv.org/api/query?id_list=2003.05391,2406.00790,2501.08260,1712.00755&max_results=4'),('canonical.xml','https://export.arxiv.org/api/query?'+urllib.parse.urlencode(dict(search_query='all:"canonical reduction" AND all:semigroup',max_results=20,sortBy='lastUpdatedDate',sortOrder='descending'))),('specialist.xml','https://export.arxiv.org/api/query?'+urllib.parse.urlencode(dict(search_query='all:"pseudo-Frobenius" AND all:"four"',max_results=25,sortBy='lastUpdatedDate',sortOrder='descending'))),('rahimi.pdf','https://arxiv.org/pdf/1712.00755v3')]
import sys
if '--successor' in sys.argv: jobs=[('determinantal.pdf','https://arxiv.org/pdf/2609.18136v1')]
for name,url in jobs:
 r=dict(url=url,at=datetime.datetime.now(datetime.timezone.utc).isoformat(),path='sources/'+name)
 try:
  with urllib.request.urlopen(url,timeout=25) as response:
   data=response.read(4000000);r.update(status=response.status,final_url=response.url)
  p=L/'sources'/name;p.write_bytes(data);r['sha256']=hashlib.sha256(data).hexdigest();assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256'];r['frozen_before_read']=True
  if name.endswith('.xml'):
   root=E.fromstring(data);ns={'a':'http://www.w3.org/2005/Atom'}
   for e in root.findall('a:entry',ns):print(name,[(k,e.findtext('a:'+k,namespaces=ns)) for k in ['id','title','published','updated','summary']])
  elif name.endswith('.pdf'):
   subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True);r['text_sha256']=hashlib.sha256(p.with_suffix('.txt').read_bytes()).hexdigest()
 except Exception as ex:r['failure']=repr(ex)
 with (L/'access.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
 print('RECEIPT',r)
