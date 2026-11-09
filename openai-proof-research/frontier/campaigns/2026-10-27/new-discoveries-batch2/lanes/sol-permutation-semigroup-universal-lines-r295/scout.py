from pathlib import Path
import urllib.request,urllib.parse,hashlib,json,datetime,sys,xml.etree.ElementTree as ET,subprocess
L=Path(__file__).resolve().parent
def fetch(url,p):
 log=L/'access.json'; rows=json.loads(log.read_text()) if log.exists() else []
 e=dict(url=url,time=datetime.datetime.now(datetime.timezone.utc).isoformat(),file=str(p.relative_to(L)))
 try:
  with urllib.request.urlopen(url,timeout=20) as r: data=r.read(12*1024*1024);e['status']=r.status
  if any(x in data[:2000].lower() for x in [b'captcha',b'challenge']):raise ValueError('challenge; stop')
  p.parent.mkdir(exist_ok=True);p.write_bytes(data);e.update(sha256=hashlib.sha256(data).hexdigest(),size=len(data))
 except Exception as ex:e['failure']=str(ex)
 rows.append(e);log.write_text(json.dumps(rows,indent=2)+'\n');print(e,flush=True)
 return 'failure' not in e
if sys.argv[1]=='feed':
 q='cat:math.* AND (ti:counterexample OR ti:disproof) AND submittedDate:[202101010000 TO 202112312359]'
 fetch('https://export.arxiv.org/api/query?'+urllib.parse.urlencode(dict(search_query=q,start=0,max_results=35,sortBy='submittedDate',sortOrder='descending')),L/'sources'/'scout.xml')
elif sys.argv[1]=='list':
 root=ET.parse(L/'sources'/'scout.xml');ns={'a':'http://www.w3.org/2005/Atom'}
 for e in root.findall('a:entry',ns): print(e.findtext('a:id',namespaces=ns),' '.join(e.findtext('a:title',namespaces=ns).split()),' '.join(e.findtext('a:summary',namespaces=ns).split())[:1000])
elif sys.argv[1]=='bodies':
 for ident in sys.argv[2:]:
  p=L/'sources'/(ident+'.pdf')
  if fetch('https://arxiv.org/pdf/'+ident,p):
   subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True,timeout=20)
   data=p.with_suffix('.txt').read_bytes();h=hashlib.sha256(data).hexdigest()
   idx=L/'derived-bindings.json'; rows=json.loads(idx.read_text()) if idx.exists() else []
   rows.append(dict(file=str(p.with_suffix('.txt').relative_to(L)),sha256=h));idx.write_text(json.dumps(rows,indent=2)+'\n')
