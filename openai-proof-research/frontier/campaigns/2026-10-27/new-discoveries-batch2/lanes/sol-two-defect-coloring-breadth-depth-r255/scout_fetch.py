import pathlib,urllib.request,urllib.parse,json,hashlib,datetime,xml.etree.ElementTree as ET,subprocess
L=pathlib.Path(__file__).parent;(L/'scout').mkdir(exist_ok=True)
receipts=[]
def get(u,p,cap):
 r={'url':u,'utc':str(datetime.datetime.now(datetime.timezone.utc))}
 try:
  with urllib.request.urlopen(u,timeout=18) as f:b=f.read(cap+1);r['status']=f.status
  assert len(b)<=cap
  p.write_bytes(b);r.update(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
  assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256']
  receipts.append(r);return b
 except Exception as e:r['failure']=repr(e);receipts.append(r);return None
q='(cat:math.CO OR cat:math.NT OR cat:math.AC) AND all:conjecture AND submittedDate:[202105010000 TO 202105312359]'
u='https://export.arxiv.org/api/query?'+urllib.parse.urlencode({'search_query':q,'max_results':10,'sortBy':'submittedDate','sortOrder':'ascending'})
b=get(u,L/'scout'/'index.xml',200000)
ns={'a':'http://www.w3.org/2005/Atom'}
entries=[]
if b:
 for e in ET.fromstring(b).findall('a:entry',ns):
  ident=e.findtext('a:id',namespaces=ns).rsplit('/',1)[-1];title=e.findtext('a:title',namespaces=ns)
  pdf=L/'scout'/(ident+'.pdf');bb=get('https://arxiv.org/pdf/'+ident,pdf,3500000)
  if bb:
   # Source frozen and verified before extraction/scientific reading.
   subprocess.run(['pdftotext','-layout',str(pdf),str(pdf)+'.txt'],check=True,timeout=12)
  entries.append({'id':ident,'title':title,'authors':[a.findtext('a:name',namespaces=ns) for a in e.findall('a:author',ns)]})
(L/'scout'/'entries.json').write_text(json.dumps(entries,indent=2));(L/'scout-receipts.json').write_text(json.dumps(receipts,indent=2))
print(json.dumps(entries,indent=2))
