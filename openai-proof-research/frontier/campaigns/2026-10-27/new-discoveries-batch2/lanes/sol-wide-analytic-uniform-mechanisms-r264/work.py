from pathlib import Path
import urllib.request, urllib.error, hashlib, json, datetime, sys, subprocess
L=Path(__file__).resolve().parent
B=L.parent.parent
def sha(d): return hashlib.sha256(d).hexdigest()
def freeze(p, name):
 d=p.read_bytes(); q=L/'science'/name; q.parent.mkdir(exist_ok=True); q.write_bytes(d)
 rec={'original':str(p),'copy':str(q),'sha256':sha(d),'administrative':False}
 with (L/'bindings.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 assert sha(p.read_bytes())==sha(q.read_bytes())
 return q
def get(url,name):
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'bounded-math-research/1.0'}),timeout=35) as r:
   rec.update(status=r.status,headers=dict(r.headers)); d=r.read(12_000_001)
  if len(d)>12_000_000:raise ValueError('12MB bound exceeded')
  if any(x in d[:10000].lower() for x in [b'captcha',b'cf-chl-',b'google.com/recaptcha']):raise ValueError('challenge: STOP route')
  p=L/'primary'/name;p.parent.mkdir(exist_ok=True);p.write_bytes(d);rec.update(path=str(p),sha256=sha(d));freeze(p,name)
 except Exception as e:rec['error']=str(e)
 with (L/'access.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 return rec
if sys.argv[1]=='query':
 import urllib.parse
 query='(cat:math.CA OR cat:math.PR OR cat:math.MG OR cat:math.FA OR cat:math.SP) AND (all:conjecture OR all:"open problem")'
 r=get('https://export.arxiv.org/api/query?'+urllib.parse.urlencode(dict(search_query=query,start=0,max_results=65,sortBy='submittedDate',sortOrder='descending')),'query.xml');print(r)
 if 'error' not in r:
  import xml.etree.ElementTree as E
  root=E.parse(L/'science/query.xml');ns={'a':'http://www.w3.org/2005/Atom'}
  entries=[{k:e.find('a:'+k,ns).text for k in ['id','title','summary','published','updated']} for e in root.findall('a:entry',ns)]
  (L/'query.json').write_text(json.dumps(entries,indent=2));print(json.dumps(entries,indent=2))
elif sys.argv[1]=='pdf':
 for ident in sys.argv[2:]:
  r=get('https://arxiv.org/pdf/'+ident,ident+'.pdf');print(r)
  if 'error' not in r:
   subprocess.run(['pdftotext','-layout',str(L/'science'/(ident+'.pdf')),str(L/'science'/(ident+'.txt'))],check=True)
elif sys.argv[1]=='history':
 idx=freeze(B/'lanes/sol-wide-analytic-source-mechanisms-r259/expanded-history.json','history-index.json')
 refs=json.loads(idx.read_text())['verified_references'];out=[]
 for r in refs:
  p=Path(r['path']);d=p.read_bytes(); assert sha(d)==r['sha256'];out.append(r)
 (L/'history-verified.json').write_text(json.dumps(out,indent=2));print('Verified',len(out))
elif sys.argv[1]=='followup':
 import urllib.parse,xml.etree.ElementTree as E
 for label,query in [('breiman','all:Breiman'),('dirac','au:Gontier AND all:scalar')]:
  rec=get('https://export.arxiv.org/api/query?'+urllib.parse.urlencode(dict(search_query=query,max_results=25,sortBy='submittedDate',sortOrder='descending')),label+'-prior.xml')
  print(label,rec.get('status'),rec.get('error'))
  if 'error' not in rec:
   ns={'a':'http://www.w3.org/2005/Atom'};root=E.parse(L/'science'/(label+'-prior.xml'))
   print([(e.find('a:id',ns).text,e.find('a:title',ns).text) for e in root.findall('a:entry',ns)])
 ids=[p.stem.split('v')[0] for p in (L/'primary').glob('*.pdf')]
 rec=get('https://export.arxiv.org/api/query?'+urllib.parse.urlencode(dict(id_list=','.join(ids),max_results=20)),'versions.xml');print('versions',rec.get('status'),rec.get('error'))
 for n in ['sol-wide-finite-arithmetic-mechanisms-r260','sol-wide-finite-structural-mechanisms-r262']:
  p=B/'lanes'/n/'SCOUTING.md'
  if p.exists():
   q=freeze(p,n+'.md');print(n,q.read_text()[:8000])
