from pathlib import Path
import json,hashlib,urllib.request,urllib.parse,datetime,sys,subprocess,xml.etree.ElementTree as E
L=Path(__file__).resolve().parent; B=L.parent.parent
def sha(d):return hashlib.sha256(d).hexdigest()
def freeze(p,name):
 d=p.read_bytes(); q=L/'science'/name;q.parent.mkdir(exist_ok=True);q.write_bytes(d)
 assert sha(p.read_bytes())==sha(q.read_bytes())
 with (L/'bindings.jsonl').open('a') as f:f.write(json.dumps(dict(original=str(p),copy=str(q),sha256=sha(d)))+'\n')
 return q
def get(url,name):
 rec=dict(url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'bounded-math-research/1.0'}),timeout=25) as r:
   rec.update(status=r.status,headers=dict(r.headers));d=r.read(12000001)
  if len(d)>12000000:raise ValueError('12MB cap')
  if any(x in d[:10000].lower() for x in [b'captcha',b'cf-chl-',b'google.com/recaptcha']):raise ValueError('challenge STOP')
  p=L/'primary'/name;p.parent.mkdir(exist_ok=True);p.write_bytes(d);rec.update(path=str(p),sha256=sha(d));freeze(p,name)
 except Exception as e:rec['error']=str(e)
 with (L/'access.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 return rec
def query(q,name):
 r=get('https://export.arxiv.org/api/query?'+urllib.parse.urlencode(dict(search_query=q,max_results=100,sortBy='submittedDate',sortOrder='ascending')),name+'.xml')
 if 'error' in r:print(r);return
 ns={'a':'http://www.w3.org/2005/Atom'};out=[]
 for e in E.parse(L/'science'/(name+'.xml')).findall('a:entry',ns):
  d={k:e.findtext('a:'+k,namespaces=ns) for k in ['id','title','summary','published','updated']};d['authors']=[a.findtext('a:name',namespaces=ns) for a in e.findall('a:author',ns)];out.append(d)
 (L/(name+'.json')).write_text(json.dumps(out,indent=2));print('\n'.join(d['id']+' '+d['title']+' '+d['summary'][:650] for d in out))
if sys.argv[1]=='query':query(sys.argv[2],sys.argv[3])
elif sys.argv[1]=='pdf':
 for ident in sys.argv[2:]:
  r=get('https://arxiv.org/pdf/'+ident,ident+'.pdf');print(r)
  if 'error' not in r:subprocess.run(['pdftotext','-layout',str(L/'science'/(ident+'.pdf')),str(L/'science'/(ident+'.txt'))],check=True)
elif sys.argv[1]=='history':
 p=B/'lanes/sol-wide-analytic-source-mechanisms-r259/expanded-history.json'; q=freeze(p,'history-index.json');refs=json.loads(q.read_text())['verified_references']
 for r in refs:assert sha(Path(r['path']).read_bytes())==r['sha256']
 (L/'history-verified.json').write_text(json.dumps(refs,indent=2));print('verified',len(refs))
elif sys.argv[1]=='screen':
 terms=sys.argv[2:];hits=[]
 for r in json.loads((L/'history-verified.json').read_text()):
  p=Path(r['path']);d=p.read_bytes();assert sha(d)==r['sha256'];s=d.decode(errors='replace')
  for t in terms:
   if t.lower() in s.lower():
    i=s.lower().index(t.lower());hits.append(dict(term=t,path=str(p),sha256=r['sha256'],excerpt=s[max(0,i-180):i+500]))
 (L/'history-hits.json').write_text(json.dumps(hits,indent=2));print(json.dumps(hits,indent=2))
