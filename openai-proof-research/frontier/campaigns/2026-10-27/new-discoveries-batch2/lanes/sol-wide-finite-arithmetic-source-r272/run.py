import pathlib,hashlib,json,urllib.request,datetime,subprocess,sys,xml.etree.ElementTree as E
L=pathlib.Path(__file__).resolve().parent
B=L.parent.parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
def fetch(url,name):
 p=L/'sources'/name;p.parent.mkdir(exist_ok=True)
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical source research (bounded retrieval)'}),timeout=22) as r:
   data=r.read(12000000);rec.update(status=r.status,bytes=len(data),final_url=r.url)
  if b'captcha' in data[:5000].lower() or b'challenge' in data[:1000].lower():raise RuntimeError('challenge; stop route')
  p.write_bytes(data);rec['sha256']=sha(p)
 except Exception as e:rec['failure']=str(e)
 with (L/'access.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 return p if p.exists() else None
if sys.argv[1]=='init':
 (L/'admin').mkdir(exist_ok=True)
 for n in ['AGENTS.md','ledger.json','prior-campaign-context.json']:(L/'admin'/n).write_bytes((B/n).read_bytes())
 a=json.loads((B/'ledger.json').read_text());print({k:a.get(k) for k in ['accepted_count','total_accepted_count','next_global_outcome_number']})
 c=json.loads((B/'prior-campaign-context.json').read_text());print('context keys',list(c));print(str(c)[:4000])
 refs=[B/'lanes/sol-wide-finite-algebraic-mechanisms-r269/SCOUTING.md',B/'lanes/sol-wide-finite-arithmetic-mechanisms-r260/SCOUTING.md',pathlib.Path('openai-proof-research/sources/CONTENTS.md'),pathlib.Path('openai-proof-research/sources/preprints-tree.json')]
 dump(L/'immutable-references.json',[{'path':str(p.resolve()),'sha256':sha(p)} for p in refs])
 for yr in ['2010','2016','2020']:
  url='https://export.arxiv.org/api/query?search_query='+urllib.parse.quote('(cat:math.NT OR cat:math.CO OR cat:math.AC OR cat:math.OC) AND (all:conjecture OR all:question) AND submittedDate:['+yr+'01010000 TO '+yr+'12312359]')+'&start=0&max_results=24&sortBy=submittedDate&sortOrder=ascending'
  p=fetch(url,yr+'.xml')
  if p:
   ns={'a':'http://www.w3.org/2005/Atom'}
   for e in E.fromstring(p.read_bytes()).findall('a:entry',ns):print(e.findtext('a:id',namespaces=ns),e.findtext('a:title',namespaces=ns),e.findtext('a:summary',namespaces=ns)[:1000])
elif sys.argv[1]=='pdf':
 for ident in sys.argv[2:]:
  name=ident.replace('/','_');p=fetch('https://arxiv.org/pdf/'+ident,name+'.pdf')
  if p:
   before=sha(p);subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
   assert sha(p)==before
   with (L/'derived.jsonl').open('a') as f:f.write(json.dumps({'pdf':p.name,'sha256':before,'text_sha256':sha(p.with_suffix('.txt'))})+'\n')
elif sys.argv[1]=='fetch':fetch(sys.argv[2],sys.argv[3])
elif sys.argv[1]=='search':
 for i,q in enumerate(sys.argv[2:]):
  p=fetch('https://export.arxiv.org/api/query?search_query='+urllib.parse.quote(q)+'&max_results=12&sortBy=lastUpdatedDate&sortOrder=descending','search-'+hashlib.sha256(q.encode()).hexdigest()[:10]+'.xml')
  if p:
   ns={'a':'http://www.w3.org/2005/Atom'}
   for e in E.fromstring(p.read_bytes()).findall('a:entry',ns):print(q,e.findtext('a:id',namespaces=ns),e.findtext('a:title',namespaces=ns),e.findtext('a:summary',namespaces=ns)[:1300])
