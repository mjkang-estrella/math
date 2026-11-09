import pathlib,json,hashlib,sys,subprocess,urllib.request,datetime
L=pathlib.Path(__file__).resolve().parent
B=L.parent.parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def freeze(p,kind='scientific'):
 p=pathlib.Path(p).resolve(); h=sha(p)
 records=json.loads((L/'bindings.json').read_text()) if (L/'bindings.json').exists() else []
 if any(r['original']==str(p) for r in records):return
 if kind=='administrative':
  d=L/'administrative'/p.name;d.parent.mkdir(exist_ok=True);d.write_bytes(p.read_bytes());assert sha(d)==h
 else:d=p
 assert sha(p)==h
 records.append(dict(original=str(p),copy=str(d),sha256=h,kind=kind,frozen_utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))
 dump(L/'bindings.json',records)
def get(url,name):
 assert not any(s in url.lower() for s in ['google','sciencedirect'])
 assert 'github' not in url.lower() or url=='https://github.com/openai/math'
 out=L/'sources'/name;out.parent.mkdir(exist_ok=True)
 log=json.loads((L/'access.json').read_text()) if (L/'access.json').exists() else []
 if out.exists():return
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'Research scout (bounded primary-source inspection)'})
  with urllib.request.urlopen(req,timeout=22) as r:
   data=r.read(12_000_001);assert len(data)<=12_000_000
   out.write_bytes(data)
   log.append(dict(url=url,file=str(out),status=r.status,sha256=sha(out),date=datetime.datetime.now(datetime.timezone.utc).isoformat()))
  freeze(out)
 except Exception as e:log.append(dict(url=url,error=str(e),date=datetime.datetime.now(datetime.timezone.utc).isoformat()))
 dump(L/'access.json',log)
if sys.argv[1]=='init':
 for p in [B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/AGENTS.md')]:freeze(p,'administrative')
 freeze(B/'lanes/root-scout-r291-disposition/STATUS.md')
 # Flat immutable bindings only: original reports, never their historical subtrees.
 for p in B.glob('lanes/*/SCOUTING.md'):freeze(p)
 for p in B.glob('lanes/*/SUMMARY.md'):freeze(p)
 for p in pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/sources').glob('*.json'):freeze(p)
 freeze('/home/mj-kang/Documents/Dev/math/openai-proof-research/sources/CONTENTS.md')
 print('bindings',len(json.loads((L/'bindings.json').read_text())))
elif sys.argv[1]=='get':get(sys.argv[2],sys.argv[3])
elif sys.argv[1]=='papers':
 for ident in sys.argv[2:]:
  get('https://arxiv.org/pdf/'+ident,ident+'.pdf')
  p=L/'sources'/(ident+'.pdf')
  if p.exists() and not p.with_suffix('.txt').exists():
   subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True);freeze(p.with_suffix('.txt'))
elif sys.argv[1]=='queries':
 import urllib.parse
 for name,q in [('word','all:"word-representable" AND all:conjecture'),('matrix','all:"sign pattern" AND all:conjecture'),('orientation','all:"proper orientation" AND all:conjecture'),('permutation','all:"permutation" AND all:"conjectures"'),('geometry','all:"blocking sets" AND all:conjecture'),('word2','all:"abelian" AND all:"word" AND all:"open problems"')]:
  get('https://export.arxiv.org/api/query?'+urllib.parse.urlencode(dict(search_query=q,start=0,max_results=8,sortBy='relevance')),name+'-search.xml')
elif sys.argv[1]=='list':
 import xml.etree.ElementTree as E
 for p in (L/'sources').glob('*xml'):
  print('\n',p.name)
  for e in E.parse(p).getroot().findall('{http://www.w3.org/2005/Atom}entry'):
   print(e.findtext('{http://www.w3.org/2005/Atom}id'),e.findtext('{http://www.w3.org/2005/Atom}title'),e.findtext('{http://www.w3.org/2005/Atom}summary')[:1300])
elif sys.argv[1]=='followup':
 import urllib.parse
 for name,q in [('ap','all:"AP-irreducible"'),('sepr','all:"unique sepr"'),('semigroup','all:"permutation semigroups"'),('bruijn','all:"simplified de Bruijn"'),('lyndon','all:"Lyndon-Word"'),('parikh-original','au:Dick AND all:Parikh')]:
  get('https://export.arxiv.org/api/query?'+urllib.parse.urlencode(dict(search_query=q,start=0,max_results=8,sortBy='submittedDate',sortOrder='descending')),name+'-followup.xml')
elif sys.argv[1]=='locations':
 for p in (L/'sources').glob('*.txt'):
  pages=p.read_text().split('\f')
  for i,page in enumerate(pages,1):
   for s in ['Conjecture 5.1.','Conjecture 3.8.','Lemma 3.10.','Conjecture 1.3.','Question 4.1.','Theorem 4.6.','AP-irreducible if','2.2    Open Problems','Question 7.2.']:
    if s in page:print(p.name,'PDFpage',i,s)
elif sys.argv[1]=='pdf':
 p=L/'sources'/sys.argv[2];freeze(p);h=sha(p)
 subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
 assert sha(p)==h;freeze(p.with_suffix('.txt'))
elif sys.argv[1]=='dedup':
 terms=sys.argv[2:]; records=json.loads((L/'bindings.json').read_text());result={}
 for term in terms:
  hits=[]
  for r in records:
   p=pathlib.Path(r['original'])
   if p.suffix not in ['.md','.json']:continue
   assert sha(p)==r['sha256']
   for n,line in enumerate(p.read_text(errors='replace').splitlines(),1):
    if term.lower() in line.lower():hits.append([str(p),n,line[:650]])
  result[term]=hits[:35]
 dump(L/('dedup-'+str(len(list(L.glob('dedup*.json'))))+'.json'),result);print(json.dumps(result,indent=2))
