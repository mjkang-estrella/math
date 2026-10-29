import os,sys,json,hashlib,gzip,sqlite3,re,time,urllib.request,urllib.error
from pathlib import Path
L=Path(__file__).resolve().parent
R=L.parents[5]
B=L.parent.parent
def sha(b):return hashlib.sha256(b).hexdigest()
def dump(n,x):(L/n).write_text(json.dumps(x,indent=2)+'\n')
if sys.argv[1]=='context':
 (L/'sources').mkdir(exist_ok=True)
 paths=[R/'AGENTS.md',B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',B/'NEXT.md',R/'sources/upstream.json',R/'sources/CONTENTS.md',R/'sources/preprints-tree.json']
 for folder,names in [('sol-fresh-source-discovery-r118',['SUMMARY.md','discovery.md']),('root-r118-handback',['DECISION.md','CHECKS.json']),('sol-renyi-final-delta-closure-r4',['review.md']),('sol-factorial-product-full-final-review-r1',['review.md','fresh-coverage.json']),('sol-renyi-registry-gap-closure-r3',['SUMMARY.md']),('sol-factorial-product-prior-clearance-r2',['SUMMARY.md'])]:
  paths.extend(B/'lanes'/folder/n for n in names)
 rec=[]
 for i,p in enumerate(paths):
  if not p.exists():rec.append({'original':str(p),'missing':True});continue
  data=p.read_bytes();dest=L/'sources'/('context-%02d'%i+p.suffix);dest.write_bytes(data)
  rec.append(dict(original=str(p),copy=str(dest.relative_to(L)),sha256=sha(data),bytes=len(data),as_read_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())))
 dump('context-receipts.json',rec)
 print(json.dumps(rec,indent=2))
elif sys.argv[1]=='scan':
 start=time.monotonic();db=sqlite3.connect(L/'screen.sqlite');db.execute('create table bodies(h text primary key,path text)')
 extensions={'.md','.txt','.json','.jsonl','.py','.sh','.lean','.tex','.csv','.tsv','.html','.htm','.yaml','.yml','.toml','.bib','.rst'}
 excluded={'inventory-content.jsonl','required-content.jsonl','semantic-hits.jsonl','duplicate-corpus.jsonl','matches.jsonl','pathmap.jsonl','semantic-matches.jsonl'}
 dirs_ex={'.git','node_modules','.lake','__pycache__','vendor','dist','build'}
 pats={'geometry':r'logarithmic.Brunn|B.conjecture|Gardner.Zvavitch|log.Minkowski|dual.volume|chord.integral', 'analytic':r'Nielsen.beta|Volterra.function|Bickley.function|Berg.*conjecture|complete.monotonic.*conjecture'}
 regs={k:re.compile(v,re.I) for k,v in pats.items()};hits={k:0 for k in pats};n=u=0;gaps=[];excluded_count={}
 with gzip.open(L/'pathmap.jsonl.gz','wt') as out,open(L/'semantic-matches.jsonl','w') as mo:
  for root,dirs,files in os.walk(R):
   dirs[:]=[d for d in dirs if d not in dirs_ex and Path(root)/d!=L]
   for name in files:
    p=Path(root)/name;rel=str(p.relative_to(R))
    if name in excluded:excluded_count[name]=excluded_count.get(name,0)+1;continue
    if p.suffix.lower() not in extensions:continue
    try:
     size=p.stat().st_size
     if size>12000000:gaps.append([rel,size,'12MB cap']);continue
     h=hashlib.sha256()
     with p.open('rb') as f:
      while chunk:=f.read(65536):h.update(chunk)
     h=h.hexdigest();n+=1;out.write(json.dumps([h,rel])+'\n')
     try:db.execute('insert into bodies values (?,?)',(h,rel))
     except sqlite3.IntegrityError:continue
     u+=1
     with p.open(errors='replace') as f:
      for lineno,line in enumerate(f,1):
       for key,rg in regs.items():
        if hits[key]<120 and rg.search(line):mo.write(json.dumps(dict(topic=key,path=rel,line=lineno,text=line[:850]))+'\n');hits[key]+=1
    except (OSError,ValueError) as e:gaps.append([rel,str(e)])
 db.commit();db.close();dump('screen-receipt.json',dict(paths=n,unique=u,seconds=time.monotonic()-start,hits=hits,excluded_names=excluded_count,excluded_dirs=sorted(dirs_ex),extensions=sorted(extensions),gaps=gaps,scope='All-date hash-deduplicated bounded lexical scan; not a semantic audit; PDF/binary/compressed bodies excluded. Generated content echoes excluded by explicit basename and size, not all generated files.'))
 print(n,u,hits,time.monotonic()-start)
elif sys.argv[1]=='targets':
 db=sqlite3.connect(L/'screen.sqlite');rg=re.compile(r'Nielsen|Volterra|1805[.]01462|22499[.]94241|jca-27-09',re.I);n=0;docs=0
 with open(L/'target-matches.jsonl','w') as out:
  for h,rel in db.execute('select h,path from bodies'):
   p=R/rel;matches=[]
   try:
    with p.open(errors='replace') as f:
     for lineno,line in enumerate(f,1):
      if rg.search(line):
       n+=1
       if len(matches)<8:matches.append({'line':lineno,'text':line[:1000]})
   except OSError:continue
   if matches:docs+=1;out.write(json.dumps({'path':rel,'sha256':h,'matches':matches})+'\n')
 db.close();dump('target-scan-receipt.json',{'matching_lines':n,'matching_distinct_bodies':docs,'max_excerpts_per_body':8,'max_excerpt_chars':1000,'terms':rg.pattern,'scope':'All hash-distinct screened text bodies, not PDFs; no global hit cutoff.'});print(docs,n)
elif sys.argv[1]=='fetch':
 url,name=sys.argv[2:];receipt=dict(url=url,utc=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()))
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source verification'}),timeout=35) as r:
   data=r.read(8000001);receipt.update(status=r.status,content_type=r.headers.get('Content-Type'),final_url=r.url)
  (L/'sources'/name).write_bytes(data);receipt.update(copy='sources/'+name,sha256=sha(data),bytes=len(data),truncated=len(data)>8000000)
 except urllib.error.HTTPError as e:
  data=e.read(100000);(L/'sources'/name).write_bytes(data);receipt.update(status=e.code,error=str(e),copy='sources/'+name,sha256=sha(data),bytes=len(data))
 except Exception as e:receipt['error']=str(e)
 with (L/'http.jsonl').open('a') as f:f.write(json.dumps(receipt)+'\n')
 print(receipt)
