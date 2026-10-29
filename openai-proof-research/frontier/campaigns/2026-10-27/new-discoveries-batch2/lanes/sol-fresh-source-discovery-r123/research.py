import os,sys,json,hashlib,gzip,sqlite3,re,time,urllib.request,urllib.error
from pathlib import Path
L=Path(__file__).resolve().parent
R=L.parents[5]; B=L.parent.parent
def sha(b):return hashlib.sha256(b).hexdigest()
def dump(n,x):(L/n).write_text(json.dumps(x,indent=2)+'\n')
if sys.argv[1]=='context':
 (L/'sources').mkdir(exist_ok=True)
 paths=[R/'AGENTS.md',B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',R/'sources/upstream.json',R/'sources/CONTENTS.md',R/'sources/preprints-tree.json']
 for folder,names in [('root-renyi-acceptance-r1',['ACCEPTANCE.md']),('root-factorial-final-exclusion-r1',['DECISION.md']),('sol-fresh-source-discovery-r120',['SUMMARY.md','discovery.md']),('sol-renyi-final-delta-closure-r4',['review.md','exactcoverage.json']),('sol-factorial-product-full-final-review-r1',['review.md','fresh-coverage.json']),('sol-fresh-source-discovery-r119',['registry-coverage.json','context-drift.json'])]:
  paths.extend(B/'lanes'/folder/n for n in names)
 rec=[]
 for i,p in enumerate(paths):
  if not p.exists():rec.append({'original':str(p),'missing':True});continue
  data=p.read_bytes();dest=L/'sources'/('context-%02d'%i+p.suffix);dest.write_bytes(data)
  rec.append(dict(original=str(p),copy=str(dest.relative_to(L)),sha256=sha(data),bytes=len(data),as_read_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())))
 dump('context-receipts.json',rec)
 data=(B/'NEXT.md').read_bytes();(L/'coordination-NEXT-as-read.md').write_bytes(data)
 dump('coordination-receipt.json',dict(sha256=sha(data),bytes=len(data),utc=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),scope='Mutable coordination only; not mathematical freeze'))
 print([(r['original'],r.get('bytes')) for r in rec])
elif sys.argv[1]=='scan':
 start=time.monotonic();db=sqlite3.connect(L/'screen.sqlite');db.execute('create table bodies(h text primary key,path text)')
 extensions={'.md','.txt','.json','.jsonl','.py','.sh','.lean','.tex','.csv','.tsv','.html','.htm','.yaml','.yml','.toml','.bib','.rst'}
 excluded={'inventory-content.jsonl','required-content.jsonl','semantic-hits.jsonl','duplicate-corpus.jsonl','matches.jsonl','pathmap.jsonl','semantic-matches.jsonl','target-matches.jsonl','focused-matches.jsonl'}
 dirs_ex={'.git','node_modules','.lake','__pycache__','vendor','dist','build','.venv','venv'}
 rg=re.compile(r'generalized.gamma.convolution|hyperbolic.complete.monoton|inverse.beta|Mittag.Leffler.*conjecture|Bickley.*conjecture|conjecture.*Bickley|conjecture.*(probab|Laplace|Stieltjes)',re.I)
 n=u=hitdocs=0;gaps=[];exc={}
 with gzip.open(L/'pathmap.jsonl.gz','wt') as out,open(L/'history-matches.jsonl','w') as mo:
  for root,dirs,files in os.walk(R):
   dirs[:]=[d for d in dirs if d not in dirs_ex and Path(root)/d!=L]
   for name in files:
    p=Path(root)/name;rel=str(p.relative_to(R))
    if name in excluded:exc[name]=exc.get(name,0)+1;continue
    if p.suffix.lower() not in extensions:continue
    try:
     size=p.stat().st_size
     if size>12000000 or re.search(r'r11[123]/.*(content|corpus|aggregate)',rel):gaps.append([rel,size,'size/aggregate exclusion']);continue
     h=hashlib.sha256()
     with p.open('rb') as f:
      while chunk:=f.read(65536):h.update(chunk)
     h=h.hexdigest();n+=1;out.write(json.dumps([h,rel])+'\n')
     try:db.execute('insert into bodies values (?,?)',(h,rel))
     except sqlite3.IntegrityError:continue
     u+=1;matches=[];count=0
     with p.open(errors='replace') as f:
      for lineno,line in enumerate(f,1):
       if rg.search(line):
        count+=1
        if len(matches)<6:matches.append([lineno,line[:900]])
     if matches:hitdocs+=1;mo.write(json.dumps(dict(path=rel,sha256=h,count=count,matches=matches))+'\n')
    except (OSError,ValueError) as e:gaps.append([rel,str(e)])
 db.commit();db.close();dump('screen-receipt.json',dict(paths=n,unique=u,seconds=time.monotonic()-start,matching_bodies=hitdocs,terms=rg.pattern,excluded_names=exc,excluded_dirs=sorted(dirs_ex),extensions=sorted(extensions),gaps=gaps,scope='All-date original/rejection/review/catalogue/script text stream with hash dedup; six 900-char excerpts/body; no global hit cap. No semantic clearance. PDF/binary/compressed bodies not searched.'))
 print(n,u,hitdocs,time.monotonic()-start)
elif sys.argv[1]=='targets':
 db=sqlite3.connect(L/'screen.sqlite');rg=re.compile(r'Ferreira|2108[.]09244|Mill.?s.?ratio|beta.prime|Bondesson.Steutel|556295|noncentral.chi|03505|Conjecture.?7[.]1|2609[.]28707|boundary.contact',re.I);docs=lines=0
 with open(L/'target-matches.jsonl','w') as out:
  for h,rel in db.execute('select h,path from bodies'):
   matches=[];count=0
   try:
    with (R/rel).open(errors='replace') as f:
     for no,line in enumerate(f,1):
      if rg.search(line):
       count+=1
       if len(matches)<5:matches.append([no,line[:1100]])
   except OSError:continue
   if count:docs+=1;lines+=count;out.write(json.dumps(dict(path=rel,sha256=h,count=count,matches=matches))+'\n')
 dump('target-receipt.json',dict(docs=docs,lines=lines,terms=rg.pattern,max_matches_per_body=5,no_global_hit_cutoff=True));print(docs,lines)
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
