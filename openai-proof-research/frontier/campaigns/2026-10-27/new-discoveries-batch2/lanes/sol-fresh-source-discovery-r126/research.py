import os,sys,re,json,hashlib,gzip,sqlite3,time,urllib.request,urllib.error
from pathlib import Path
L=Path(__file__).resolve().parent; R=L.parents[5]; B=L.parent.parent
def sha(b):return hashlib.sha256(b).hexdigest()
def utc():return time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())
def dump(n,x):(L/n).write_text(json.dumps(x,indent=2)+'\n')
if sys.argv[1]=='context':
 (L/'sources').mkdir(exist_ok=True)
 paths=[R/'AGENTS.md',B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',R/'sources/upstream.json',R/'sources/CONTENTS.md',R/'sources/preprints-tree.json']
 for folder,names in [('root-r119-handback',['DECISION.md']),('root-r120-handback',['DECISION.md']),('root-r121-handback',['DECISION.md']),('root-r122-handback',['DECISION.md']),('sol-fresh-source-discovery-r123',['SUMMARY.md','discovery.md']),('sol-renyi-final-delta-closure-r4',['review.md','exactcoverage.json']),('sol-factorial-product-full-final-review-r1',['review.md','fresh-coverage.json']),('sol-fresh-source-discovery-r119',['registry-coverage.json','context-drift.json'])]:
  paths.extend(B/'lanes'/folder/n for n in names)
 rec=[]
 for i,p in enumerate(paths):
  if not p.exists():rec.append(dict(original=str(p),missing=True));continue
  data=p.read_bytes();dest=L/'sources'/('context-%02d'%i+p.suffix);dest.write_bytes(data)
  rec.append(dict(original=str(p),copy=str(dest.relative_to(L)),sha256=sha(data),bytes=len(data),utc=utc()))
 dump('context-receipts.json',rec)
 data=(B/'NEXT.md').read_bytes();(L/'coordination-NEXT-as-read.md').write_bytes(data)
 dump('coordination-receipt.json',dict(sha256=sha(data),bytes=len(data),utc=utc(),scope='Mutable coordination, separate from scientific source freeze'))
 print('context',len(rec))
elif sys.argv[1]=='scan':
 start=time.monotonic();db=sqlite3.connect(L/'screen.sqlite');db.execute('create table bodies(h text primary key,path text)')
 ext={'.md','.txt','.json','.jsonl','.py','.sh','.lean','.tex','.csv','.tsv','.html','.htm','.yaml','.yml','.toml','.bib','.rst'}
 # Roles: generated copied-content indexes and lexical retrieval output; no lane exclusion.
 excluded={'inventory-content.jsonl','required-content.jsonl','semantic-hits.jsonl','duplicate-corpus.jsonl','matches.jsonl','pathmap.jsonl','semantic-matches.jsonl','target-matches.jsonl','focused-matches.jsonl','history-matches.jsonl'}
 dirs_ex={'.git','node_modules','.lake','__pycache__','vendor','dist','build','.venv','venv'}
 pat=re.compile(r'Mahmoud|Mortici|02697|Structural Properties, Complete Monotonicity|Szab[oó]|129984|Completely monotone functions in general|COMPLETE MONOTONICITY OF DISCRETE EQUATIONS|Ferreira|Weigert|01136',re.I)
 n=u=hits=0;gaps=[];exc={}
 with gzip.open(L/'pathmap.jsonl.gz','wt') as out,open(L/'target-matches.jsonl','w') as mo:
  for root,dirs,files in os.walk(R):
   dirs[:]=[d for d in dirs if d not in dirs_ex and Path(root)/d!=L]
   for name in files:
    p=Path(root)/name;rel=str(p.relative_to(R))
    if name in excluded:exc[name]=exc.get(name,0)+1;continue
    if p.suffix.lower() not in ext:continue
    try:
     size=p.stat().st_size
     if size>12000000:gaps.append([rel,size,'per-file >12MB']);continue
     h=hashlib.sha256()
     with p.open('rb') as f:
      while chunk:=f.read(65536):h.update(chunk)
     h=h.hexdigest();n+=1;out.write(json.dumps([h,rel])+'\n')
     try:db.execute('insert into bodies values (?,?)',(h,rel))
     except sqlite3.IntegrityError:continue
     u+=1;matches=[];count=0
     with p.open(errors='replace') as f:
      for lineno,line in enumerate(f,1):
       if pat.search(line):
        count+=1
        if len(matches)<8:matches.append([lineno,line[:1200]])
     if count:hits+=1;mo.write(json.dumps(dict(path=rel,sha256=h,count=count,omitted_matches=max(0,count-8),matches=matches))+'\n')
    except OSError as e:gaps.append([rel,str(e)])
 db.commit();db.close();dump('screen-receipt.json',dict(utc=utc(),paths=n,unique=u,matching_bodies=hits,seconds=time.monotonic()-start,pattern=pat.pattern,excluded_names=exc,excluded_dirs=sorted(dirs_ex),extensions=sorted(ext),gaps=gaps,no_global_match_cutoff=True,per_body_limit='8 excerpts of 1200 characters; full match count recorded',scope='All-date text lexical screen; no scientific r111-r113 lane exclusions. Binary/PDF/compressed bodies require separate extraction; not semantic clearance.'))
 print(n,u,hits,time.monotonic()-start)
elif sys.argv[1]=='exact':
 db=sqlite3.connect(L/'screen.sqlite')
 pat=re.compile(r's00025-026-02697-2|Wallis.Type Gamma Ratio|Completely monotone functions in general|jmaa[.]2025[.]129984|complete monotonicity of discrete equations|Rui A[.]? C[.]? Ferreira|CM_Discrete_M_L_Function|2607[.]09868|Determinacy Witnesses',re.I)
 docs=lines=0
 with (L/'exact-matches.jsonl').open('w') as out:
  for h,rel in db.execute('select h,path from bodies'):
   ms=[];count=0
   with (R/rel).open(errors='replace') as f:
    for no,line in enumerate(f,1):
     if pat.search(line):
      count+=1
      if len(ms)<12:ms.append([no,line[:1400]])
   if count:
    docs+=1;lines+=count;out.write(json.dumps(dict(path=rel,sha256=h,count=count,omitted_matches=max(0,count-12),matches=ms))+'\n')
 dump('exact-receipt.json',dict(utc=utc(),docs=docs,lines=lines,pattern=pat.pattern,no_global_match_cutoff=True,scope='Every deduplicated body from first scan reopened; not filtering its truncated excerpts; 12x1400 per body.'))
 print(docs,lines)
elif sys.argv[1]=='focus':
 pat=re.compile(r'Mahmoud|Mortici|s00025-026-02697|Wallis.Type|129984\b|Szab.{0,8}(problem|monoton)|discrete equations|01136',re.I)
 rows=[]
 with (L/'target-matches.jsonl').open() as f:
  for line in f:
   row=json.loads(line);ms=[m for m in row['matches'] if pat.search(m[1])]
   if ms:rows.append(dict(path=row['path'],count=row['count'],matches=ms))
 dump('focused-history.json',rows)
 for row in rows:print(row['path'],row['matches'])
elif sys.argv[1]=='fetch':
 url,name=sys.argv[2:];rec=dict(url=url,utc=utc())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source verification'}),timeout=35) as r:
   data=r.read(8000001);rec.update(status=r.status,content_type=r.headers.get('Content-Type'),final_url=r.url)
  rec.update(truncated=len(data)>8000000)
 except urllib.error.HTTPError as e:data=e.read(100000);rec.update(status=e.code,error=str(e))
 except Exception as e:
  rec['error']=str(e);data=b''
 (L/'sources'/name).write_bytes(data);rec.update(copy='sources/'+name,bytes=len(data),sha256=sha(data))
 with (L/'http.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 print(rec)
