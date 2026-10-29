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
 for folder,names in [('root-r119-handback',['DECISION.md','ADOPTION.json']),('root-r120-handback',['DECISION.md','ADOPTION.json']),('root-renyi-acceptance-r1',['ACCEPTANCE.md']),('root-factorial-final-exclusion-r1',['DECISION.md']),('sol-fresh-source-discovery-r119',['SUMMARY.md','discovery.md','registry-coverage.json']),('sol-fresh-source-discovery-r120',['SUMMARY.md','discovery.md']),('sol-fresh-source-discovery-r121',['SUMMARY.md','discovery.md'])]:
  paths.extend(B/'lanes'/folder/n for n in names)
 rec=[]
 for i,p in enumerate(paths):
  data=p.read_bytes();dest=L/'sources'/('context-%02d'%i+p.suffix);dest.write_bytes(data)
  rec.append(dict(original=str(p),copy=str(dest.relative_to(L)),sha256=sha(data),bytes=len(data),as_read_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),mutable=p.name=='NEXT.md'))
 dump('context-receipts.json',rec)
 print('context copies',len(rec))
elif sys.argv[1]=='scan':
 start=time.monotonic();db=sqlite3.connect(L/'screen.sqlite');db.execute('create table bodies(h text primary key,path text)')
 extensions={'.md','.txt','.json','.jsonl','.py','.sh','.lean','.tex','.csv','.tsv','.html','.htm','.yaml','.yml','.toml','.bib','.rst'}
 excluded={'inventory-content.jsonl','required-content.jsonl','semantic-hits.jsonl','duplicate-corpus.jsonl','matches.jsonl','pathmap.jsonl','semantic-matches.jsonl','target-matches.jsonl','target-specific-matches.jsonl'}
 dirs_ex={'.git','node_modules','.lake','__pycache__','vendor','dist','build','.venv','venv'}
 rg=re.compile(r'Agoh|aa9[/ .]|intrinsic factor of an alternating|reciprocals? of subsum|2605[.]10512|Ballantine|Maurischat',re.I)
 n=u=lines=docs=0;gaps=[];ex=[]
 with gzip.open(L/'pathmap.jsonl.gz','wt') as out,open(L/'target-matches.jsonl','w') as mo:
  for root,dirs,files in os.walk(R):
   dirs[:]=[d for d in dirs if d not in dirs_ex and Path(root)/d!=L]
   for name in files:
    p=Path(root)/name;rel=str(p.relative_to(R))
    if name in excluded:ex.append(rel);continue
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
     u+=1;matches=[];count=0
     with p.open(errors='replace') as f:
      for lineno,line in enumerate(f,1):
       if rg.search(line):
        lines+=1;count+=1
        if len(matches)<8:matches.append({'line':lineno,'text':line[:1000]})
     if count:docs+=1;mo.write(json.dumps(dict(path=rel,sha256=h,matching_lines=count,excerpts=matches))+'\n')
    except (OSError,ValueError) as e:gaps.append([rel,str(e)])
 db.commit();db.close();dump('screen-receipt.json',dict(paths=n,unique=u,seconds=time.monotonic()-start,matching_lines=lines,matching_bodies=docs,terms=rg.pattern,global_match_cutoff=None,per_body_excerpt_limit=8,excerpt_char_limit=1000,excluded_paths=ex,excluded_dirs=sorted(dirs_ex),extensions=sorted(extensions),gaps=gaps,scope='All-date original/copy research/rejection/review/script/catalogue text; hashes and aliases streamed. PDF/binary/compressed and other extensions omitted. Lexical retrieval, not full semantic reading.'))
 print(n,u,docs,lines,time.monotonic()-start)
elif sys.argv[1]=='refine':
 start=time.monotonic();db=sqlite3.connect(L/'screen.sqlite')
 rg=re.compile(r"Agoh.{0,8}alternating.numerator|alternating.numerator.characterization|18154119|intrinsic factor of an alternating sum involving certain rational functions|ordinary denominator log.concavity|denominator.dyadic|Reciprocals of Subsum Polynomials|2605[.]10512|Koizumi|18714404|aa28/|irrationality of the reciprocal sum|pseudo.greedy",re.I)
 docs=lines=0
 with (L/'refined-matches.jsonl').open('w') as out:
  for h,p in db.execute('select h,path from bodies'):
   matches=[];count=0
   try:
    with (R/p).open(errors='replace') as f:
     for i,line in enumerate(f,1):
      if rg.search(line):
       lines+=1;count+=1
       if len(matches)<8:matches.append({'line':i,'text':line[:1000]})
   except OSError:continue
   if count:docs+=1;out.write(json.dumps({'path':p,'sha256':h,'matching_lines':count,'excerpts':matches})+'\n')
 dump('refined-receipt.json',dict(terms=rg.pattern,matching_bodies=docs,matching_lines=lines,global_match_cutoff=None,per_body_excerpt_limit=8,excerpt_char_limit=1000,seconds=time.monotonic()-start,scope='Rescreen of every distinct original text body in the saved stream. Same exact omitted paths and formats as screen-receipt.'))
 print(docs,lines,time.monotonic()-start)
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
