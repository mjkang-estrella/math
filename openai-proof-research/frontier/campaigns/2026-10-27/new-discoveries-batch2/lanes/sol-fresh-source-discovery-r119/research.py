import os,sys,json,hashlib,gzip,sqlite3,re,time,urllib.request,shutil
from pathlib import Path
L=Path(__file__).resolve().parent
R=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
B=L.parent.parent
def sha(b):return hashlib.sha256(b).hexdigest()
def dump(p,x): (L/p).write_text(json.dumps(x,indent=2)+'\n')
if sys.argv[1]=='context':
 (L/'sources').mkdir(exist_ok=True)
 paths=[R/'AGENTS.md',B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',B/'NEXT.md',R/'sources/upstream.json',R/'sources/CONTENTS.md',R/'sources/preprints-tree.json',B/'lanes/root-r117-handback/ADOPTION.json',B/'lanes/root-r117-handback/DECISION.md',B/'lanes/sol-fresh-source-discovery-r118/SUMMARY.md',B/'lanes/sol-fresh-source-discovery-r118/discovery.md',B/'lanes/root-renyi-final-review-adoption-r1/ADOPTION.json',B/'lanes/sol-renyi-registry-gap-closure-r3/exactcoverage.json']
 rec=[]
 for i,p in enumerate(paths):
  data=p.read_bytes(); dest=L/'sources'/('context-%02d'%i+p.suffix);dest.write_bytes(data)
  rec.append(dict(original=str(p),copy=str(dest.relative_to(L)),sha256=sha(data),bytes=len(data)))
  if p.suffix=='.json':
   j=json.loads(data); print(p.name, 'keys',list(j)[:30] if isinstance(j,dict) else len(j))
  elif p.name=='NEXT.md':
   # Read all coordination text, report only target-bearing lines, bounded.
   lines=data.decode().splitlines();print('NEXT lines',len(lines));print('\n'.join([s for s in lines if re.search('reject|exclude|r117|r118|count',s,re.I)][:50]))
 dump('context-receipts.json',rec)
elif sys.argv[1]=='scan':
 start=time.monotonic();db=sqlite3.connect(L/'screen.sqlite');db.execute('create table if not exists bodies (h text primary key, path text)')
 extensions={'.md','.txt','.json','.jsonl','.py','.sh','.lean','.tex','.csv','.tsv','.html','.htm','.yaml','.yml','.toml','.ipynb','.bib','.rst'}
 # Exact basename exclusions: generated aggregate outputs only; originals remain eligible.
 excluded_names={'inventory-content.jsonl','required-content.jsonl','semantic-hits.jsonl','duplicate-corpus.jsonl','matches.jsonl','pathmap.jsonl','pathmap.jsonl.gz','audit.sqlite','audit.sqlite.gz','screen.sqlite'}
 excluded_dirs={'.git','node_modules','.lake','__pycache__','vendor','dist','build'}
 pats={ 'partition':r'minimum.period|restricted.partition|Cimpoea|Nicolae', 'ward':r'Ward.{0,35}divis|divis.{0,35}Ward', 'readonce':r'read.once.{0,40}factorial|factorial.{0,40}read.once'}
 regs={k:re.compile(v,re.I) for k,v in pats.items()};hits={k:0 for k in pats};n=u=0;gaps={};ex={};
 with gzip.open(L/'pathmap.jsonl.gz','wt') as out,open(L/'semantic-matches.jsonl','w') as mo:
  for root,dirs,files in os.walk(R):
   dirs[:]=[d for d in dirs if d not in excluded_dirs and Path(root)/d!=L]
   for name in files:
    p=Path(root)/name;rel=str(p.relative_to(R))
    if name in excluded_names:ex[name]=ex.get(name,0)+1;continue
    if p.suffix.lower() not in extensions:continue
    try:
     size=p.stat().st_size
     if size>12000000:gaps[rel]={'bytes':size,'reason':'12MB text cap'};continue
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
        if hits[key]<90 and rg.search(line):
         mo.write(json.dumps(dict(topic=key,path=rel,line=lineno,text=line[:650]))+'\n');hits[key]+=1
    except (OSError,ValueError) as e:gaps[rel]=str(e)
 db.commit();db.close();dump('screen-receipt.json',dict(paths=n,unique=u,seconds=time.monotonic()-start,hits=hits,excluded_names=ex,excluded_dirs=sorted(excluded_dirs),extensions=sorted(extensions),gaps=gaps,scope='hash-deduplicated lexical original/copy/tool screening, not semantic completeness; binary/pdf/compressed texts unsearched'))
 print(n,u,hits,'seconds',time.monotonic()-start)
elif sys.argv[1]=='focused':
 db=sqlite3.connect(L/'screen.sqlite');rx=re.compile(r'Beck.{0,35}(Sam|Woods)|2608\.02085|quasiperiod|minimum.period.conjecture|relaxed.{0,25}divisibility.chain',re.I)
 matches=[];total=0
 for h,path in db.execute('select h,path from bodies'):
  p=R/path
  # Never interpret generated scan outputs as original mathematics.
  if any(x in p.name.lower() for x in ['inventory','matches','semantic-hit','required-content','corpus','pathmap']):continue
  try:
   with p.open(errors='replace') as f:
    for num,line in enumerate(f,1):
     if rx.search(line):
      total+=1
      if len(matches)<65:matches.append(dict(sha256=h,path=path,line=num,text=line[:700]))
  except OSError:pass
 dump('focused-matches.json',dict(total=total,retained=matches,limit=65,scope='exact-target lexical rescreen; generated basename substrings excluded only for interpreting hits'))
 print(json.dumps(dict(total=total,retained=matches[:12]),indent=2))
 j=json.loads((L/'sources/omega-delta.json').read_text());o=json.loads((L/'sources/openai-head.json').read_text());head=json.loads((L/'sources/omega-head.json').read_text())
 dump('registry-coverage.json',dict(omega_head=head['sha'],openai_head=o['sha'],base='d254db264d94f6837888d045d5c12126faa84a5c',compare_status=j.get('status'),merge_base=j.get('merge_base_commit',{}).get('sha'),commits=j.get('total_commits'),returned_commits=len(j.get('commits',[])),paths=len(j.get('files',[])),capped=len(j.get('files',[]))>=300,target_path_hits=[f['filename'] for f in j.get('files',[]) if rx.search(f['filename'])],limits='path/patch response observation only; no all-body clearance. Earlier interval left to r4; no novelty PASS.'))
elif sys.argv[1]=='text':
 from html.parser import HTMLParser
 class Parser(HTMLParser):
  def handle_data(self,data):self.parts.append(data)
 p=Parser();p.parts=[];p.feed((L/'sources'/sys.argv[2]).read_text());(L/'sources'/(sys.argv[2]+'.txt')).write_text(' '.join(p.parts))
elif sys.argv[1]=='fetch':
 url,name=sys.argv[2:];receipt=dict(url=url,utc=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()))
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'Research source verification'})
  with urllib.request.urlopen(req,timeout=35) as r:data=r.read(8000000);receipt.update(status=r.status,content_type=r.headers.get('Content-Type'))
  (L/'sources'/name).write_bytes(data);receipt.update(copy='sources/'+name,sha256=sha(data),bytes=len(data))
 except Exception as e:receipt['error']=str(e)
 with (L/'http.jsonl').open('a') as f:f.write(json.dumps(receipt)+'\n')
 print(receipt)
