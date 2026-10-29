import sys,os,json,hashlib,time,sqlite3,gzip,re,urllib.request,urllib.error
from pathlib import Path
L=Path(__file__).resolve().parent
R=L.parents[5]; B=L.parent.parent
def sha(b):return hashlib.sha256(b).hexdigest()
def dump(n,x):(L/n).write_text(json.dumps(x,indent=2)+'\n')
def utc():return time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())
if sys.argv[1]=='context':
 (L/'sources').mkdir(exist_ok=True)
 paths=[R/'AGENTS.md',B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',B/'NEXT.md',R/'sources/upstream.json']
 paths += [B/'lanes'/('root-r%d-handback'%i)/'DECISION.md' for i in range(119,124)]
 paths += [B/'lanes'/'sol-fresh-source-discovery-r124'/x for x in ['SUMMARY.md','discovery.md']]
 receipts=[]
 for i,p in enumerate(paths):
  b=p.read_bytes();dest='sources/context-%02d%s'%(i,p.suffix);(L/dest).write_bytes(b)
  receipts.append(dict(original=str(p),copy=dest,sha256=sha(b),bytes=len(b),utc=utc(),mutable=p.name=='NEXT.md'))
 dump('context-receipts.json',receipts)
 for p in paths[2:4]:
  j=json.loads(p.read_text());print(p.name,[(a['number'],a.get('title'),a.get('scope')) for a in j['accepted']])
elif sys.argv[1]=='scan':
 t=time.monotonic();db=sqlite3.connect(L/'screen.sqlite');db.execute('create table bodies(h text primary key,path text)')
 pattern=re.compile(r'18154061|aa6/|Phothila|Thoket|Kanasri|length of the longest arithmetic progressions|2610[.]19249|Guo.{0,30}Krattenthaler|graph binomial coefficients',re.I)
 ext={'.md','.txt','.json','.jsonl','.py','.sh','.lean','.tex','.csv','.tsv','.html','.htm','.yaml','.yml','.toml','.bib','.rst'}
 # Exclude generated retrieval echoes by filename role, never entire research lanes.
 skip={'inventory-content.jsonl','required-content.jsonl','semantic-hits.jsonl','duplicate-corpus.jsonl','matches.jsonl','pathmap.jsonl','semantic-matches.jsonl','target-matches.jsonl','target-specific-matches.jsonl'}
 skipdirs={'.git','node_modules','.lake','__pycache__','vendor','dist','build','.venv','venv'}
 n=u=hits=lines=0;omitted=[];excluded=[]
 with gzip.open(L/'pathmap.jsonl.gz','wt') as aliases,(L/'matches.jsonl').open('w') as out:
  for root,dirs,files in os.walk(R):
   dirs[:]=[d for d in dirs if d not in skipdirs and Path(root)/d!=L]
   for name in files:
    p=Path(root)/name;rel=str(p.relative_to(R))
    if name in skip:excluded.append(rel);continue
    if p.suffix.lower() not in ext:continue
    try:
     size=p.stat().st_size
     if size>12000000:omitted.append([rel,size]);continue
     h=hashlib.sha256()
     with p.open('rb') as f:
      while b:=f.read(65536):h.update(b)
     h=h.hexdigest();n+=1;aliases.write(json.dumps([h,rel])+'\n')
     try:db.execute('insert into bodies values (?,?)',(h,rel))
     except sqlite3.IntegrityError:continue
     u+=1;excerpts=[];count=0
     with p.open(errors='replace') as f:
      for i,line in enumerate(f,1):
       if pattern.search(line):
        count+=1;lines+=1
        if len(excerpts)<8:excerpts.append([i,line[:1000]])
     if count:hits+=1;out.write(json.dumps(dict(path=rel,sha256=h,count=count,excerpts=excerpts))+'\n')
    except OSError as e:omitted.append([rel,str(e)])
 db.commit();db.close()
 dump('screen-receipt.json',dict(utc=utc(),paths=n,bodies=u,matching_bodies=hits,matching_lines=lines,seconds=time.monotonic()-t,terms=pattern.pattern,global_cutoff=None,excerpt_limit=8,chars_per_excerpt=1000,excluded_roles=sorted(skip),excluded_paths=excluded,excluded_dirs=sorted(skipdirs),extensions=sorted(ext),omissions=omitted))
 print(n,u,hits,lines)
elif sys.argv[1]=='fetch':
 url,name=sys.argv[2:];rec=dict(url=url,utc=utc())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source verification'}),timeout=35) as r:
   b=r.read(8000001);rec.update(status=r.status,final_url=r.url,content_type=r.headers.get('Content-Type'))
  (L/'sources'/name).write_bytes(b);rec.update(copy='sources/'+name,sha256=sha(b),bytes=len(b),truncated=len(b)>8000000)
 except urllib.error.HTTPError as e:
  b=e.read(100000);(L/'sources'/name).write_bytes(b);rec.update(status=e.code,error=str(e),copy='sources/'+name,sha256=sha(b),bytes=len(b))
 except Exception as e:rec['error']=str(e)
 with (L/'http.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 print(rec)
elif sys.argv[1]=='aliases':
 matches=[json.loads(l) for l in (L/'matches.jsonl').open()];hs={j['sha256'] for j in matches};aliases=[]
 with gzip.open(L/'pathmap.jsonl.gz','rt') as f:
  for line in f:
   h,p=json.loads(line)
   if h in hs:aliases.append([h,p])
 dump('matching-aliases.json',aliases)
 print('matching bodies',len(matches),'aliases',len(aliases))
 print('Alias map saved; no content inventory printed.')
elif sys.argv[1]=='refine':
 t=time.monotonic();db=sqlite3.connect(L/'screen.sqlite')
 pat=re.compile(r'centered.reduced.residue|MirzavaziriYaqubi|Guo.Krattenthaler positivity|Fr_\{n,i\}|aperiodic.{0,20}subsets|2610[.]19249',re.I)
 excluded=[];docs=lines=0
 with (L/'refined-matches.jsonl').open('w') as out:
  for h,p in db.execute('select h,path from bodies'):
   if Path(p).name in {'duplicate-corpus.json','duplicate-report-files.txt','duplicate-corpus-paths.txt'}:excluded.append(p);continue
   count=0;ex=[]
   with (R/p).open(errors='replace') as f:
    for i,line in enumerate(f,1):
     if pat.search(line):
      count+=1;lines+=1
      if len(ex)<8:ex.append([i,line[:900]])
   if count:docs+=1;out.write(json.dumps(dict(path=p,sha256=h,count=count,excerpts=ex))+'\n')
 dump('refined-receipt.json',dict(utc=utc(),seconds=time.monotonic()-t,matching_bodies=docs,matching_lines=lines,terms=pat.pattern,global_cutoff=None,excerpt_limit=8,chars_per_excerpt=900,extra_generated_role_exclusions=excluded,scope='Every unique body from first stream except listed generated roles; original r111-r113 scientific reports retained. Initial format/size omissions still apply.'))
 print(docs,lines)
elif sys.argv[1]=='retain':
 paths=sys.argv[2:];rec=json.loads((L/'original-receipts.json').read_text()) if (L/'original-receipts.json').exists() else []
 for i,s in enumerate(paths,len(rec)):
  p=Path(s);b=p.read_bytes();dest='sources/original-%02d-%s'%(i,p.name);(L/dest).write_bytes(b)
  rec.append(dict(original=str(p),copy=dest,sha256=sha(b),bytes=len(b),utc=utc()))
 dump('original-receipts.json',rec);print('retained',len(rec))
elif sys.argv[1]=='freeze':
 mutable={r['copy'] for r in json.loads((L/'context-receipts.json').read_text()) if r['mutable']}
 rec=[]
 for p in sorted((L/'sources').iterdir()):
  rel=str(p.relative_to(L))
  if rel not in mutable:
   b=p.read_bytes();rec.append(dict(path=rel,bytes=len(b),sha256=sha(b)))
 dump('scientific-freeze.json',dict(utc=utc(),files=rec,mutable_context_excluded=sorted(mutable),scope='Local retained as-read copies only; source originals may change.'))
 db=sqlite3.connect(L/'screen.sqlite')
 originals=[]
 for h,p in db.execute('select h,path from bodies'):
  if re.search(r'sol-fresh-source-discovery-r11[123]/(discovery|SUMMARY|progress)[.]md$',p):originals.append([h,p])
 dump('retained-r111-r113-science.json',originals)
 print('scientific files',len(rec),'original r111-r113 scientific representatives',len(originals))
elif sys.argv[1]=='metadata':
 http=[json.loads(s) for s in (L/'http.jsonl').read_text().splitlines()]
 dump('primary-receipts.json',dict(utc=utc(),http=http,source_scope={'A6':'Exact unnumbered page14 conjecture; definitions, Lemma1, even Case2 proof and public all-step proof bodies read.','2610.19249v1':'Lemma4.1 and Theorem4.2 proof bodies, finite computation, large-n conclusion, free-part proof, final questions read.','1301.7651v2':'Literal original Conjecture7.4 read.'},external_lean_compile=False))
 guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
 dump('provenance.json',dict(lane=L.name,status='NO_ELIGIBLE_DISCOVERY',credit=0,counts_as_read={'additional':9,'total':39},utc=utc(),solo=True,children=False,writes_scope=str(L),git_actions=False,external_mutations=False,authored_lean_or_paper=False,primary_receipts='primary-receipts.json',context='context-receipts.json',scientific_freeze='scientific-freeze.json',original_dispositions='original-receipts.json',history=['screen-receipt.json','refined-receipt.json','pathmap.jsonl.gz','matching-aliases.json'],checks='check-results.json',resource_guard={'path':str(guard),'sha256':sha(guard.read_bytes()),'unchanged':True,'AS_bytes':536870912,'sampled_group_RSS_bytes':536870912,'CPU_seconds':210,'wall_seconds':230,'sample_ms':40,'BLAS_threads':1},registry={'omega_inherited':'a7769c386bd6072628a21cf4680756d2a49bf221','openai_inherited':'7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a','r119_observed_utc':'2026-10-29T22:21:24Z','d254_to_a776':{'commits':47,'paths':207,'uncapped':True,'semantic_clearance':False},'renyi_fixed_closure':{'base':'0d4df45','head':'d254db','steps':9,'commits':28,'paths':538},'factorial_final_review_to':'c3e8754','fresh_requests':'Two exact pinned proof bodies and their fixed-head path-filtered chronology only; no current HEAD observation or global absence clearance.'},search_queries=['site.integers-ejcnt.org 2026 conjecture polynomial divisibility','site.arxiv.org conjecture 2026 binomial divisibility polynomial','Phothila conjecture','Length of the longest arithmetic progressions conjecture proof','18154061 proof','Pongsriiam arithmetic progressions 2018','Phothila Thoket proof reduced residue','reduced residue system conjecture 2026','Thoket conjecture arithmetic','certain reduced proof conjecture longest progression','Guo Krattenthaler 7.4 proof positivity 2026'],limits=['Initial combined context output and aliases display truncated; saved data and subsequent bounded original reads control.','Historical text retrieval omits nonselected formats and >12MB bodies; no global match cutoff.','Generated .json echoes remained in initial pass and were excluded by role in refinement; base64 false positive ignored.','Shared history is as-read, not a transactional snapshot.','404 response retained; no 403/429 challenge or bypass occurred.','Chronology commits do not certify earliest public availability.','No genuinely fresh full-scope substantive source resolution achieved.']))
 print('metadata retained')
elif sys.argv[1]=='manifest':
 excluded={'finalmanifest.json','manifest-verification.json','manifest-verify.log'}
 entries=[]
 for p in sorted(L.rglob('*')):
  if p.is_file() and p.name not in excluded and '__pycache__' not in p.parts:
   b=p.read_bytes();entries.append(dict(path=str(p.relative_to(L)),bytes=len(b),sha256=sha(b)))
 dump('finalmanifest.json',dict(utc=utc(),files=entries,exclusions=sorted(excluded),note='Self and detached verification receipts excluded to avoid circular hashing.'))
 print(len(entries))
elif sys.argv[1]=='verify':
 m=json.loads((L/'finalmanifest.json').read_text());bad=[]
 for e in m['files']:
  p=L/e['path']
  if not p.is_file() or sha(p.read_bytes())!=e['sha256']:bad.append(e['path'])
 rec=dict(utc=utc(),status='PASS' if not bad else 'FAIL',checked=len(m['files']),bad=bad,manifest_sha256=sha((L/'finalmanifest.json').read_bytes()))
 dump('manifest-verification.json',rec);print(rec)
 assert not bad
