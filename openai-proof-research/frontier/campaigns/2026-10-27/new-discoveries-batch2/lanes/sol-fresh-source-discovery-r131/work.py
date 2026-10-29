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
 paths += [B/'lanes'/('root-r%d-handback'%i)/'DECISION.md' for i in range(119,126)]
 paths += [B/'lanes'/'root-r126-r127-handback'/'DECISION.md']
 receipts=[]
 for i,p in enumerate(paths):
  b=p.read_bytes();dest='sources/context-%02d%s'%(i,p.suffix);(L/dest).write_bytes(b)
  receipts.append(dict(original=str(p),copy=dest,sha256=sha(b),bytes=len(b),utc=utc(),mutable=p.name=='NEXT.md'))
 dump('context-receipts.json',receipts)
 for p in paths[2:4]:
  j=json.loads(p.read_text());print(p.name,[(a['number'],a.get('title'),a.get('scope')) for a in j['accepted']])
elif sys.argv[1]=='scan':
 t=time.monotonic();db=sqlite3.connect(L/'screen.sqlite');db.execute('create table bodies(h text primary key,path text)')
 pattern=re.compile(r'15283716|z39/|Cullinan|Gajek.Leonard|Yamamura|truncated logarithm|17535327|z102/|Adutwum|Tougouma|distributions of Ulam words|Ulam.words|17711561|z105/|Di.Nasso|Renling.Jin|pairwise.sum.theorem|Schur.{0,30}pairwise',re.I)
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
 pat=re.compile(r'2401[.]14138|2410[.]01217|15283716|z39/|Cullinan|Gajek.Leonard|Yamamura|truncated logarithm|17535327|z102/|Adutwum|Tougouma|distributions of Ulam words|Ulam.words|17711561|z105/|Di.Nasso|Renling.Jin|pairwise.sum.theorem|Schur.{0,30}pairwise|PR.witness.{0,50}S.?2',re.I)
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
 db=sqlite3.connect(L/'history.sqlite')
 originals=[]
 for h,p in db.execute('select h,path from bodies'):
  if re.search(r'sol-fresh-source-discovery-r11[123]/(discovery|SUMMARY|progress|PROOF|review)[.]md$',p):originals.append([h,p])
 dump('retained-r111-r113-science.json',originals)
 print('scientific files',len(rec),'original r111-r113 scientific representatives',len(originals))
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
