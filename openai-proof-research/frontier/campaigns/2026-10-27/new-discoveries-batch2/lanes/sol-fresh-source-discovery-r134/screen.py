import os,sys,json,hashlib,gzip,re,time,sqlite3,zlib
from pathlib import Path
L=Path(__file__).resolve().parent; R=L.parents[5]
P=re.compile(rb'2607[.]05941|Hongyu.{0,8}Jia|Zhankui.{0,8}Xiao|zero.{0,12}Jordan.{0,12}product|zero.{0,10}product.{0,10}determined|zJpd|2407[.]00892|106693',re.I)
ext={'.md','.txt','.json','.jsonl','.py','.sh','.lean','.tex','.csv','.tsv','.html','.htm','.yaml','.yml','.toml','.bib','.rst','.log'}
roles=re.compile(r'inventory|pathmap|path-map|hash-path|screen-hits|corpus|search-matches|all-files|tree-cache|screen-content|supplement-content|required-content|semantic-hits|required-hashes|screen-hashes|supplement-hashes|duplicate-stream|matches[.]jsonl|matching-aliases',re.I)
skipdirs={'.git','node_modules','.lake','__pycache__','vendor','dist','build','.venv','venv'}
if sys.argv[1]=='scan':
 shard=int(sys.argv[2]); start=time.monotonic(); seen=set(); stats=dict(shard=shard,paths=0,bodies=0,hits=0,oversized=[],extensions_omitted={},role_paths=[],binary_paths=[],errors=[])
 with gzip.open(L/f'aliases-{shard}.jsonl.gz','wt') as aliases,(L/f'hits-{shard}.jsonl').open('w') as out:
  for root,dirs,files in os.walk(R):
   dirs[:]=[d for d in dirs if d not in skipdirs and Path(root)/d!=L]
   for name in files:
    p=Path(root)/name; rel=str(p.relative_to(R))
    if zlib.crc32(rel.encode())%4!=shard:continue
    if p.suffix.lower() not in ext:
     k=p.suffix.lower(); stats['extensions_omitted'][k]=stats['extensions_omitted'].get(k,0)+1;continue
    if roles.search(name):stats['role_paths'].append(rel);continue
    try:
     size=p.stat().st_size
     if size>12000000:stats['oversized'].append([rel,size]);continue
     b=p.read_bytes()
     if b'\0' in b:stats['binary_paths'].append(rel);continue
     h=hashlib.sha256(b).hexdigest();stats['paths']+=1;aliases.write(json.dumps([h,rel])+'\n')
     if h in seen:continue
     seen.add(h);stats['bodies']+=1
     hits=list(P.finditer(b))
     if hits:
      stats['hits']+=1;out.write(json.dumps(dict(path=rel,sha256=h,count=len(hits),excerpts=[[m.start(),b[max(0,m.start()-180):m.end()+300].decode(errors='replace')] for m in hits]))+'\n');out.flush()
    except OSError as e:stats['errors'].append([rel,str(e)])
 stats.update(seconds=time.monotonic()-start,pattern=P.pattern.decode(),global_hit_cutoff=None,excerpt_cutoff=None,extensions=sorted(ext),excluded_dirs=sorted(skipdirs),role_regex=roles.pattern)
 (L/f'history-{shard}.json').write_text(json.dumps(stats,indent=2)+'\n');print(shard,stats['paths'],stats['bodies'],stats['hits'],stats['seconds'])
elif sys.argv[1]=='merge':
 db=sqlite3.connect(L/'history.sqlite');db.execute('create table bodies(h text primary key,path text)');n=0
 with gzip.open(L/'history-aliases.jsonl.gz','wt') as a:
  for i in range(4):
   with gzip.open(L/f'aliases-{i}.jsonl.gz','rt') as f:
    for line in f:
     h,p=json.loads(line);a.write(line);db.execute('insert or ignore into bodies values(?,?)',(h,p));n+=1
 db.commit();u=db.execute('select count(*) from bodies').fetchone()[0];seen=set();hits=[]
 for i in range(4):
  for line in (L/f'hits-{i}.jsonl').open():
   j=json.loads(line)
   if j['sha256'] not in seen:
    seen.add(j['sha256']);b=(R/j['path']).read_bytes();j['reopened_sha256']=hashlib.sha256(b).hexdigest();j['unchanged']=j['reopened_sha256']==j['sha256'];hits.append(j)
 (L/'history-matches.json').write_text(json.dumps(hits,indent=2)+'\n')
 r=dict(paths=n,distinct_bodies=u,matching_bodies=len(hits),global_cutoff=None,all_dates=True,aliases='history-aliases.jsonl.gz',semantic_limit='Lexical only; shard receipts list format/size/role gaps; as-read not transactional')
 (L/'history-receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(r)
 for j in hits:print(j['path'],j['count'])
