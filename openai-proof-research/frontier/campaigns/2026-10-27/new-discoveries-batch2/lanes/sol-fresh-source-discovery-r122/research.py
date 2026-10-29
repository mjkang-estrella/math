import os,sys,json,hashlib,gzip,sqlite3,re,time,urllib.request
from pathlib import Path
L=Path(__file__).resolve().parent
R=L.parents[5]
B=L.parent.parent
def sha(b):return hashlib.sha256(b).hexdigest()
def dump(p,x):(L/p).write_text(json.dumps(x,indent=2)+'\n')
if sys.argv[1]=='context':
 paths=[R/'AGENTS.md',B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',B/'NEXT.md',R/'sources/upstream.json',R/'sources/CONTENTS.md',B/'lanes/root-renyi-acceptance-r1/ACCEPTANCE.md',B/'lanes/root-factorial-final-exclusion-r1/DECISION.md',B/'lanes/sol-fresh-source-discovery-r119/SUMMARY.md',B/'lanes/sol-fresh-source-discovery-r119/discovery.md',B/'lanes/sol-fresh-source-discovery-r119/registry-coverage.json',B/'lanes/root-factorial-final-exclusion-r1/EXCLUSION.json']
 rec=[]
 for i,p in enumerate(paths):
  data=p.read_bytes();dest=L/'sources'/('context-%02d'%i+p.suffix);dest.write_bytes(data)
  rec.append(dict(original=str(p),copy=str(dest.relative_to(L)),sha256=sha(data),bytes=len(data)))
  if p.name in ['ledger.json','prior-campaign-context.json']:
   j=json.loads(data);print(p.name,'keys',list(j))
   for k in ['accepted','rejected','outcomes','completed']:
    if isinstance(j.get(k),list):
     print(k,[(x.get('number'),x.get('title'),x.get('source_target')) for x in j[k] if isinstance(x,dict)])
  if p.name=='NEXT.md':
   lines=data.decode().splitlines();print('NEXT',len(lines),'lines; bounded rejection summary')
   print('\n'.join(s[:400] for s in lines if re.search('EXCLUD|exhaust|rejected|families',s,re.I))[:18000])
 dump('context-receipts.json',rec)
elif sys.argv[1]=='fetch':
 url,name=sys.argv[2:];receipt=dict(url=url,utc=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()))
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'Research source verification'})
  with urllib.request.urlopen(req,timeout=35) as r:
   data=r.read(8000001);receipt.update(status=r.status,content_type=r.headers.get('Content-Type'))
  if len(data)>8000000:raise ValueError('8MB cap')
  (L/'sources'/name).write_bytes(data);receipt.update(copy='sources/'+name,sha256=sha(data),bytes=len(data))
 except Exception as e:receipt['error']=str(e)
 with (L/'http.jsonl').open('a') as f:f.write(json.dumps(receipt)+'\n')
 print(receipt)
elif sys.argv[1]=='scan':
 start=time.monotonic();db=sqlite3.connect(L/'screen.sqlite');db.execute('create table bodies(h text primary key,path text)')
 exts={'.md','.txt','.json','.jsonl','.py','.sh','.lean','.tex','.csv','.tsv','.html','.htm','.yaml','.yml','.toml','.bib','.rst'}
 excluded_dirs={'.git','node_modules','.lake','__pycache__','vendor','dist','build'}
 rx=re.compile(r'ti\(G\)|TI.graph|4510\.pdf|Augmenting graphs|Goddard.{0,60}Henning|total dominating set and an independent',re.I)
 n=u=total=0;gaps=[];echo=0
 with gzip.open(L/'pathmap.jsonl.gz','wt') as out,open(L/'matches.jsonl','w') as mo:
  for root,dirs,files in os.walk(R):
   dirs[:]=[d for d in dirs if d not in excluded_dirs and Path(root)/d!=L]
   for name in files:
    p=Path(root)/name;rel=str(p.relative_to(R))
    if p.suffix.lower() not in exts:continue
    if any(s in name.lower() for s in ['inventory','matches','semantic-hit','required-content','corpus','pathmap']):echo+=1;continue
    if re.search(r'/sol-fresh-source-discovery-r11[123]/',rel):echo+=1;continue
    try:
     size=p.stat().st_size
     if size>12000000:gaps.append([rel,size]);continue
     h=hashlib.sha256()
     with p.open('rb') as f:
      while chunk:=f.read(65536):h.update(chunk)
     h=h.hexdigest();n+=1;out.write(json.dumps([h,rel])+'\n')
     try:db.execute('insert into bodies values (?,?)',(h,rel))
     except sqlite3.IntegrityError:continue
     u+=1
     with p.open(errors='replace') as f:
      for num,line in enumerate(f,1):
       if rx.search(line):
        total+=1
        if total<=100:mo.write(json.dumps(dict(h=h,path=rel,line=num,text=line[:700]))+'\n')
    except OSError as e:gaps.append([rel,str(e)])
 db.commit();db.close();dump('screen-receipt.json',dict(paths=n,unique=u,total_matches=total,retained=min(total,100),seconds=time.monotonic()-start,excluded_echo_files=echo,excluded_dirs=sorted(excluded_dirs),extensions=sorted(exts),gaps=gaps,scope='All-date selected text hash dedup. r111-r113 wholly excluded as echo; generated basename exclusions; no binary/compressed/large text clearance. Lexical only.'))
 print(n,u,total,time.monotonic()-start)
