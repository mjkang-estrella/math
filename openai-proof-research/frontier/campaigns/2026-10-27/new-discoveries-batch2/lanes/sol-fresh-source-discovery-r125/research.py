import os,sys,json,hashlib,gzip,re,time,urllib.request,datetime,sqlite3
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
def utc():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(name,x): (HERE/name).write_text(json.dumps(x,indent=2)+'\n')
def fetch(url,name):
 r={'url':url,'utc':utc(),'file':name}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-source-check/1.0'}),timeout=35) as f:
   b=f.read(12000000);r.update(status=f.status,final_url=f.url,content_type=f.headers.get('Content-Type'),bytes=len(b),sha256=hashlib.sha256(b).hexdigest());(HERE/name).write_bytes(b)
 except Exception as e:r['error']=str(e)
 with (HERE/'http.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
 print(json.dumps(r))
def screen():
 start=time.monotonic(); db=sqlite3.connect(HERE/'screen.sqlite');db.execute('create table if not exists bodies(hash text primary key,path text)')
 patterns=[('imv-title',r'independent[\s–-]+mutual[\s–-]+visibility[\s–-]+colou?ring'),('imv-doi',r'01280-y|01280.y'),('imv-authors',r'(?:Peterin.{0,100}Samadi|Samadi.{0,100}Yero)'),('game-title',r'Builder.{0,10}Blocker.{0,15}mutual'),('game-authors',r'Ir.si.{0,25}Chenoweth')]
 pats=[(k,re.compile(v,re.I)) for k,v in patterns]; stats={'started_utc':utc(),'paths':0,'distinct':0,'duplicates':0,'binary':0,'large':0,'role_excluded':0,'unselected_extension':0,'errors':[],'large_paths':[],'scope':'all dates under openai-proof-research; no whole-lane exclusion; own lane excluded'}
 text_ext={'.md','.txt','.json','.jsonl','.py','.lean','.tex','.html','.htm','.csv','.tsv','.yaml','.yml','.rst','.log'}
 with gzip.open(HERE/'hash-paths.jsonl.gz','wt') as mapping,(HERE/'screen-hits.jsonl').open('w') as hits:
  for base,dirs,files in os.walk(ROOT):
   dirs[:]=[d for d in dirs if d not in {'.git','node_modules','.lake','__pycache__'} and Path(base,d)!=HERE]
   for fn in files:
    p=Path(base,fn); rel=str(p.relative_to(ROOT))
    if p.suffix.lower() not in text_ext:stats['unselected_extension']+=1;continue
    # Generated content roles only; original SUMMARY/discovery/proof/reviews remain included.
    if re.search(r'(?:inventory|pathmap|path-map|hash-path|screen-hits|corpus|search-matches|all-files|tree-cache)',fn,re.I):stats['role_excluded']+=1;continue
    try:
     if p.stat().st_size>12000000:stats['large']+=1;stats['large_paths'].append(rel);continue
     b=p.read_bytes();stats['paths']+=1
     if b'\0' in b:stats['binary']+=1;continue
     h=hashlib.sha256(b).hexdigest();mapping.write(json.dumps({'sha256':h,'path':rel})+'\n')
     try:db.execute('insert into bodies values(?,?)',(h,rel))
     except sqlite3.IntegrityError:stats['duplicates']+=1;continue
     stats['distinct']+=1;s=b.decode('utf-8',errors='replace')
     for key,pat in pats:
      matches=list(pat.finditer(s))
      if matches:
       excerpts=[{'offset':m.start(),'text':s[max(0,m.start()-160):m.end()+260]} for m in matches[:6]]
       hits.write(json.dumps({'target':key,'path':rel,'sha256':h,'match_count':len(matches),'excerpts':excerpts})+'\n')
    except Exception as e:stats['errors'].append({'path':rel,'error':str(e)})
 db.commit();stats.update(ended_utc=utc(),wall_seconds=time.monotonic()-start);save('screen-receipt.json',stats);print(json.dumps(stats))
if __name__=='__main__':
 if sys.argv[1]=='screen':screen()
 elif sys.argv[1]=='fetch':fetch(sys.argv[2],sys.argv[3])
