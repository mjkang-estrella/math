import os,json,hashlib,sqlite3,time,re
from pathlib import Path
O=Path(__file__).parent;ROOT=O.parents[5]
assert ROOT.name=='openai-proof-research',str(ROOT)
db=sqlite3.connect(O/'audit-paths.sqlite')
db.execute('create table if not exists done(path text primary key)')
with open(O/'audit-manifest.jsonl') as f:
 for line in f:
  try:db.execute('insert or ignore into done values(?)',(json.loads(line)['path'],))
  except json.JSONDecodeError:pass
db.commit()
excluded=re.compile(r'(?:inventory[-_]content|required[-_]content|semantic[-_](?:hits|reads)|screen[-_]content|supplement[-_]content|duplicate[-_]corpus|join[-_]corpus)',re.I)
needles=[b'supertoken',b'super-token',b'myciel',b'hameed',b'semi-transitiv',b'word-represent',b'el zein',b'mortada',b'local girth',b'2412.20558',b'366438',b'2603.25113',b'373855']
counts={'files':0,'bytes':0,'excluded_generated':0,'errors':0}
with open(O/'audit-manifest-resumed.jsonl','w',buffering=1) as manifest,open(O/'audit-hits-resumed.jsonl','w',buffering=1) as hits,open(O/'audit-excluded-resumed.jsonl','w',buffering=1) as ex:
 for directory,dirs,files in os.walk(ROOT):
  dirs[:]=[d for d in dirs if d not in {'.git','node_modules','.lake','.venv','__pycache__'} and Path(directory)/d!=O]
  for name in files:
   p=Path(directory)/name;rel=str(p.relative_to(ROOT))
   if excluded.search(name):
    ex.write(json.dumps({'path':rel,'bytes':p.stat().st_size,'reason':'generated corpus echo; excluded without content read'})+'\n');counts['excluded_generated']+=1;continue
   if p.suffix.lower() not in {'.md','.txt','.json','.jsonl','.py','.sh','.lean','.tex','.html','.htm','.raw','.csv','.tsv','.yaml','.yml'}:continue
   if db.execute('select 1 from done where path=?',(rel,)).fetchone():continue
   h=hashlib.sha256();n=0;found={};carry=b''
   try:
    with open(p,'rb') as f:
     while b:=f.read(262144):
      h.update(b);low=(carry+b).lower()
      for needle in needles:
       at=low.find(needle)
       if at>=0 and found.get(needle.decode(),0)<2:
        found[needle.decode()]=found.get(needle.decode(),0)+1
        hits.write(json.dumps({'path':rel,'offset_approx':n+at-len(carry),'key':needle.decode(),'excerpt':low[max(0,at-120):at+len(needle)+280].decode('utf8','replace')})+'\n')
      carry=b[-64:];n+=len(b)
    manifest.write(json.dumps({'path':rel,'bytes':n,'sha256':h.hexdigest(),'matches':found})+'\n')
    counts['files']+=1;counts['bytes']+=n
   except OSError as e:counts['errors']+=1;ex.write(json.dumps({'path':rel,'error':str(e)})+'\n')
counts['utc']=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime());counts['status']='COMPLETE'
(O/'audit-result-resumed.json').write_text(json.dumps(counts,indent=2)+'\n');print(json.dumps(counts))
