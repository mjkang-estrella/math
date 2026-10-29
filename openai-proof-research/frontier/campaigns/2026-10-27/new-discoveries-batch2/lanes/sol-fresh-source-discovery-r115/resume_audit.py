import os,re,json,hashlib,time,sqlite3
from pathlib import Path
lane=Path(__file__).resolve().parent;root=lane.parents[5]
assert root.name=='openai-proof-research',root
db=sqlite3.connect(lane/'audit-path-index.sqlite')
db.execute('create table if not exists seen(path text primary key)')
for line in (lane/'audit-manifest.jsonl').open():db.execute('insert or ignore into seen values(?)',(json.loads(line)['path'],))
db.commit()
exact=re.compile(r'(?<![\d.])2209[.]00986(?:v\d+)?(?![\d.])')
assert exact.search('2209.00986v2') and not exact.search('12209.00986') and not exact.search('2209.009860')
pat=re.compile(r'common.transversal|Aivazidis|Loukaki|sum of element orders|T[ăa]rn[ăa]uceanu|Giuga|arithmetic derivative|(?<![\d.])2209[.]00986(?:v\d+)?(?![\d.])',re.I)
gen=re.compile(r'inventory-content|required-content|supplement-content|screen-content|semantic-hits?|duplicate-corpus|screen-hits?|screen-hit-excerpts|(?:inventory|required|supplement|screen)-hashes',re.I)
start=time.monotonic();n=0;complete=True
with (lane/'audit-manifest.jsonl').open('a') as mf,(lane/'audit-matches.jsonl').open('a') as hf,(lane/'audit-exclusions.jsonl').open('a') as ef:
 for base,dirs,files in os.walk(root):
  dirs[:]=[d for d in dirs if d not in {'.git','.lake','node_modules','__pycache__'} and Path(base,d)!=lane]
  if time.monotonic()-start>170:complete=False;break
  for name in files:
   p=Path(base,name);rel=str(p.relative_to(root))
   if db.execute('select 1 from seen where path=?',(rel,)).fetchone():continue
   if gen.search(name):
    ef.write(json.dumps({'path':rel,'bytes':p.stat().st_size,'reason':'excluded generated corpus echo/index; no content read'})+'\n');db.execute('insert or ignore into seen values(?)',(rel,));continue
   if p.suffix.lower() not in {'.md','.txt','.tex','.py','.lean','.json','.jsonl','.html','.bib','.csv','.tsv'}:continue
   h=hashlib.sha256();size=0;hits=0;tail=b''
   try:
    with p.open('rb') as f:
     while True:
      b=f.read(65536)
      if not b:break
      h.update(b);size+=len(b)
      if hits<4:
       s=(tail+b).decode('utf8','replace')
       for m in pat.finditer(s):
        hf.write(json.dumps({'path':rel,'chunk_end_byte':size,'excerpt':s[max(0,m.start()-120):m.end()+240]})+'\n');hits+=1
        if hits>=4:break
      tail=b[-512:]
    mf.write(json.dumps({'path':rel,'sha256':h.hexdigest(),'bytes':size,'bounded_hits':hits})+'\n');mf.flush()
    db.execute('insert into seen values(?)',(rel,));n+=1
   except OSError as e:ef.write(json.dumps({'path':rel,'error':str(e)})+'\n')
db.commit();db.close()
receipt={'utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'new_files':n,'traversal_complete':complete,'seconds':time.monotonic()-start,'exact_regex_tests':'PASS','correction':'initial matcher had ID selftests but semantic-hit loop omitted bare IDs; supplemental exact-ID pass remains necessary for initial segment'}
with (lane/'audit-continuations.jsonl').open('a') as f:f.write(json.dumps(receipt)+'\n')
print(json.dumps(receipt))
