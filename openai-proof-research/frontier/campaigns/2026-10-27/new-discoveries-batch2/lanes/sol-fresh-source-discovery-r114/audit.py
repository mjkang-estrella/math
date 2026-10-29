import os,re,json,hashlib,time
from pathlib import Path
ROOT=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
OUT=Path(__file__).parent
patterns={
 'mycielski':rb'myciel|hameed|semi.transitiv|word.represent',
 'supertoken':rb'supertoken|super.token|reyes.{0,30}fiol|metric dimension',
 'localgirth':rb'el zein|mortada|local girth|373855',
 'source_ids':rb'(?<![0-9])(?:2603[.]25113|2511[.]12761|373855)(?![0-9])'}
rx={k:re.compile(v,re.I) for k,v in patterns.items()}
assert rx['source_ids'].search(b'arXiv:2603.25113v1')
assert rx['source_ids'].search(b'/p/373855/title')
assert not rx['source_ids'].search(b'13738550')
assert not rx['source_ids'].search(b'12603.251139')
excluded=re.compile(r'(?:inventory[-_]content|required[-_]content|semantic[-_](?:hits|reads)|screen[-_]content|supplement[-_]content|duplicate[-_]corpus|join[-_]corpus)',re.I)
counts={'files':0,'bytes':0,'excluded_generated':0,'hit_files':0,'errors':0}
with open(OUT/'audit-manifest.jsonl','w') as manifest,open(OUT/'audit-hits.jsonl','w') as hits,open(OUT/'audit-excluded.jsonl','w') as ex:
 for directory,dirs,files in os.walk(ROOT):
  dirs[:]=[d for d in dirs if d not in {'.git','node_modules','.lake','.venv','__pycache__'} and Path(directory)/d!=OUT]
  for name in files:
   p=Path(directory)/name;rel=str(p.relative_to(ROOT))
   if excluded.search(name):
    ex.write(json.dumps({'path':rel,'bytes':p.stat().st_size,'reason':'generated corpus echo; not mathematical source'})+'\n');counts['excluded_generated']+=1;continue
   if p.suffix.lower() not in {'.md','.txt','.json','.jsonl','.py','.sh','.lean','.tex','.html','.htm','.raw','.csv','.tsv','.yaml','.yml'}:continue
   h=hashlib.sha256();n=0;matched=False;bykey={}
   try:
    with open(p,'rb') as f:
     for line_no in range(1,1000000000):
      line=f.readline(65536)
      if not line:break
      h.update(line);n+=len(line)
      for key,r in rx.items():
       m=r.search(line)
       if m and bykey.get(key,0)<4:
        bykey[key]=bykey.get(key,0)+1;matched=True
        hits.write(json.dumps({'path':rel,'chunk_line':line_no,'key':key,'excerpt':line[max(0,m.start()-160):m.end()+320].decode('utf8','replace')})+'\n')
    manifest.write(json.dumps({'path':rel,'bytes':n,'sha256':h.hexdigest(),'matches':bykey})+'\n')
    counts['files']+=1;counts['bytes']+=n;counts['hit_files']+=matched
   except OSError as e:
    counts['errors']+=1;ex.write(json.dumps({'path':rel,'error':str(e)})+'\n')
counts['utc']=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())
(OUT/'audit-result.json').write_text(json.dumps(counts,indent=2)+'\n')
print(json.dumps(counts))
