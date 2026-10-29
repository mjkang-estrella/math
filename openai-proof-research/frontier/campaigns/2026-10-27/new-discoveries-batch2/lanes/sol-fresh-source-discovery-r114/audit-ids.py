import json,re,time
from pathlib import Path
O=Path(__file__).parent;ROOT=O.parents[5]
rx=re.compile(rb'(?<![0-9])(?:2412[.]20558|366438|2603[.]25113|373855)(?![0-9])')
tests={b'2412.20558v1':True,b'/p/366438/':True,b'13664380':False,b'12412.205580':False,b'366438366758':False}
for s,v in tests.items():assert bool(rx.search(s))==v
files=matches=0
with open(O/'audit-exact-ids.jsonl','w') as out:
 for manifest in ['audit-manifest.jsonl','audit-manifest-resumed.jsonl']:
  with open(O/manifest) as meta:
   for line in meta:
    try:record=json.loads(line)
    except json.JSONDecodeError:continue
    p=ROOT/record['path'];carry=b'';offset=0;found=0
    try:
     with open(p,'rb') as f:
      while b:=f.read(262144):
       combined=carry+b
       for m in rx.finditer(combined):
        if found<4:
         out.write(json.dumps({'path':record['path'],'audited_sha256':record['sha256'],'source_id':m[0].decode(),'offset_approx':offset-len(carry)+m.start(),'excerpt':combined[max(0,m.start()-100):m.end()+180].decode('utf8','replace')})+'\n');found+=1;matches+=1
       carry=b[-64:];offset+=len(b)
     files+=1
    except OSError as e:out.write(json.dumps({'path':record['path'],'error':str(e)})+'\n')
(O/'audit-ids-result.json').write_text(json.dumps({'files':files,'matches':matches,'self_tests':5,'utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())},indent=2)+'\n')
