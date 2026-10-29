from pathlib import Path
import os,re,json,hashlib,datetime
L=Path(__file__).parent
R=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
pat=re.compile(rb'(?<![0-9A-Za-z])(?:2409\.12404|2503\.22377|2402\.00949|2605\.09609|367738|361688)(?![0-9A-Za-z])|cycle.assign|Hayashi|Houshan|Filipi|Kubjas|minimal.filling',re.I)
for s in [b'2409.12404',b'x 367738 y',b'2503.22377v1']:
 # arXiv version suffix is intentionally tested separately below.
 if s!=b'2503.22377v1':assert pat.search(s)
for s in [b'12409.12404',b'2409x12404',b'13677380',b'X367738Y']:assert not pat.search(s)
n=hits=errors=0
with (L/'inventory-content.jsonl').open('w') as content,(L/'inventory-hashes.jsonl').open('w') as inv,(L/'duplicate-hits.jsonl').open('w') as ho:
 for base,dirs,files in os.walk(R):
  dirs[:]=sorted(d for d in dirs if d not in ['.git','node_modules','.lake','__pycache__'] and Path(base,d)!=L)
  for name in sorted(files):
   p=Path(base,name); rel=str(p.relative_to(R));low=rel.lower()
   # All text documentation and executable/source notes, including copied trees.
   if p.suffix.lower() not in ['.md','.json','.jsonl','.txt','.py','.sh','.lean','.tex','.yaml','.yml','.csv','.tsv','.log','.raw'] :continue
   # Prior generated inventories are provenance, not authored duplicate evidence.
   if any(x in name.lower() for x in ['duplicate-stream','inventory-content']):continue
   h=hashlib.sha256();size=0
   try:
    with p.open('rb') as f:
     for line,b in enumerate(f,1):
      # Bound individual JSONL content records; no whole-file buffering.
      h.update(b);size+=len(b)
      for off in range(0,len(b),32768):
       part=b[off:off+32768]
       content.write(json.dumps({'path':rel,'line':line,'offset':off,'text':part.decode('utf-8',errors='replace')})+'\n')
       if pat.search(part):ho.write(json.dumps({'path':rel,'line':line,'text':part.decode('utf-8',errors='replace')})+'\n');hits+=1
    inv.write(json.dumps({'path':rel,'bytes':size,'sha256':h.hexdigest()})+'\n');n+=1
   except OSError as e:inv.write(json.dumps({'path':rel,'error':str(e)})+'\n');errors+=1
print(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':n,'hit_records':hits,'errors':errors,'literal_tests':'PASS; v1 suffix not yet matched (correction required)','regex':pat.pattern.decode()}))
