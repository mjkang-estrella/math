from pathlib import Path
import os,re,json,hashlib,datetime
L=Path(__file__).parent
R=L.parents[5]
assert R.name=='openai-proof-research',R
pat=re.compile(rb'(?<![A-Za-z0-9])(?:10\.2478/ausm-2020-0020|1605\.09534(?:v[0-9]+)?|2301\.07948(?:v[0-9]+)?)(?![A-Za-z0-9])|nil.clean|nilpotents.{0,50}differences|bounded.{0,30}unit',re.I)
for s in [b'10.2478/ausm-2020-0020',b'(1605.09534v2)',b'2301.07948'] :assert pat.search(s)
for s in [b'11605.09534',b'1605x09534',b'x2301.07948',b'2301.07948v2x',b'10x2478/ausm-2020-0020']:assert not pat.search(s)
n=hits=errors=omitted=0
with (L/'screen-content.jsonl').open('w') as co,(L/'screen-hashes.jsonl').open('w') as ha,(L/'screen-hits.jsonl').open('w') as ho:
 for base,dirs,files in os.walk(R):
  dirs[:]=sorted(d for d in dirs if d not in ['.git','node_modules','.lake','__pycache__'] and Path(base,d)!=L)
  for name in sorted(files):
   p=Path(base,name);rel=str(p.relative_to(R))
   if p.suffix.lower() not in ['.md','.json','.jsonl','.txt','.py','.sh','.lean','.tex','.yaml','.yml','.csv','.tsv','.log','.raw','.html']:continue
   # Generated full-content inventories are not authored evidence. Hash them,
   # but do not recursively duplicate their copied content in the content stream.
   generated=any(t in name.lower() for t in ['inventory-content','screen-content','duplicate-stream','audit-content','required-content'])
   h=hashlib.sha256();size=0;prev=b''
   try:
    with p.open('rb') as f:
     while b:=f.read(65536):
      h.update(b)
      if not generated:
       co.write(json.dumps({'path':rel,'offset':size,'text':b.decode('utf-8','replace')})+'\n')
       if pat.search(prev+b):ho.write(json.dumps({'path':rel,'offset':size,'text':(prev+b).decode('utf-8','replace')})+'\n');hits+=1
      size+=len(b);prev=b[-256:]
    ha.write(json.dumps({'path':rel,'bytes':size,'sha256':h.hexdigest(),'content_streamed':not generated})+'\n');n+=1;omitted+=generated
   except OSError as e:ha.write(json.dumps({'path':rel,'error':str(e)})+'\n');errors+=1
print(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':n,'hit_chunks':hits,'errors':errors,'generated_inventory_content_omissions':omitted,'literal_regex_tests':'PASS','root':str(R)}))
