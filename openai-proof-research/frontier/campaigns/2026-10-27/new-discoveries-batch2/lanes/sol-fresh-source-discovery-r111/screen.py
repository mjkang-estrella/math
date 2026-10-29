import os,re,json,hashlib,datetime
from pathlib import Path
root=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research');lane=Path(__file__).parent
terms={'maxwell':r'Maxwell1D|relative Maxwell|Conjecture 1\.8|2609\.09637','entropy2':r'2210\.12842|2409\.03664|Kneser.{0,3}Poulsen.*entropy','reverseEPI':r'2510\.09206|Borowiecki','BNT':r'2609\.11418|Ball.{0,12}Nayar.{0,12}Tkocz'}
tests=[]
for id in ['2210.12842','2409.03664','2510.09206','2609.09637','2609.11418']:
 pat=re.compile(r'(?<![0-9])'+re.escape(id)+r'(?![0-9])')
 assert pat.search('arxiv:'+id+'v2');assert not pat.search('9'+id);assert not pat.search(id+'7');assert not pat.search(id.replace('.','x'))
 tests.append({'id':id,'positive':True,'negative_prefix_suffix_dot':True})
patterns={k:re.compile(v,re.I) for k,v in terms.items()};nf=nl=nh=0
with (lane/'required-content.jsonl').open('w') as out,(lane/'required-hashes.jsonl').open('w') as hashes,(lane/'duplicate-hits.jsonl').open('w') as hits:
 for base,ds,fs in os.walk(root):
  ds[:]=[d for d in ds if d not in {'.git','.lake','node_modules','__pycache__'} and Path(base,d)!=lane]
  for name in sorted(fs):
   p=Path(base,name);rel=str(p.relative_to(root));low=rel.lower()
   if p.suffix.lower() not in {'.md','.txt','.json','.jsonl','.py','.sh','.html','.csv'}:continue
   required=any(s in name.lower() for s in ['summary','discovery','proof','findings','review','ledger','screened-out','next.md','prior-campaign','agents.md']) or any(s in low for s in ['/tools/','/scripts/','agent','openproblem','review'])
   if not required:continue
   h=hashlib.sha256();size=0
   try:
    with p.open('rb') as f:
     for i,b in enumerate(f,1):
      h.update(b);size+=len(b);s=b.decode('utf-8','replace');row={'path':rel,'line':i,'text':s};out.write(json.dumps(row)+'\n');nl+=1
      for k,pat in patterns.items():
       if pat.search(s):hits.write(json.dumps(dict(row,target=k))+'\n');nh+=1
    hashes.write(json.dumps({'path':rel,'bytes':size,'sha256':h.hexdigest()})+'\n');nf+=1
   except OSError as e:out.write(json.dumps({'path':rel,'error':str(e)})+'\n')
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':nf,'lines':nl,'hits':nh,'literal_id_tests':tests,'scope':'all-date required named artifacts, all copied review trees, tools/scripts/agent/openproblem text; each selected file streamed in full'}
(lane/'screen-receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt))
