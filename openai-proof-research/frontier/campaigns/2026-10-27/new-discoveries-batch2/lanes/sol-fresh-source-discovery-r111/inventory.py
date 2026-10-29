import os,json,hashlib,re,datetime
from pathlib import Path
root=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
lane=Path(__file__).parent
counts={'files':0,'lines':0,'bytes':0,'errors':0}
with (lane/'inventory-content.jsonl').open('w') as out,(lane/'inventory-hashes.jsonl').open('w') as hashes:
 for base,ds,fs in os.walk(root):
  ds[:]=[d for d in ds if d not in {'.git','.lake','node_modules','__pycache__'} and Path(base,d)!=lane]
  for name in sorted(fs):
   p=Path(base,name)
   if p.suffix.lower() not in {'.md','.txt','.json','.jsonl','.py','.sh','.csv','.html','.htm'}:continue
   # Every eligible file, including copied reviews, agent briefs, embedded screens and scripts.
   h=hashlib.sha256();n=0
   try:
    with p.open('rb') as f:
     for i,line in enumerate(f,1):
      h.update(line);n+=len(line)
      out.write(json.dumps({'path':str(p.relative_to(root)),'line':i,'text':line.decode('utf-8','replace')},ensure_ascii=True)+'\n');counts['lines']+=1
    hashes.write(json.dumps({'path':str(p.relative_to(root)),'bytes':n,'sha256':h.hexdigest()})+'\n');counts['files']+=1;counts['bytes']+=n
   except OSError as e:
    out.write(json.dumps({'path':str(p),'error':str(e)})+'\n');counts['errors']+=1
counts['utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
print(json.dumps(counts));(lane/'inventory-receipt.json').write_text(json.dumps(counts,indent=2)+'\n')
