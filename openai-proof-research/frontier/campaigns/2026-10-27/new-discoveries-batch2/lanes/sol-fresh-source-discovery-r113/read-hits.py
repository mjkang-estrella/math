from pathlib import Path
import json,re
L=Path(__file__).parent
pat=re.compile(r'ausm-2020-0020|nil.clean|nilpotents.{0,50}differences|bounded.{0,30}unit',re.I)
with (L/'screen-hits.jsonl').open() as f,(L/'screen-hit-excerpts.jsonl').open('w') as o:
 for line in f:
  try:r=json.loads(line)
  except ValueError:continue
  if any(t in r['path'].lower() for t in ['inventory','hashes','screen-content','duplicate-stream','screen-hits']):continue
  for m in pat.finditer(r['text']):
   o.write(json.dumps({'path':r['path'],'offset':r['offset']+m.start(),'context':r['text'][max(0,m.start()-160):m.end()+240]})+'\n')
