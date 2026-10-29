from pathlib import Path
import json,re,collections
L=Path(__file__).parent
parts=[]
for suffix in ['', '-part2','-part3']:
 c=collections.Counter();last=None
 with (L/f'screen-hashes{suffix}.jsonl').open() as f:
  for s in f:
   try:r=json.loads(s)
   except ValueError:c['incomplete_trailing_json']+=1;continue
   c['files']+=1;c['errors']+=('error' in r);c['content_omitted']+=(r.get('content_streamed')==False);last=r['path']
   for token in ['summary','discovery','proof','findings','review','ledger','screened-out','agent','openproblem']:
    c[token]+=token in r['path'].lower()
 parts.append({'suffix':suffix,'counters':dict(c),'last':last})
pat=re.compile(r'ausm-2020-0020|nil.?clean|nilpotents.{0,50}differences',re.I);h=0
with (L/'target-hit-excerpts-final.jsonl').open('x') as out:
 for suffix in ['', '-part2','-part3']:
  with (L/f'screen-hits{suffix}.jsonl').open() as f:
   for s in f:
    try:r=json.loads(s)
    except ValueError:continue
    for m in pat.finditer(r['text']):
     out.write(json.dumps({'path':r['path'],'offset':r['offset']+m.start(),'context':r['text'][max(0,m.start()-120):m.end()+240]})+'\n');h+=1
(L/'audit-summary.json').write_text(json.dumps({'parts':parts,'target_hit_excerpts':h,'limitation':'Lexical screen with explicit generated-inventory content omissions, not atomic or global semantic clearance; supplement separately extends spelling and script languages.'},indent=2)+'\n')
print(json.dumps({'parts':len(parts),'target_excerpts':h,'files':sum(p['counters']['files'] for p in parts)}))
