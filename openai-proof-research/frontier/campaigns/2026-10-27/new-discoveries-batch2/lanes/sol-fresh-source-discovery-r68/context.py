import json,pathlib,hashlib
b=pathlib.Path(__file__).resolve().parent; root=b.parents[1]
files=[root/'ledger.json',root/'prior-campaign-context.json',root/'NEXT.md']
for p in files:
 s=p.read_text();print(p.name,len(s),hashlib.sha256(p.read_bytes()).hexdigest())
 if p.suffix=='.json':
  d=json.loads(s)
  for k in ['accepted','rejected','excluded','held_candidates']:
   for x in d.get(k,[]):print(k,x.get('number'),x.get('title',x.get('source_target',x.get('mathdb_id'))))
p=root/'lanes/sol-polyomino57-full-final-review-r1/live/omega-D5.json'
d=json.loads(p.read_text()); hits=[x['path'] for x in d['tree'] if any(v in x['path'].lower() for v in ['rather','zerodivisor','semiproper','quasiregular','antiferro','leeseo','independence'])]
print('Actual Lean tree',d['sha'],hits)
(b/'context-screen.json').write_text(json.dumps({'input_hashes':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in files},'actual_lean_tree_sha':d['sha'],'registry_path_hits':hits},indent=2))
