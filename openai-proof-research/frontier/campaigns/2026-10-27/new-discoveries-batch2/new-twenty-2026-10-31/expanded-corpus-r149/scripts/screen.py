import json,pathlib,re,hashlib
L=pathlib.Path(__file__).resolve().parents[1];ids=json.loads((L/'reservation.json').read_text())['ids']
out={}
for name in ['omega-D5','omega-Problems','openai-preprints']:
 p=L/f'sources/{name}.json';d=json.loads(p.read_text())
 matches=[x for x in d['tree'] if any(re.search(r'(?<!\d)'+str(i)+r'(?!\d)',x['path']) for i in ids) or re.search('Bernstein|subcube|polychrom|Hall.Paige|Kneser|Kazhdan|Garland|sunflower|Biadjoint|Tight.Tree',x['path'],re.I)]
 out[name]=dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),truncated=d.get('truncated'),entries=len(d['tree']),matches=matches)
 print(name,len(d['tree']),d.get('truncated'))
 for x in matches: print(x['path'])
(L/'outputs/registry-screens.json').write_text(json.dumps(out,indent=2))
for name in ['campaign','batch','inherited']:
 d=json.loads((L/f'outputs/{name}-context.json').read_text());items=[]
 for kind in ['accepted','excluded','excluded_after_review']:
  for v in d.get(kind,[]):
   items.append({k:v[k] for k in ['mathdb_id','title','source_target','scope','reason','exact_endpoint'] if k in v})
 (L/f'outputs/{name}-families.json').write_text(json.dumps(items,indent=2))
