from pathlib import Path
import json,re,hashlib
L=Path(__file__).resolve().parents[1]; D=json.loads((L/'outputs/exact-records.json').read_text());R=json.loads((L/'outputs/registry-screen.json').read_text()); terms=['trialit','cyclically','frustration','copious','unicellular','weak-excedance','adjacency','edge-inducibility','132-avoid','false-theta','bent-function','arrow-pattern','freiman','ramsey-finite']+[str(i) for i in D]+[x['record']['source_url'].split('/')[-1] for x in D.values()]
R['screen']={}
for kind in ['pool','omega','openai']:
 p=Path(R[kind]['tree_receipt'])/'body';t=json.loads(p.read_text()); paths=[x['path'] for x in t.get('tree',[])]; R['screen'][kind]={'truncated':t.get('truncated'),'hits':{term:[p for p in paths if term.lower() in p.lower()] for term in terms if any(term.lower() in p.lower() for p in paths)}}
 if kind=='pool':
  R['screen'][kind]['body_hits']={}
  for x in R[kind]['files']:
   body=(Path(x['receipt'])/'body').read_text()
   hits=[line for line in body.splitlines() if any(term.lower() in line.lower() for term in terms)]
   if hits:R['screen'][kind]['body_hits'][x['path']]=hits
(L/'outputs/registry-screen.json').write_text(json.dumps(R,indent=2));print(json.dumps(R['screen'],indent=2))
