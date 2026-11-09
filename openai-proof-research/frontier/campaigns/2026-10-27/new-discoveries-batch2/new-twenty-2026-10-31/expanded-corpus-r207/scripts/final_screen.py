import json,re,hashlib
from pathlib import Path
L=Path(__file__).resolve().parents[1];D=json.loads((L/'outputs/exact-records.json').read_text());R=json.loads((L/'outputs/registry-screen.json').read_text());terms=['trialit','cyclically','frustration','copious','unicellular','excedance','132','adjacency','inducib','false.theta','bent','arrow','freiman','Nadler','Delaby','Helleseth','Archer','Laudone','Keith','Carrance','Bousquet','Chen','Keszegh','Rappaport','Strasser','Burr','Oudet','Maxwell']+[str(i) for i in D]+[x['record']['source_url'].split('/')[-1] for x in D.values()]
R['complete_subtree_screens']={}
for k in ['omega','openai']:
 for scope in ['D5','Problems','preprints']:
  if scope not in R[k]:continue
  p=Path(R[k][scope]['receipt'])/'body';T=json.loads(p.read_text());paths=[x['path'] for x in T['tree']];R['complete_subtree_screens'][k+'/'+scope]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'truncated':T.get('truncated'),'paths':len(paths),'hits':{t:[p for p in paths if re.search(t,p,re.I)] for t in terms if any(re.search(t,p,re.I) for p in paths)}}
R['github_search']=json.loads((L/'outputs/github-search.json').read_text());R['limitations']=['Eight spaced repository queries, not semantic search of all public Lean proofs.','Complete current D5/Problems/preprints path screens; proof bodies not exhaustively inspected.','Pool projects.yml and all candidates files fetched at current HEAD.','Broad search hits oph-gap-lean and lean4-experimentation README bodies concern unrelated topics.']
(L/'outputs/registry-screen.json').write_text(json.dumps(R,indent=2));print(json.dumps(R['complete_subtree_screens'],indent=2))
