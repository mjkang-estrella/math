import pathlib,json
L=pathlib.Path(__file__).resolve().parent;d=json.loads((L/'openai-narrow-OAI.body').read_text());print([e['path'] for e in d['tree']]);j=[]
for e in d['tree']:
 if e['path'] in ['Combinatorics','NumberTheory','Dynamics','GraphTheory','Topology','AlgebraicTopology','Discrete'] and e['type']=='tree':j.append(('openai-finalbranch-'+e['path'],'https://api.github.com/repos/openai/math/git/trees/'+e['sha']+'?recursive=1'))
(L/'branch-jobs.json').write_text(json.dumps(j))
