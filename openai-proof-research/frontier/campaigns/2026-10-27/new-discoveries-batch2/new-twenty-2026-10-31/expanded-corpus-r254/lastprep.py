import pathlib,json,re
L=pathlib.Path(__file__).resolve().parent;d=json.loads((L/'openai-complete-lean.body').read_text());j=[]
for e in d['tree']:
 if e['path'] in ['OAI/Combinatorics','OAI/Algebra','OAI/Topology','OAI/Dynamics','OAI/NumberTheory'] and e['type']=='tree':j.append(('openai-branch-'+e['path'].split('/')[-1],'https://api.github.com/repos/openai/math/git/trees/'+e['sha']+'?recursive=1'))
# Read only actual subject match manuscripts; unrelated filename collisions not every section.
old=json.loads((L/'matched-jobs.json').read_text());j += [x for x in old if x[1].endswith('/build/paper.tex')]
j += [('source-journal-331498','https://doi.org/10.1016/j.ejc.2014.08.024'),('source-journal-331825','https://dmtcs.episciences.org/1408/pdf')]
(L/'last-jobs.json').write_text(json.dumps(j))
