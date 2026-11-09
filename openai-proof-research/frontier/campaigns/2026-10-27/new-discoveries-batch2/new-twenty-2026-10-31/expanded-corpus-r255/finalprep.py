import pathlib,json,re
L=pathlib.Path(__file__).resolve().parent; jobs=[]
for x in json.loads((L/'openai-branch-OAI.body').read_text())['tree']:
 if x['path'] in ['Algebra','Combinatorics','ComputerScience','Topology','AlgebraicTopology']:jobs.append(['openai-complete-'+x['path'],x['url']+'?recursive=1'])
d=json.loads((L/'pool-tree.body').read_text())
for x in d['tree']:
 if x['type']=='blob' and x['path'].startswith('candidates/') and x['path'].endswith('.txt'):jobs.append(['pool-txt-'+x['path'].split('/')[-1],'https://raw.githubusercontent.com/Vilin97/lean-pool/'+d['sha']+'/'+x['path']])
jobs.extend([['polar-author-journal','https://www.researchgate.net/publication/404357074_Polarity_on_H_-split_graphs'],['toffoli-proof-pdf','https://arxiv.org/pdf/1601.04950'],['dgr-proof-pdf','https://arxiv.org/pdf/2210.00878']])
(L/'final-jobs.json').write_text(json.dumps(jobs))
