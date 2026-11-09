import pathlib,json
L=pathlib.Path(__file__).resolve().parent;jobs=[]
a=json.loads((L/'openai-branch-lean.body').read_text());print('lean branches',[(x['path'],x['type']) for x in a['tree']])
for x in a['tree']:
 if x['type']=='tree':jobs.append(['openai-branch-'+x['path'],x['url']])
d=json.loads((L/'pool-tree.body').read_text());print('pool truncated',d.get('truncated'))
for x in d['tree']:
 path=x['path']
 if 'candidate' in path.lower() or path.endswith('projects.yml'):print('poolindex',path)
 if x['type']=='blob' and ('candidate' in path.lower() and path.endswith(('.json','.jsonl','.md','.yaml','.yml')) or path.endswith('projects.yml')):
  jobs.append(['pool-index-'+str(len(jobs)),'https://raw.githubusercontent.com/Vilin97/lean-pool/'+d['sha']+'/'+path])
old=json.loads((L/'matched-jobs.json').read_text())
for n,u in old:
 if any(s in u.lower() for s in ['prefix-normal','homflypt','obryant','sum-product-recurrence']):jobs.append(['narrow-'+n,u])
jobs.extend([['polar-journal','https://www.sciencedirect.com/science/article/pii/S0166218X26000168'],['toric-journal','https://www.sciencedirect.com/science/article/pii/S1071579714001443'],['prefix-full-pdf','https://www.socs.uoguelph.ca/~sawada/papers/pnf.pdf']])
(L/'narrow-jobs.json').write_text(json.dumps(jobs))
