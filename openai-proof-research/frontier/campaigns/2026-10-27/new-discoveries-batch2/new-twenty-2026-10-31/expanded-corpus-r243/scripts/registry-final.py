import pathlib,json,re
L=pathlib.Path(__file__).resolve().parents[1];u=[]
x=json.loads((L/'sources/leanpool-head/body').read_text());sha=x['sha'];tree=json.loads((L/'sources/leanpool-tree/body').read_text())
for z in tree['tree']:
 p=z['path']
 if p=='LeanPool/projects.yml' or (p.startswith('candidates/') and z['type']=='blob'):
  u.append([f'https://raw.githubusercontent.com/Vilin97/lean-pool/{sha}/{p}','leanpool-file-'+p.replace('/','_')])
for url,n in [('https://arxiv.org/pdf/2504.09617','sumset-followup'),('https://trureturing.org/research/garg-2019-fibonacci-prefix-antipowers/','garg-proof'),('https://christokeller.website/naples_ex.pdf','naples-slides'),('https://arxiv.org/pdf/2108.02520','rainbow-followup'),('https://arxiv.org/pdf/2508.11636','rigidity-followup')]:u.append([url,n])
(L/'scripts/registry-final-urls.json').write_text(json.dumps(u))
