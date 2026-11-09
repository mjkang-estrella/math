from pathlib import Path
import json,re
L=Path(__file__).resolve().parent; D=L/'http'
terms=r'andrew|maced|recalcitr|hamada|queen|stahl|kneser|gessel|zhuang|peak|star.forest|transversal|latin|dewar|rigid|antidirect|agrawal|triple.array|triangle.free.*cycl|assembly|adjacency.dimension|extendab|bow.tie|wheel|immersion|mubayi|regular.subgraph|skew.symmetr|reversal|laplacian|spectral.radius'
jobs=[];report={}
for name,repo in [('openai','openai/math'),('omega','the-omega-institute/trureturing'),('pool','Vilin97/lean-pool')]:
 t=json.loads((D/(name+'-tree.json')).read_text());h=json.loads((D/(name+'-head.json')).read_text())['sha'];report[name]={'head':h,'truncated':t.get('truncated'),'hits':[]}
 for x in t.get('tree',[]):
  p=x['path']
  if x['type']=='tree' and t.get('truncated') and (p in ['preprints','candidates','proofs','formalizations']):jobs.append([name+'-subtree-'+p+'.json',f'https://api.github.com/repos/{repo}/git/trees/{x["sha"]}?recursive=1'])
  if x['type']=='blob' and re.search(terms,p,re.I):report[name]['hits'].append(p)
  if name=='pool' and x['type']=='blob' and p.startswith('candidates/') and '/' not in p[len('candidates/'):]:jobs.append(['pool-index-'+p.replace('/','--'),f'https://raw.githubusercontent.com/{repo}/{h}/{p}'])
(L/'registry-screen.json').write_text(json.dumps(report,indent=2));(L/'registry-jobs.json').write_text(json.dumps(jobs))
print(json.dumps(report,indent=2)[:17000]);print('jobs',len(jobs))
