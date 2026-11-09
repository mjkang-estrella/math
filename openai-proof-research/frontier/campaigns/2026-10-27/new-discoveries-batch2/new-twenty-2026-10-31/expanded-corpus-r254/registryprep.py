import pathlib,json,re
L=pathlib.Path(__file__).resolve().parent;jobs=[]
for k,r in [('openai','openai/math'),('omega','the-omega-institute/trureturing'),('pool','Vilin97/lean-pool')]:
 d=json.loads((L/(k+'-head.body')).read_text()); print(k,d['sha']); jobs.append((k+'-tree','https://api.github.com/repos/'+r+'/git/trees/'+d['commit']['tree']['sha']+'?recursive=1'))
 if k=='pool':jobs.append(('pool-projects','https://raw.githubusercontent.com/'+r+'/'+d['sha']+'/LeanPool/projects.yml'))
(L/'tree-jobs.json').write_text(json.dumps(jobs))
# versions not yet read (latest PDF already downloaded)
v=[]
for p in L.glob('*-abs.body'):
 a=p.name.split('-abs')[0];nums=[int(x) for x in re.findall(r'\[v(\d+)\]',p.read_text())]
 for n in range(1,max(nums)) :v.append((a+'v'+str(n)+'-pdf','https://arxiv.org/pdf/'+a+'v'+str(n)))
(L/'version-jobs.json').write_text(json.dumps(v))
