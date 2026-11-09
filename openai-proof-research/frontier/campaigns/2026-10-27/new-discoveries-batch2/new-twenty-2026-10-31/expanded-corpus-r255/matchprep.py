import pathlib,json,re
L=pathlib.Path(__file__).resolve().parent; jobs=[]
pat=re.compile(r'(?:^|[/_-])toric|prefix.normal|kinser|dowling|toffoli|tamari|weakly.closed|folkman|whitham|concisen|polar.obstr|twinning|neumann.lara|lescure|manoussakis|motzkin|sum.product|homfly|knot.floer',re.I)
for n,repo in [('openai','openai/math'),('omega','the-omega-institute/trureturing'),('pool','Vilin97/lean-pool')]:
 head=json.loads((L/(n+'-head.body')).read_text())['sha']
 for p in L.glob(n+'-sub-*.body'):
  d=json.loads(p.read_text());print(p.name,'truncated',d.get('truncated'))
  prefix=p.stem.split('-sub-')[1]
  if d.get('truncated'):
   jobs.append([n+'-branch-'+prefix,'https://api.github.com/repos/'+repo+'/git/trees/'+d['sha']]);continue
  for x in d.get('tree',[]):
   path=prefix+'/'+x['path']
   if pat.search(path):print(n,path)
   if x['type']=='blob' and (pat.search(path) and path.endswith(('.tex','.lean','.md')) or n=='pool' and (path.endswith('projects.yml') or 'candidate' in path.lower() and path.endswith(('.json','.jsonl','.yml','.yaml','.md')))):
    jobs.append([n+'-body-'+str(len(jobs)),'https://raw.githubusercontent.com/'+repo+'/'+head+'/'+path])
(L/'matched-jobs.json').write_text(json.dumps(jobs))
