import pathlib,json,re,subprocess,resource
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
L=pathlib.Path(__file__).resolve().parent; jobs=[]
pat=re.compile('toric|prefix.normal|kinser|dowling|toffoli|grassmann|tamari|weakly.closed|folkman|whitham|concisen|polar.obstr|twinning|neumann.lara|lescure|manoussakis|motzkin|sum.product|regularity|knot.floer',re.I)
for n,repo in [('openai','openai/math'),('omega','the-omega-institute/trureturing'),('pool','Vilin97/lean-pool')]:
 p=L/(n+'-tree.body')
 if not p.exists():continue
 d=json.loads(p.read_text());head=json.loads((L/(n+'-head.body')).read_text())['sha'];print(n,'truncated',d.get('truncated'))
 for x in d.get('tree',[]):
  path=x['path']
  if pat.search(path):print(n,path)
  if x['type']=='blob' and (pat.search(path) and path.endswith(('.tex','.lean','.md','.yml')) or n=='pool' and (path.endswith('projects.yml') or 'candidate' in path.lower() and path.endswith(('.json','.jsonl','.md','.yml')))):
   jobs.append([n+'-match-'+str(len(jobs)),'https://raw.githubusercontent.com/'+repo+'/'+head+'/'+path])
 if d.get('truncated'):
  root=L/(n+'-root.body')
  jobs.append([n+'-root','https://api.github.com/repos/'+repo+'/git/trees/'+head])
(L/'registry-jobs.json').write_text(json.dumps(jobs))
for p in L.glob('*v*-pdf.body'):subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
