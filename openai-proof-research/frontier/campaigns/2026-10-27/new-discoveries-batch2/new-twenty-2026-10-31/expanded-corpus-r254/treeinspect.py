import pathlib,json,re
L=pathlib.Path(__file__).resolve().parent
pat=re.compile('stirling|semiacyclic|bordeaux|soliton|gilbreath|quasisymmetric|two.stack|binomial|touching|borg|primitive|convex|wilf|corners|zero.divisor|spectral.ratio',re.I)
jobs=[]
for k,r in [('openai','openai/math'),('omega','the-omega-institute/trureturing'),('pool','Vilin97/lean-pool')]:
 p=L/(k+'-tree.body')
 if not p.exists():continue
 try:d=json.loads(p.read_text())
 except:continue
 print(k,'truncated',d.get('truncated'),len(d.get('tree',[])))
 for e in d.get('tree',[]):
  if (d.get('truncated') and e['type']=='tree' and e['path'] in ['preprints','LeanPool','D5']) :jobs.append((k+'-subtree-'+e['path'],'https://api.github.com/repos/'+r+'/git/trees/'+e['sha']+'?recursive=1'))
  if pat.search(e['path']):print(e['path'][:240])
(L/'subtree-jobs.json').write_text(json.dumps(jobs))
