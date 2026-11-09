import pathlib,json
L=pathlib.Path(__file__).resolve().parent; jobs=[]
for n,repo,want in [('openai','openai/math',{'preprints','lean'}),('omega','the-omega-institute/trureturing',{'D5','Problems','Blueprint'}),('pool','Vilin97/lean-pool',{'LeanPool'})]:
 for x in json.loads((L/(n+'-root.body')).read_text())['tree']:
  if x['path'] in want:jobs.append([n+'-sub-'+x['path'],x['url']+'?recursive=1'])
(L/'sub-jobs.json').write_text(json.dumps(jobs))
for p in L.glob('*citing-pdf.body'):
 import subprocess
 subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
