import pathlib,json,subprocess
p=pathlib.Path(__file__).resolve().parent
head=json.loads((p/'sources/omega-head.json').read_text())['sha']
paths=['Blueprint/D5/S1/Dynamics/MinimalFlowDilationMixing.md','D5/S1/Dynamics/MinimalFlowDilationMixing.lean']
for part in ['IncompleteBeta','IncompleteBetaShape']:
 for n in ['Defs','Result']:paths.append('D5/S3/Analytic/'+part+'/'+n+'.lean')
for i,x in enumerate(paths):
 subprocess.run(['python3',str(p/'fetch.py'),'registry-body-'+str(i)+'.txt','https://raw.githubusercontent.com/the-omega-institute/trureturing/'+head+'/'+x],check=True)
(p/'registry-body-paths.json').write_text(json.dumps(dict(enumerate(paths)),indent=2))
