import runpy,pathlib,json
D=pathlib.Path(__file__).resolve().parents[1]; f=runpy.run_path(str(D/'scripts/fetch.py'))['fetch']
for repo in ['openai/math','Vilin97/lean-pool','the-omega-institute/trureturing']:
 label=repo.replace('/','-'); r=f('https://api.github.com/repos/'+repo+'/commits?per_page=1',label+'-head')
 try: sha=json.loads((D/r['steps'][-1]['file']).read_text())[0]['sha']
 except Exception:continue
 f('https://api.github.com/repos/'+repo+'/git/trees/'+sha+'?recursive=1',label+'-tree')
