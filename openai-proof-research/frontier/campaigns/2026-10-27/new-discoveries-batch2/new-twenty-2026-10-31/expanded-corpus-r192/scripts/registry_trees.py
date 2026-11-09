import pathlib,json,runpy,sys
D=pathlib.Path(__file__).resolve().parents[1];args=[]
for name,repo,wanted in [('omega','the-omega-institute/trureturing',['D5','Problems']),('openai','openai/math',['preprints'])]:
 x=json.loads((D/f'sources/{name}-root.body').read_text())
 for z in x.get('tree',[]):
  if z['path'] in wanted:args += [name+'-'+z['path'],'https://api.github.com/repos/'+repo+'/git/trees/'+z['sha']+'?recursive=1']
sys.argv=[str(D/'scripts/fetch.py')]+args;runpy.run_path(str(D/'scripts/fetch.py'),run_name='__main__')
