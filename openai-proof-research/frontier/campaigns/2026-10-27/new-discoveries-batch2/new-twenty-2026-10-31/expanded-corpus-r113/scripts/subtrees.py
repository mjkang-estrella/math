import pathlib,json
from fetch import get
D=pathlib.Path(__file__).resolve().parents[1]
for name,repo,scopes in [('openai','openai/math',['preprints']),('omega','the-omega-institute/trureturing',['D5','Problems'])]:
 t=json.loads((D/f'sources/{name}-tree.json').read_text())
 for scope in scopes:
  row=next((x for x in t['tree'] if x['path']==scope),None)
  if row:
   key=name+'-'+scope+'.json';get((key,f"https://api.github.com/repos/{repo}/git/trees/{row['sha']}?recursive=1"));obj=json.loads((D/'sources'/key).read_text());print(name,scope,'truncated',obj.get('truncated'),'paths',len(obj.get('tree',[])))
   hits=[x['path'] for x in obj.get('tree',[]) if any(str(i) in x['path'] for i in json.loads((D/'reservation.json').read_text())['ids'])]; print('hits',hits)
  else:print(name,scope,'not in root truncated tree; not screened')
