import pathlib,json
L=pathlib.Path(__file__).resolve().parents[1];u=[]
for name,repo,scopes in [('omega','the-omega-institute/trureturing',['Problems']),('openai','openai/math',['preprints'])]:
 x=json.loads((L/f'sources/{name}-root-nonrecursive/body').read_text())
 for z in x['tree']:
  if z['path'] in scopes:u.append([f"https://api.github.com/repos/{repo}/git/trees/{z['sha']}?recursive=1",name+'-'+z['path']+'-complete'])
(L/'scripts/scope-urls.json').write_text(json.dumps(u))
