import pathlib,json,urllib.parse
L=pathlib.Path(__file__).resolve().parents[1];u=[]
for name,repo,scopes in [('omega','the-omega-institute/trureturing',['D5','Problems']),('openai','openai/math',['preprints'])]:
 x=json.loads((L/f'sources/{name}-tree/body').read_text())
 for z in x['tree']:
  if z['path'] in scopes:u.append([f"https://api.github.com/repos/{repo}/git/trees/{z['sha']}?recursive=1",name+'-'+z['path']+'-scope'])
sha=json.loads((L/'sources/omega-head/body').read_text())['sha']
for p in ['D5/S1/Words/Antipowers/GargFibonacciPrefixAntipower.lean','Blueprint/D5/S1/Words/Antipowers/GargFibonacciPrefixAntipower.md']:
 u.append([f'https://raw.githubusercontent.com/the-omega-institute/trureturing/{sha}/{p}','omega-garg-'+p.split('.')[-1]])
for url,n in [('https://www.trureturing.org/research/garg-2019-fibonacci-prefix-antipowers/','garg-web'),('https://arxiv.org/pdf/2004.07918','hyper-followup')]:u.append([url,n])
q='"chordless" "low degree" lean';u.append(['https://api.github.com/search/repositories?q='+urllib.parse.quote(q),'github-search-02'])
(L/'scripts/moreurls.json').write_text(json.dumps(u))
