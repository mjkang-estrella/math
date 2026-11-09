import pathlib,json,re
P=pathlib.Path(__file__).resolve().parent/'fetch.py';ns={'__name__':'fetch','__file__':str(P)};exec(compile(P.read_text(),str(P),'exec'),ns);get=ns['get'];D=ns['D']
for a in ['1502.04068','1201.6629','1501.03238']:
 s=(D/'sources'/f'{a}-abs.html').read_text();vs=sorted(set(re.findall(r'\[v(\d+)\]',s)))
 for v in vs:get(a+'v'+v+'.pdf','https://arxiv.org/pdf/'+a+'v'+v)
for key,repo,scopes in [('omega','the-omega-institute/trureturing',['D5','Problems']),('openai','openai/math',['preprints'])]:
 sha=json.loads((D/'sources'/f'{key}-head.json').read_text())['sha'];get(key+'-root.json',f'https://api.github.com/repos/{repo}/git/trees/{sha}')
 for t in json.loads((D/'sources'/f'{key}-root.json').read_text()).get('tree',[]):
  if t['path'] in scopes:get(key+'-'+t['path']+'-tree.json',t['url']+'?recursive=1')
