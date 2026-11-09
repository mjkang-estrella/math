exec(compile((__import__('pathlib').Path(__file__).parent/'fetch.py').read_text().split("if sys.argv[1]=='sources':")[0],str(__import__('pathlib').Path(__file__).parent/'fetch.py'),'exec'))
for i,o in json.loads((D/'extracted.json').read_text()).items():fetch(o['source_url'],i+'-abs.html')
for key,repo,scopes in [('omega','the-omega-institute/trureturing',['D5','Problems']),('openai','openai/math',['preprints'])]:
 sha=json.loads((D/f'sources/{key}-head.json').read_text())['sha'];r=fetch('https://api.github.com/repos/'+repo+'/git/trees/'+sha,key+'-root.json')
 if r.get('status')!=200:continue
 tree=json.loads((D/f'sources/{key}-root.json').read_text())
 for scope in scopes:
  sub=next((x for x in tree['tree'] if x['path']==scope),None)
  if sub:fetch('https://api.github.com/repos/'+repo+'/git/trees/'+sub['sha']+'?recursive=1',key+'-'+scope+'-tree.json')
