import pathlib,importlib.util,json,urllib.parse
D=pathlib.Path(__file__).resolve().parents[1];s=importlib.util.spec_from_file_location('h',D/'scripts/http.py');h=importlib.util.module_from_spec(s);s.loader.exec_module(h)
for a in ['2401.04683']:
 h.get(a+'.abs.html','https://arxiv.org/abs/'+a);h.get(a+'.pdf','https://arxiv.org/pdf/'+a)
h.get('polygon-publisher.html','https://link.springer.com/article/10.1007/s00454-022-00438-0')
h.get('tree-published.pdf','https://cfc.nankai.edu.cn/_upload/article/files/d0/e0/14bed57849dab44905b374017424/f708f5f5-0ed0-4bf7-9743-56e17176a3cd.pdf')
h.get('meszaros-tanjaya.pdf','https://alco.centre-mersenne.org/item/10.5802/alco.200.pdf')
h.get('dennin.pdf','https://alco.centre-mersenne.org/item/10.5802/alco.422.pdf')
for repo,dirs in [('openai/math',['preprints']),('the-omega-institute/trureturing',['D5','Problems'])]:
 key=repo.replace('/','-');sha=json.loads((D/'sources'/(key+'-head.json')).read_text())['sha'];h.get(key+'-root.json','https://api.github.com/repos/'+repo+'/git/trees/'+sha)
 rt=json.loads((D/'sources'/(key+'-root.json')).read_text())
 for x in rt.get('tree',[]):
  if x['path'] in dirs:h.get(key+'-'+x['path']+'-complete.json','https://api.github.com/repos/'+repo+'/git/trees/'+x['sha']+'?recursive=1')
h.get('github-gao-lean.json','https://api.github.com/search/repositories?q='+urllib.parse.quote('Gao Schubert lean'))
