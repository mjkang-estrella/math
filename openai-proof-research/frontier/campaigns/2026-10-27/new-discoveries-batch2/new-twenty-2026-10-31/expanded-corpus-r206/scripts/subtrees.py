import pathlib,json,sys,re
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));from net import get,D
for key,repo,names in [('omega','the-omega-institute/trureturing',['D5','Problems']),('openai','openai/math',['preprints'])]:
 head=json.loads((D/f'sources/{key}-head.json').read_text())['sha'];get(key+'-root.json',f'https://api.github.com/repos/{repo}/git/trees/{head}')
 root=json.loads((D/f'sources/{key}-root.json').read_text())
 for o in root['tree']:
  if o['path'] in names:get(key+'-'+o['path']+'-complete.json',f'https://api.github.com/repos/{repo}/git/trees/{o["sha"]}?recursive=1')
