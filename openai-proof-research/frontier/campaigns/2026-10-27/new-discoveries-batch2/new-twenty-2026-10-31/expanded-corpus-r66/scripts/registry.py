from fetch import get,D
import json,hashlib
h=json.loads((D/'sources/omega-head.json').read_text())['sha']
print(get(('omega-root.json',f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{h}')))
r=json.loads((D/'sources/omega-root.json').read_text());out={'head':h}
for x in r['tree']:
 if x['path'] in ['D5','Problems']:
  k=x['path'];print(get((f'omega-{k}.json',x['url']+'?recursive=1')))
  p=D/f'sources/omega-{k}.json';o=json.loads(p.read_text());out[k]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'truncated':o.get('truncated'),'entries':len(o['tree']),'id_path_hits':{i:[a['path'] for a in o['tree'] if i in a['path']] for i in json.loads((D/'extracted.json').read_text())}}
p=D.parent/'fresh-corpus-r10/sources/registry-preprints.json';out['openai']={'head':json.loads((D/'sources/openai-head.json').read_text())['sha'],'inherited_tree':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
(D/'outputs/registry-screen.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
