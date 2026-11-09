from fetch import get,D
import json,hashlib
h=json.loads((D/'sources/omega-head.json').read_text())['sha']
print(get(('omega-root.json',f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{h}')))
x=json.loads((D/'sources/omega-root.json').read_text());res={}
ids=json.loads((D/'reservation.json').read_text())['ids']
for e in x['tree']:
 if e['path'] not in ['D5','Problems']:continue
 name='omega-'+e['path']+'.json';print(get((name,f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{e["sha"]}?recursive=1')))
 t=json.loads((D/'sources'/name).read_text());res[e['path']]={'tree_sha':e['sha'],'entries':len(t['tree']),'truncated':t.get('truncated'),'hits':{str(i):[v for v in t['tree'] if str(i) in v['path']] for i in ids}}
p=D.parent/'fresh-corpus-r10/sources/registry-preprints.json'
res['openai']={'current_head':json.loads((D/'sources/openai-head.json').read_text())['sha'],'cached_preprints':str(p),'cached_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'limit':'Unchanged current HEAD per brief; inherited complete preprints listing, path screen only.'}
res['limit']='Only complete D5/Problems path screens, not every proof body. No global novelty clearance.'
(D/'outputs/registry.json').write_text(json.dumps(res,indent=2)+'\n')
