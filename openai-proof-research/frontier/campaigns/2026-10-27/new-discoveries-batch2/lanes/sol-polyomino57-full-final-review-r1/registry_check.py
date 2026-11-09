import resource,signal,json,re,hashlib
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(210,210));signal.alarm(230)
D=Path('live');old=Path('../sol-fresh-source-discovery-r47/sources');r={}
for name in ['omega-D5.json','omega-Problems.json','openai-preprints.json','aim-tree.json','count-tree.json']:
 d=json.loads((D/name).read_text());assert d['truncated']==False
 baseline=json.loads((old/name).read_text());a={x['path']:x['sha'] for x in baseline['tree'] if x['type']=='blob'};b={x['path']:x['sha'] for x in d['tree'] if x['type']=='blob'}
 hits=[x for x in b if re.search('polyomino|omino|universal.?container|punctured.?diamond|395495',x,re.I)]
 r[name]=dict(entries=len(d['tree']),tree=d['sha'],delta=[x for x in a.keys()|b.keys() if a.get(x)!=b.get(x)],hits=hits)
Path('registry-results.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))
