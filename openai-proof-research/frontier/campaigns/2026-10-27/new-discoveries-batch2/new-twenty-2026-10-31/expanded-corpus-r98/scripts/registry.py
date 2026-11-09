from fetch import get,D
import json,re,hashlib
h=json.loads((D/'sources/omega-head.json').read_text()); repo='https://api.github.com/repos/the-omega-institute/trureturing'
print(get(('omega-root.json',repo+'/git/trees/'+h['commit']['tree']['sha'])))
t=json.loads((D/'sources/omega-root.json').read_text())['tree']
for scope in ['D5','Problems']:
 e=next(x for x in t if x['path']==scope);print(get(('omega-'+scope+'.json',repo+'/git/trees/'+e['sha']+'?recursive=1')))
pat=r'370485|374274|382281|357901|358056|358320|358915|359211|359254|359916|360179|360364|360530|367278|382208|353162|353460|353951|354562|354574|markov|mourre|braid|procesi|weingarten|promotion|homomes|paley|hanson|ruzsa|ovoid|hypertree|super.standard|chain.type|flag.accur|genus|overpartition|chvatal|percolation'
out={'omega_head':h['sha'],'openai_head':json.loads((D/'sources/openai-head.json').read_text())['sha'],'scope':'complete path screen; bodies not read merely on no match','trees':{}}
for p in [D/'sources/omega-D5.json',D/'sources/omega-Problems.json',D.parent/'fresh-corpus-r10/sources/registry-preprints.json']:
 b=p.read_bytes();o=json.loads(b);out['trees'][str(p)]={'sha256':hashlib.sha256(b).hexdigest(),'truncated':o.get('truncated'),'hits':[e['path'] for e in o.get('tree',[]) if re.search(pat,e['path'],re.I)]}
(D/'outputs/registry-screen.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
