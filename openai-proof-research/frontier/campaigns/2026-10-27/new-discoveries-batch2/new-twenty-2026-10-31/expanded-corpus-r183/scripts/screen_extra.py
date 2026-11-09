import sys,pathlib,json,hashlib
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from fetch import D,get
r=json.loads((D/'outputs/registry-screen.json').read_text());s=r['pool_head']
get('pool-projects.yml',f'https://raw.githubusercontent.com/Vilin97/lean-pool/{s}/projects.yml')
paths=[x['path'] for x in json.loads((D/'sources/pool-tree.json').read_text())['tree'] if 'project' in x['path'] and x['path'].endswith(('.yml','.yaml'))]
for p in paths:get('pool-'+p.replace('/','_'),f'https://raw.githubusercontent.com/Vilin97/lean-pool/{s}/{p}')
r['project_manifests']=paths
terms=['Mabilat','Quidd','Kreweras','WeakShuffle','Mammez','NaturalOrient','HotSpot','Caldararu','Hurewicz','LatinTable','WidePartition','BabaiGoodman','TightCycle']
scopes=[]
for p in (D.parent/'nanostar-parent-final-r1/registries').glob('*.paths'):
 data=p.read_bytes();hits=[l for l in data.decode().splitlines() if any(t.lower() in l.lower() for t in terms)]
 scopes.append({'path':str(p),'sha256':hashlib.sha256(data).hexdigest(),'hits':hits})
r['cached_omega_path_screens']=scopes
r['heads']={n:json.loads((D/f'sources/{n}-head.json').read_text())['sha'] for n in ['omega','openai','pool']}
for p in paths:
 f=D/'sources'/('pool-'+p.replace('/','_'))
 if f.exists():r.setdefault('manifest_hits',[]).extend([{'path':p,'line':n,'text':l} for n,l in enumerate(f.read_text().splitlines(),1) if any(t.lower() in l.lower() for t in terms)])
r['search_counts']=[{'query':x['query'],'total_count':json.loads((D/f'sources/github-search-{n}.json').read_text()).get('total_count')} for n,x in enumerate(r['repository_search'])]
(D/'outputs/registry-screen.json').write_text(json.dumps(r,indent=2)+'\n')
# Read structured ledger in full and retain family summary, with hashes.
ls=[]
for p in [D.parent/'ledger.json',D.parent.parent/'ledger.json',D.parent.parent/'prior-campaign-context.json']:
 o=json.loads(p.read_text());ls.append({'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'keys':list(o),'accepted':[{k:x.get(k) for k in ['mathdb_id','title','status','scope','substantive_reason']} for x in o.get('accepted',[])],'excluded':o.get('excluded',[])})
(D/'outputs/ledger-read.json').write_text(json.dumps(ls,indent=2)+'\n')
print(json.dumps({'heads':r['heads'],'manifests':paths,'omega_hits':scopes,'manifest_hits':r.get('manifest_hits',[]),'counts':r['search_counts']},indent=2))
