import sys,json,pathlib,urllib.parse,time
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from fetch import get,D
sha=json.loads((D/'sources/pool-head.json').read_text())['sha']
get('pool-tree.json',f'https://api.github.com/repos/Vilin97/lean-pool/git/trees/{sha}?recursive=1')
t=json.loads((D/'sources/pool-tree.json').read_text())
files=[x['path'] for x in t['tree'] if x['type']=='blob' and (x['path']=='projects.yml' or x['path'].startswith('candidates/'))]
for p in files:get('pool-'+p.replace('/','_'),f'https://raw.githubusercontent.com/Vilin97/lean-pool/{sha}/{p}')
qs=['"natural orientation" lean','"Mabilat" lean','"Hopkins" "Rubey" lean','"Kanno" "regularity" lean','"weak shuffle" lean','"extremal" "pattern" lean','"2003.09704" lean','"2006.01470" lean']
search=[]
for n,q in enumerate(qs):
 if n:time.sleep(8)
 r=get(f'github-search-{n}.json','https://api.github.com/search/repositories?'+urllib.parse.urlencode({'q':q,'per_page':100}));search.append({'query':q,'receipt':r})
 if r.get('status') in (403,429):break
terms=[str(i) for i in json.loads((D/'reservation.json').read_text())['ids']]+[x['source_url'].rsplit('/',1)[-1] for x in json.loads((D/'extracted.json').read_text()).values()]+['Mabilat','Contreras','Rosevear','Hopkins','Rubey','Kanno','Grytczuk','shuffle','subgraph','quidd','Caldararu','Hurewicz','wheel','tableau','fertility']
hits=[]
for p in files:
 f=D/'sources'/('pool-'+p.replace('/','_'))
 if f.exists():
  for n,l in enumerate(f.read_text(errors='replace').splitlines(),1):
   ts=[s for s in terms if s.lower() in l.lower()]
   if ts:hits.append({'path':p,'line':n,'text':l,'terms':ts})
out={'pool_head':sha,'candidate_files':files,'tree_truncated':t.get('truncated'),'pool_hits':hits,'repository_search':search,'limits':'Path and metadata screen only; no blanket proof-body or novelty clearance.'}
(D/'outputs/registry-screen.json').write_text(json.dumps(out,indent=2)+'\n')
