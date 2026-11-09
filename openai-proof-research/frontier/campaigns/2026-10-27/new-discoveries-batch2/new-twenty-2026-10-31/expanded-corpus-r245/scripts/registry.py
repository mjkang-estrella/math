import json,pathlib,subprocess,re,urllib.parse
D=pathlib.Path(__file__).resolve().parents[1];r=json.loads((D/'extracted.json').read_text());t=json.loads((D/'sources/pool-tree.body').read_text());paths=[x['path'] for x in t['tree']];c=[p for p in paths if 'candidates/' in p and p.endswith(('.md','.yml','.yaml','.json'))];(D/'outputs/pool-paths.json').write_text(json.dumps(paths,indent=2));print('candidate files',len(c),'truncated',t['truncated'])
head=json.loads((D/'sources/pool-head.body').read_text())['sha']
args=['pool-projects-correct','https://raw.githubusercontent.com/Vilin97/lean-pool/'+head+'/LeanPool/projects.yml']
for j,p in enumerate(c):args += ['pool-candidate-'+str(j),'https://raw.githubusercontent.com/Vilin97/lean-pool/'+head+'/'+urllib.parse.quote(p)]
subprocess.run(['python3','-I','-B',str(D/'scripts/fetch.py'),*args],check=True)
# Queries intentionally broad but conjunctive source/author + Lean; spaced to respect search limit.
queries=['"1803.06568" lean','unsplittable cyclic configurations lean','"1803.00540" lean','Muh le Nadeau noncrossing lean','"1805.02287" lean','"1805.00113" lean','"338739" lean','"338842" lean']
import time
for j,q in enumerate(queries):
 subprocess.run(['python3','-I','-B',str(D/'scripts/fetch.py'),'github-search-'+str(j),'https://api.github.com/search/repositories?q='+urllib.parse.quote(q)],check=True)
 rec=json.loads((D/'sources'/('github-search-'+str(j)+'.receipt.json')).read_text())
 if rec.get('status') in (403,429):break
 time.sleep(8)
