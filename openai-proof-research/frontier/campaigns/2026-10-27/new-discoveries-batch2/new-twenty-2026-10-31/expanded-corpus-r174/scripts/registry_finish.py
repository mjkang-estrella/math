import pathlib,json,hashlib,importlib.util,re
L=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r174')
s=importlib.util.spec_from_file_location('fetch',L/'scripts/fetch.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
heads={name:json.loads((L/f'sources/{name}-head.json').read_text())['sha'] for name in ['leanpool','openai','omega']}
data=json.loads((L/'outputs/intake.json').read_text())
texts={str(p.relative_to(L)):p.read_text(errors='replace') for p in [L/'sources/leanpool-projects.yml',*list((L/'sources').glob('pool-*'))]}
screens={}
for i,x in data.items():
 r=x['record'];terms=[i,r['source_url'].split('/')[-1],r['title']]
 hits={}
 for term in terms:
  h=[{'path':p,'snippet':t[max(0,z.start()-150):z.end()+300]} for p,t in texts.items() for z in list(re.finditer(re.escape(term),t,re.I))[:4]]
  if h:hits[term]=h
 screens[i]=hits
# Exact known result body
m.fetch('https://raw.githubusercontent.com/the-omega-institute/trureturing/'+heads['omega']+'/D5/S3/Combinatorics/Graph/Eccentric/ZhangTianSteinerTreeRadius.lean','sources/ZhangTianSteinerTreeRadius.lean')
out={'heads':heads,'lean_pool_scope':'projects.yml and every candidates/ blob at HEAD; no all-proof semantic clearance','by_id':screens,'github_queries':json.loads((L/'outputs/github-queries.json').read_text()),'limitations':['Repository search indexes metadata, not code. Zero hits do not clear proofs.','Omega/OpenAI HEAD checked; their complete live proof trees not yet fetched.']}
(L/'outputs/registry-screen.json').write_text(json.dumps(out,indent=2))
print(heads)
print({i:list(x) for i,x in screens.items() if x})
