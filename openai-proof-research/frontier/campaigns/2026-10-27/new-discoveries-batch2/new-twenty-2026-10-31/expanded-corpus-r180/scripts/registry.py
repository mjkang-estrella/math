import pathlib,runpy,json,urllib.parse,time,re
D=pathlib.Path(__file__).resolve().parents[1]; mod=runpy.run_path(str(D/'scripts/fetch.py'));fetch=mod['fetch']; rec=mod['receipts']; result={}
for repo in ['Vilin97/lean-pool','the-omega-institute/trureturing','openai/math']:
 tag=repo.split('/')[-1];b=fetch(f'https://api.github.com/repos/{repo}/commits/HEAD',D/'sources'/f'{tag}-head.json')
 if not b:continue
 sha=json.loads(b)['sha']; result[repo]={'head':sha}
 tree=fetch(f'https://api.github.com/repos/{repo}/git/trees/{sha}?recursive=1',D/'sources'/f'{tag}-tree.json')
 if repo=='Vilin97/lean-pool' and tree:
  paths=[x['path'] for x in json.loads(tree)['tree'] if x['type']=='blob' and (x['path']=='projects.yml' or x['path'].startswith('candidates/'))]
  for n,p in enumerate(paths):fetch(f'https://raw.githubusercontent.com/{repo}/{sha}/{p}',D/'sources'/f'pool-{n}.txt')
  result[repo]['fetched_paths']=paths
queries=['"layered" "Jokar" lean','"Saxton" "permanent" lean','"2210.03336" lean','"2211.01893" lean','"quasi-kernel" lean','"supermagic" "cycles" lean','"inversion number" lean','"GaTEx" lean']
result['searches']=[]
for n,q in enumerate(queries):
 time.sleep(8)
 b=fetch('https://api.github.com/search/repositories?q='+urllib.parse.quote(q),D/'sources'/f'github-search-{n}.json')
 result['searches'].append({'query':q,'response':json.loads(b) if b else None})
 if not b:break
patterns=[str(i) for i in json.loads((D/'reservation.json').read_text())['ids']]+[r['source_url'].split('/')[-1] for r in json.loads((D/'reservation.json').read_text())['rows']]+['layered','Jokar','Saxton','quasi.kernel','supermagic','Cichacz','GaTEx','Hajebi','Golowich','cordial','inversion','perfect.*bas','Riesz']
result['pool_matches']={p.name:[l for l in p.read_text(errors='replace').splitlines() if re.search('|'.join(patterns),l,re.I)] for p in (D/'sources').glob('pool-*.txt')}
result['receipts']=rec
result['limits']='Path and keyword screen only; no global proof-body clearance. GitHub search at most eight spaced queries; stop on first failure.'
(D/'outputs/registry-screen.json').write_text(json.dumps(result,indent=2))
