import pathlib,json,sys,urllib.parse,time
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));from fetch import get
D=pathlib.Path(__file__).resolve().parents[1]
for repo,key in [('Vilin97/lean-pool','pool'),('the-omega-institute/trureturing','omega'),('openai/math','openai')]:
 sha=json.loads((D/f'sources/{key}-head.json').read_text())['sha'];get(key+'-tree.json',f'https://api.github.com/repos/{repo}/git/trees/{sha}?recursive=1')
 if key=='pool':get('pool-projects.yml',f'https://raw.githubusercontent.com/{repo}/{sha}/projects.yml')
queries=['"2505.04000" lean','"perfectly divisible" lean','"Klein bottle" lean','"Saxl" lean','"Anastos" "matching" lean','"chromatic homology" lean','"unicellular" "Ising" lean','"glued posets" lean']
for n,q in enumerate(queries):
 r=get(f'github-search-{n}.json','https://api.github.com/search/repositories?q='+urllib.parse.quote(q))
 if r.get('status') in (403,429):break
 time.sleep(9)
