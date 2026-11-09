import pathlib,json,urllib.parse
L=pathlib.Path(__file__).resolve().parents[1]
u=[]
for n,r in [('leanpool','Vilin97/lean-pool'),('openai','openai/math'),('omega','the-omega-institute/trureturing')]:
 x=json.loads((L/f'sources/{n}-head/body').read_text());sha=x['sha']; print(n,sha)
 u.append([f'https://api.github.com/repos/{r}/git/trees/{sha}?recursive=1',n+'-tree'])
 if n=='leanpool':u.append([f'https://raw.githubusercontent.com/{r}/{sha}/projects.yml','leanpool-projects'])
q='(antipower OR "Lu Wenzel" OR "power domination" OR "restricted signed sumsets") lean'
u.append(['https://api.github.com/search/repositories?q='+urllib.parse.quote(q),'github-search-01'])
(L/'scripts/registry-more.json').write_text(json.dumps(u))
