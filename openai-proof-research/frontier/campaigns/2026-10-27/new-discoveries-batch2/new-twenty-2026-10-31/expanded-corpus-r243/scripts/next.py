import pathlib,json,re
L=pathlib.Path(__file__).resolve().parents[1]
u=[]
for p in sorted((L/'sources').glob('*-abs/body')):
 a=p.parent.name[:-4];s=p.read_text();vs=re.findall(r'/abs/'+re.escape(a)+r'v(\d+)',s);print(a,'versions',sorted(set(vs)))
 u.append([f'https://arxiv.org/pdf/{a}',a+'-pdf'])
(L/'scripts/pdf-urls.json').write_text(json.dumps(u))
u=[[f'https://api.github.com/repos/{r}/commits/HEAD',n+'-head'] for r,n in [('Vilin97/lean-pool','leanpool'),('openai/math','openai'),('the-omega-institute/trureturing','omega')]]
(L/'scripts/registry-urls.json').write_text(json.dumps(u))
