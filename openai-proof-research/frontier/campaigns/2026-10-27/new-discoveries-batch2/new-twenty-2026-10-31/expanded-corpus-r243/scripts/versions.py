import json,pathlib,re
L=pathlib.Path(__file__).resolve().parents[1];u=[]
for p in sorted((L/'sources').glob('*-abs/body')):
 a=p.parent.name[:-4];vs=sorted(set(map(int,re.findall(r'/abs/'+re.escape(a)+r'v(\d+)',p.read_text()))))
 for v in vs[:-1]:u.append([f'https://arxiv.org/pdf/{a}v{v}',f'{a}-v{v}-pdf'])
(L/'scripts/version-urls.json').write_text(json.dumps(u))
