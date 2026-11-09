from pathlib import Path
import importlib.util,json,re
L=Path(__file__).resolve().parents[1];s=importlib.util.spec_from_file_location('fetch',L/'scripts/fetch.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
urls={
'brettell2024.pdf':'https://www.math.canterbury.ac.nz/~c.semple/papers/BST24.pdf',
'wormald2026.pdf':'https://arxiv.org/pdf/2610.00086',
'aniceto2026.pdf':'https://arxiv.org/pdf/2608.00278',
'lin-proof.pdf':'https://cs.uwaterloo.ca/journals/JIS/VOL23/Gireesh/gireesh1.pdf',
'five-twist.pdf':'https://arxiv.org/pdf/2505.02578',
'cyclic-companion.pdf':'https://repository.essex.ac.uk/24270/1/MohamedWilliams-IsomorphismsCycPresGps.pdf',
'wormald-repo.json':'https://api.github.com/repos/jamesschreib/wormald-conjecture/commits/HEAD',
'omega-D5.json':'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/032c0855dad02224a58edb95814134a4f19976b4?recursive=1',
'omega-root.json':'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/'+json.loads((L/'outputs/the-omega-institute-trureturing-head.json').read_text())['sha'],
'openai-root.json':'https://api.github.com/repos/openai/math/git/trees/4eaee87548250b2682affda7d05d947c05554bae'}
for name,url in urls.items():
 b=m.fetch(url,name)
 if b:(L/'sources'/name).write_bytes(b)
for a in ['1902.04055','2604.12557','1808.01416','1810.07856','1711.01189']:
 h=(L/'sources'/f'{a}.html').read_text();vs=sorted(set(re.findall(a+r'v(\d+)',h)));print(a,'versions',vs)
 for v in vs:
  b=m.fetch('https://arxiv.org/pdf/'+a+'v'+v,a+'v'+v)
  if b:(L/'sources'/f'{a}v{v}.pdf').write_bytes(b)
