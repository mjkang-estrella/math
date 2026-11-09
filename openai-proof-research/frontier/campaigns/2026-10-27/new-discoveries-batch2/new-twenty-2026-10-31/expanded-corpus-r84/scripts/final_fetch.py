from fetch import get
from concurrent.futures import ThreadPoolExecutor
from urllib.parse import quote
q=['"Neel walls" winding','"densely related" automaton','"spherical caps" simplex','"instanton" "flag" affine','"Ledet" conjecture','"three-valued" "Weil"','"Beilinson-Parshin"']
todo=[('catalogue-'+str(i)+'.html','https://arxiv.org/search/?query='+quote(s)+'&searchtype=all&abstracts=show&order=-announced_date_first&size=50')for i,s in enumerate(q)]
todo += [('openai-sylvester.tex','https://raw.githubusercontent.com/openai/math/4eaee87548250b2682affda7d05d947c05554bae/preprints/The-Selmer-converse-for-elliptic-curves-at-every-prime-October-7-2026/build/sections/10-sylvester-cube-sums.tex')]
with ThreadPoolExecutor(max_workers=2) as ex:
 for r in ex.map(get,todo):print(r,flush=True)
