from fetch import get,D
from concurrent.futures import ThreadPoolExecutor
from urllib.parse import quote
q=['supervenience','prime power Giuga','fat line maximal rank','stopping near the top','polar degree','signature varieties','virtual knot Alexander slice','Krattenthaler divisibility']
todo=[('followup-'+str(i)+'.html','https://arxiv.org/search/?query='+quote(s)+'&searchtype=all&abstracts=show&order=-announced_date_first&size=50')for i,s in enumerate(q)]
todo.append(('omega-Problems.json','https://api.github.com/repos/the-omega-institute/trureturing/git/trees/2738632a49f0876581f75265830f741cc3ba46ec?recursive=1'))
with ThreadPoolExecutor(max_workers=2) as ex:
 for r in ex.map(get,todo):print(r,flush=True)
