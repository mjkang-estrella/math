from fetch import get
from concurrent.futures import ThreadPoolExecutor
q=[('1903.08737.pdf','https://arxiv.org/pdf/1903.08737'),('2610.26670.pdf','https://arxiv.org/pdf/2610.26670'),('supervenience-classical.html','https://arxiv.org/search/?query=%22propositional+logic+of+determinacy%22&searchtype=all&abstracts=show&order=-announced_date_first&size=50'),('maxrank-followup.html','https://arxiv.org/search/?query=%22fat+line%22&searchtype=all&abstracts=show&order=-announced_date_first&size=50'),('signature-followup.html','https://arxiv.org/search/?query=%22signature+varieties%22&searchtype=all&abstracts=show&order=-announced_date_first&size=50')]
with ThreadPoolExecutor(max_workers=2) as ex:
 for r in ex.map(get,q):print(r,flush=True)
