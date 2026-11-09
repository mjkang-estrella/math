from fetch import get
from concurrent.futures import ThreadPoolExecutor
q=[('2610.09298.pdf','https://arxiv.org/pdf/2610.09298'),('ignat-catalogue.html','https://arxiv.org/search/?query=Ignat%2C+Radu&searchtype=author&abstracts=show&order=-announced_date_first&size=200')]
with ThreadPoolExecutor(max_workers=2) as ex:
 for r in ex.map(get,q):print(r,flush=True)
