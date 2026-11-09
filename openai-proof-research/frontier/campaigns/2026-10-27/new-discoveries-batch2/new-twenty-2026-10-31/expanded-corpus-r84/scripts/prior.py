from fetch import get
from concurrent.futures import ThreadPoolExecutor
from urllib.parse import quote
q=[('fan-arxiv-search.html','https://arxiv.org/search/?query=Fan%2C+Jie&searchtype=author&abstracts=show&order=-announced_date_first&size=200'),('fan-journal.html','https://projecteuclid.org/journals/notre-dame-journal-of-formal-logic/volume-60/issue-2/A-Modal-Logic-of-Supervenience/10.1215/00294527-2019-0006.full'),('omega-D5.json','https://api.github.com/repos/the-omega-institute/trureturing/git/trees/6e91e980030ea4e9aff463322c43b656d9a7d393?recursive=1'),('omega-root.json','https://api.github.com/repos/the-omega-institute/trureturing/git/trees/560f621894c6a54800956f8196148084589ffb51')]
with ThreadPoolExecutor(max_workers=2) as ex:
 for x in ex.map(get,q):print(x,flush=True)
