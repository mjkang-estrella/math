from fetch import *
todo=[('alfaro-later.pdf','https://d-nb.info/1302174029/34'),('real-ranks.pdf','https://arxiv.org/pdf/0808.0048'),('index-later.pdf','https://jihaoliu.org/notes/ET74.pdf'),('window-release.html','https://www.evidencepress.org/releases/sharp-shannon-window-law/'),('loop-author.html','https://cs.du.edu/~petr/loops/'),('loop-papers.html','https://cs.du.edu/~petr/papers/'),('jmlr.pdf','https://jmlr.org/papers/volume17/15-106/15-106.pdf')]
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for v in ex.map(get,todo):print(v,flush=True)
