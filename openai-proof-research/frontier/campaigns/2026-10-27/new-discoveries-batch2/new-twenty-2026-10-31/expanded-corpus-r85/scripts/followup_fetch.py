import sys,json,concurrent.futures
from fetch import get
D=None
todo=[('2501.14966.pdf','https://arxiv.org/pdf/2501.14966'),('2609.02850.pdf','https://arxiv.org/pdf/2609.02850'),('1802.08400.pdf','https://arxiv.org/pdf/1802.08400'),('omega-tree.json','https://api.github.com/repos/the-omega-institute/trureturing/git/trees/6e37b782cf6cfe60366783f4272ac2ab8645a3e6?recursive=1')]
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for v in ex.map(get,todo): print(v,flush=True)
