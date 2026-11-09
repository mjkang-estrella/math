from fetch import get
items=[('1704.03083.html','https://arxiv.org/html/1704.03083'),('2210.03564.html','https://arxiv.org/html/2210.03564'),('1408.4713.html','https://arxiv.org/html/1408.4713'),('1412.4035.html','https://arxiv.org/html/1412.4035'),('1504.01923.html','https://arxiv.org/html/1504.01923'),('author-addendum.pdf','https://www.math.uaic.ro/~martar/pdf/articole/articol%2090.pdf'),('omega-tree.json','https://api.github.com/repos/the-omega-institute/trureturing/git/trees/62852be78d7b409ccf7316df232a073b3cda6f36?recursive=1'),('klen-catalogue.html','https://users.utu.fi/klena/publications.html')]
import concurrent.futures
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for x in ex.map(get,items):print(x,flush=True)
