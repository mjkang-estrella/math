import sys
sys.argv.append('closest')
from research import get
for n,u in [('el.pdf','https://www.math.uci.edu/~brusso/ElduqueAutoGraph.pdf'),('permutation.html','https://link.springer.com/article/10.1007/s00009-025-02924-0'),('groth.html','https://arxiv.org/html/2607.15154v1'),('groth-abs.html','https://arxiv.org/abs/2607.15154')]:
 b=get(n,u);print(n,len(b) if b else None,flush=True)
