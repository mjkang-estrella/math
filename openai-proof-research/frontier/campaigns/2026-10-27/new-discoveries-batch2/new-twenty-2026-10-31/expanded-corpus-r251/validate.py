from pathlib import Path
from itertools import product
import json
L=Path(__file__).resolve().parent
# Independent literal factor test for the word generation rule.
def pn(w):return all(sum(w[i:i+k])<=sum(w[:k]) for k in range(1,len(w)+1) for i in range(len(w)-k+1))
for n in range(1,13):
 c=sum(pn((1,)+s) for s in product((0,1),repeat=n-1))
 assert c==json.loads((L/'word-dfs-results.json').read_text())['level_counts'][n]
# Exact sums of Potts histogram coefficients.
ps=json.loads((L/'potts-results.json').read_text())
assert all(sum(p['histogram'])==p['q']**p['n'] for p in ps)
assert all(len(p['edges'])*2==p['d']*p['n'] for p in ps)
# Sanity-check the complete K4 specialization against dim(DH_3)=16.
# exec requires unified globals for the locally defined helpers.
ns={'__file__':str(L/'flow.py')};exec(compile((L/'flow.py').read_text().split('rows=[];Ps={}')[0],str(L/'flow.py'),'exec'),ns)
E=frozenset((i,j) for i in range(4) for j in range(i+1,4));P=ns['poly'](E,3)
print('K4 polynomial',sorted(P.items()),'dimension',sum(P.values()))
assert sum(P.values())==16
print('literal word counts n<=12, 72 Potts histogram totals, K4 dimension: PASS')
