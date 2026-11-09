import json, sys, itertools, random
d=json.load(open('runs/cert-n11-1.json'))
E=[set(x) for x in d['edges']]; Ys=[set(y) for y in d['blocker']]
# kill table: K[j][v] = edges i with E_i ∩ Y_j = {v}
K=[{v:[i for i in range(11) if E[i]&Y=={v}] for v in sorted(Y)} for Y in Ys]
def nodes(order):
    cnt=0
    def rec(k,a):
        nonlocal cnt; cnt+=1
        if any(all(any(i in a and a[i]==v for i in K[j][v]) for v in K[j]) for j in range(len(Ys))): return
        if k==11: raise Exception('sat!')
        i=order[k]
        for v in sorted(E[i]): rec(k+1,{**a,i:v})
    rec(0,{}); return cnt
print('identity order nodes',nodes(list(range(11))))
best=None; random.seed(1)
for t in range(int(sys.argv[1]) if len(sys.argv)>1 else 5):
    o=list(range(11)); random.shuffle(o); c=nodes(o)
    if best is None or c<best[0]: best=(c,o)
print('best random order',best)
