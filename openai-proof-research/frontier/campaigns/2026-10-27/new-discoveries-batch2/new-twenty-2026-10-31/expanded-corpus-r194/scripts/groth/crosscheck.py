import json,sys,pathlib
exec(open(pathlib.Path(sys.argv[0]).with_name('common.py')).read())
n=6
w0=tuple(range(n,0,-1)); G={w0:{tuple(n-1-i for i in range(n)):1}}; layer=[w0]
while layer:
    nxt=[]
    for w in layer:
        for i in range(n-1):
            if w[i]>w[i+1]:
                v=list(w); v[i],v[i+1]=v[i+1],v[i]; v=tuple(v)
                if v not in G: G[v]=dd(G[w],i); nxt.append(v)
    layer=nxt
S=json.load(open(sys.argv[1])); bad=0
for k,s in S.items():
    w=tuple(int(c) for c in k)
    if sorted(map(list,G[w]))!=s: bad+=1
print('compared',len(S),'mismatches',bad)
# sanity: G_{2143} = x1 + x1 x2 x3 ... print a few
for k in ['213456','214356','132456']:
    print(k, sorted(G[tuple(int(c) for c in k)].items()))
