import json,sys
for n in sys.argv[2:]:
    d=json.load(open(f'{sys.argv[1]}/level-{n}.json'))
    for adj in d['minimal_forbidden']:
        N=len(adj); E=[(u,v) for u in range(N) for v in range(u+1,N) if adj[u]>>v&1]
        deg=sorted((bin(a).count('1') for a in adj),reverse=True)
        tri=sum(1 for a in range(N) for b in range(a+1,N) for c in range(b+1,N) if adj[a]>>b&1 and adj[b]>>c&1 and adj[a]>>c&1)
        print(n,'m=',len(E),'deg',deg,'triangles',tri,'tree' if len(E)==N-1 else '','E',E)
