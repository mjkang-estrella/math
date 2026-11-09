import sys,json,itertools,importlib.util
L=sys.argv[1]
s=importlib.util.spec_from_file_location('ir',L+'/scripts/irgraph.py'); ir=importlib.util.module_from_spec(s); s.loader.exec_module(ir)
hits=[]
for line in open(L+'/outputs/irgraph-N9-chunks.jsonl'):
    d=json.loads(line); hits+= [(h[0],h[1]) for h in d['path_cycle_hits']]
classes={}
for adj,sh in hits:
    c=ir.canon(9,adj); classes.setdefault(c,(adj,sh,0))
    a,s_,k=classes[c]; classes[c]=(a,s_,k+1)
print('hits',len(hits),'iso classes',len(classes))
for c,(adj,sh,k) in classes.items():
    n=9; E=[(i,j) for i in range(n) for j in range(i+1,n) if adj[i]>>j&1]
    comp=[(i,j) for i in range(n) for j in range(i+1,n) if not adj[i]>>j&1]
    degs=sorted(bin(a).count('1') for a in adj)
    # automorphism count
    aut=0
    for p in itertools.permutations(range(n)):
        if all((adj[p[i]]>>p[j]&1)==(adj[i]>>j&1) for i in range(n) for j in range(i+1,n)): aut+=1
    tri=sum(1 for a,b,c2 in itertools.combinations(range(n),3) if adj[a]>>b&1 and adj[b]>>c2&1 and adj[a]>>c2&1)
    print(sh,'count',k,'|E|',len(E),'degs',degs,'aut',aut,'triangles',tri,'\n  E=',E,'\n  complement=',comp)
