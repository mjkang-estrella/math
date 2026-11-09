import sys,json,time,math
from pathlib import Path
def vertices(n,k):
    out=[]
    def rec(start,left,mask):
        if left==0:
            if not(mask&1 and mask&(1<<(n-1))):out.append(mask)
            return
        for x in range(start,n-2*(left-1)):
            rec(x+2,left-1,mask|(1<<x))
    rec(0,k,0)
    assert len(out)==n*math.comb(n-k,k)//(n-k)
    return out
def diameter(n,k):
    V=vertices(n,k); N=len(V); adj=[];inc=[0]*n
    for j,a in enumerate(V):
        for x in range(n):
            if a>>x&1:inc[x]|=1<<j
    for a in V:
        forbidden=0
        for x in range(n):
            if a>>x&1:forbidden|=inc[x]
        adj.append(((1<<N)-1)^forbidden)
    seen=set();D=0; witness=None;cert=None;count=0;all_levels=[]
    for s,a in enumerate(V):
        if a in seen:continue
        count+=1
        for t in range(n):seen.add(((a<<t)|(a>>(n-t)))&((1<<n)-1))
        levels=[1<<s]; reached=1<<s
        while reached!=(1<<N)-1:
            union=0;f=levels[-1]
            while f:
                bit=f&-f; f-=bit;union|=adj[bit.bit_length()-1]
            f=union&~reached
            assert f
            levels.append(f);reached|=f
        all_levels.append([s,levels])
        if len(levels)-1>D:
            D=len(levels)-1; t=(levels[-1]&-levels[-1]).bit_length()-1
            witness=[s,t]; cert=levels
    row=dict(n=n,k=k,vertices=N,edges=sum(x.bit_count() for x in adj)//2,diameter=D,rotation_representatives=count,pair=[[i+1 for i in range(n) if V[j]>>i&1] for j in witness])
    if (n,k) in [(14,6),(22,10),(23,10),(27,12),(28,12),(29,13),(30,13)]:
        s,t=witness; path=[t]
        for level in reversed(cert[:-1]):
            t=(adj[t]&level&-(adj[t]&level)).bit_length()-1;path.append(t)
        row['path']=[[i+1 for i in range(n) if V[j]>>i&1] for j in reversed(path)]
        Path(f'outputs/graph-{n}-{k}-certificate.json').write_text(json.dumps(dict(vertices=V,adjacency=adj,source=s,levels=cert,witness=witness,representative_levels=all_levels)))
    print(json.dumps(row),flush=True);return row
k=int(sys.argv[1]);maxn=4*k-2 if k<=7 else 2*k+5
rows=[]
for n in ([int(sys.argv[2])] if len(sys.argv)>2 else range(2*k+1,maxn+1)):
    N=n*math.comb(n-k,k)//(n-k)
    cap=60000 if k<=7 else 4500
    if N>cap:print(json.dumps(dict(n=n,k=k,skip='vertex cap '+str(cap),vertices=N)),flush=True);continue
    rows.append(diameter(n,k))
    Path(f'outputs/graphs-k{k}'+(f'-n{sys.argv[2]}' if len(sys.argv)>2 else '')+'.json').write_text(json.dumps(rows,indent=2))
