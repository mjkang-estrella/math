import json,math
from pathlib import Path
summary=[]
for p in sorted(Path('outputs').glob('graph-*-certificate.json')):
    _,nn,kk,_=p.name.split('-');n=int(nn);k=int(kk)
    d=json.loads(p.read_text());V=d['vertices'];adj=d['adjacency'];N=len(V)
    assert len(set(V))==N==n*math.comb(n-k,k)//(n-k)
    assert all(a.bit_count()==k and a>>n==0 and not(a&(a<<1)) and not(a&1 and a>>(n-1)&1) for a in V)
    for i,a in enumerate(V):
        assert adj[i]==sum(1<<j for j,b in enumerate(V) if not(a&b))
    covered=set();diam=0
    for s,levels in d.get('representative_levels',[[d['source'],d['levels']]]):
        assert levels[0]==1<<s
        seen=0
        for f in levels:
            assert not(seen&f);seen|=f
        assert seen==(1<<N)-1
        seen=levels[0]
        for i in range(1,len(levels)):
            expected=0;f=levels[i-1]
            while f:
                b=f&-f;f-=b;expected|=adj[b.bit_length()-1]
            assert levels[i]==expected&~seen;seen|=levels[i]
        diam=max(diam,len(levels)-1)
        a=V[s]
        covered.update(((a<<t)|(a>>(n-t)))&((1<<n)-1) for t in range(n))
    row=dict(n=n,k=k,vertices=N,diameter=diam,all_orbits_covered=covered==set(V))
    if n==14:
        s,t=d['witness'];balls=[]
        for j in [s,t]:
            ball=(1<<j)|adj[j];f=adj[j]
            while f:
                b=f&-f;f-=b;ball|=adj[b.bit_length()-1]
            balls.append(ball)
        assert balls[0]&balls[1]==0
        row['radius_two_balls']=[[[x+1 for x in range(n) if a>>x&1] for i,a in enumerate(V) if ball>>i&1] for ball in balls]
    summary.append(row);print(json.dumps(row),flush=True)
Path('outputs/certificate-checks.json').write_text(json.dumps(summary,indent=2))
