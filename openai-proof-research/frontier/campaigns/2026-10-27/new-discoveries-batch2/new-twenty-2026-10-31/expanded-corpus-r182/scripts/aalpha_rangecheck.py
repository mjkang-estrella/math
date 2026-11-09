# Consistency check for 351804: no violation should occur for alpha >= d1/(d1+E) (source Thm 2.9 range,
# pendants hung at a single non-max vertex: n1 = 1, n-m-n1+1 = E). m=4, E in 1..3, alpha grid 1/40.
import sys
src=open('scripts/aalpha_search.py').read().split('best=[]')[0]
src=src.replace("m=int(sys.argv[1]); Emax=int(sys.argv[2]); lo_mask=int(sys.argv[3]) if len(sys.argv)>3 else 1; hi_mask=int(sys.argv[4]) if len(sys.argv)>4 else None","m=4;Emax=3;lo_mask=int(sys.argv[1]);hi_mask=int(sys.argv[2])")
exec(src)
inrange=0; outrange=0; maxalpha=0
for mask in range(lo_mask,hi_mask):
    adj=[[] for _ in range(m)]
    for b,(i,j) in enumerate(pairs):
        if mask>>b&1: adj[i].append(j)
    if not strong(adj): continue
    d=[len(a) for a in adj]; D=max(d); mx=[i for i in range(m) if d[i]==D]
    if len(mx)==m: continue
    for E in range(1,Emax+1):
        for a in [i/20 for i in range(1,20)]:
            def rho(j):
                M=[[(1-a)*(1 if k in adj[i] else 0)+(a*(d[i]+(E if i==j else 0)) if i==k else 0) for k in range(m)] for i in range(m)]
                return perron(M)
            r1=max(rho(j)[1] for j in mx)
            for j in range(m):
                if j in mx: continue
                if rho(j)[0]>r1+1e-9:
                    if a>=D/(D+E): inrange+=1
                    else: outrange+=1; maxalpha=max(maxalpha,a)
print('violations inside source-proved range:',inrange,' outside:',outrange,' max violating alpha:',maxalpha)
