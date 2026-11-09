# 351804: search strong digraphs G* on m vertices; compare rho(A_11) with E pendant out-vertices at v_j
# vs at every max-outdegree vertex. Pure python; Perron root by power iteration with Collatz-Wielandt brackets.
import sys
m=int(sys.argv[1]); Emax=int(sys.argv[2]); lo_mask=int(sys.argv[3]) if len(sys.argv)>3 else 1; hi_mask=int(sys.argv[4]) if len(sys.argv)>4 else None
alphas=[i/20 for i in range(1,20)]
pairs=[(i,j) for i in range(m) for j in range(m) if i!=j]
if hi_mask is None: hi_mask=1<<len(pairs)
def strong(adj):
    for s in range(m):
        seen={s}; st=[s]
        while st:
            u=st.pop()
            for v in adj[u]:
                if v not in seen: seen.add(v); st.append(v)
        if len(seen)<m: return False
    return True
def perron(M):
    x=[1.0]*m
    for it in range(3000):
        y=[sum(M[i][j]*x[j] for j in range(m)) for i in range(m)]
        lo=min(y[i]/x[i] for i in range(m)); hi=max(y[i]/x[i] for i in range(m))
        s=max(y); x=[v/s for v in y]
        if hi-lo<1e-12: break
    return lo,hi
best=[]; seen=0
for mask in range(lo_mask,hi_mask):
    adj=[[] for _ in range(m)]
    for b,(i,j) in enumerate(pairs):
        if mask>>b&1: adj[i].append(j)
    if not strong(adj): continue
    d=[len(a) for a in adj]; seen+=1
    D=max(d); mx=[i for i in range(m) if d[i]==D]
    if len(mx)==m: continue
    for E in range(1,Emax+1):
        for a in alphas:
            def rho(j):
                M=[[(1-a)*(1 if k in adj[i] else 0)+(a*(d[i]+(E if i==j else 0)) if i==k else 0) for k in range(m)] for i in range(m)]
                return perron(M)
            r1=max(rho(j)[1] for j in mx)
            for j in range(m):
                if j in mx: continue
                r=rho(j)[0]
                if r>r1+1e-9: best.append((round(r-r1,6),mask,E,a,j,tuple(d)))
best.sort(reverse=True)
print('m',m,'masks',lo_mask,hi_mask,'strong digraphs',seen,'violations',len(best))
for x in best[:15]: print(x)
