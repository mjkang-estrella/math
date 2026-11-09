import sys
exec(open(sys.argv[1]).read().split('best=[]')[0].replace('m=int(sys.argv[1]); Emax=int(sys.argv[2]); lo_mask=int(sys.argv[3]) if len(sys.argv)>3 else 1; hi_mask=int(sys.argv[4]) if len(sys.argv)>4 else None','m=4;Emax=1;lo_mask=1;hi_mask=None'))
# E=1 only: find violations, minimal arc count
res=[]
for mask in range(1,1<<len(pairs)):
    adj=[[] for _ in range(m)]
    for b,(i,j) in enumerate(pairs):
        if mask>>b&1: adj[i].append(j)
    if not strong(adj): continue
    d=[len(a) for a in adj]; D=max(d); mx=[i for i in range(m) if d[i]==D]
    if len(mx)==m: continue
    viol=[]
    for a in [i/40 for i in range(1,40)]:
        def rho(j):
            M=[[(1-a)*(1 if k in adj[i] else 0)+(a*(d[i]+(1 if i==j else 0)) if i==k else 0) for k in range(m)] for i in range(m)]
            return perron(M)
        r1=max(rho(j)[1] for j in mx)
        for j in range(m):
            if j not in mx and rho(j)[0]>r1+1e-9: viol.append((a,j,round(rho(j)[0]-r1,5)))
    if viol: res.append((sum(d),mask,[tuple(x) for x in adj],d,viol))
res.sort()
print('E=1 violating G*:',len(res))
for r in res[:6]: print(r[0],r[1],r[2],r[3],'alphas',r[4][0],'...',r[4][-1],len(r[4]))
