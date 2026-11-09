# compare Coulson-integral energy with Jacobi eigenvalues on sun, double sun, paths, random trees
import sys,math,random,importlib.util
spec=importlib.util.spec_from_file_location('rt',sys.argv[1])
sys.argv=['rt','1','coulson',sys.argv[2],sys.argv[3]]
rt=importlib.util.module_from_spec(spec)
src=open(spec.origin).read().split('t0=time.time()')[0]
exec(compile(src,'rt','exec'),rt.__dict__)
def jacobi_energy(adj):
    n=len(adj); d=[len(a) for a in adj]
    A=[[0.0]*n for _ in range(n)]
    for v in range(n):
        for u in adj[v]: A[v][u]=1/math.sqrt(d[u]*d[v])
    for sweep in range(100):
        off=sum(A[i][j]**2 for i in range(n) for j in range(n) if i!=j)
        if off<1e-26: break
        for p in range(n):
            for q in range(p+1,n):
                if abs(A[p][q])<1e-300: continue
                th=(A[q][q]-A[p][p])/(2*A[p][q]); t=(1 if th>=0 else -1)/(abs(th)+math.sqrt(th*th+1)); c=1/math.sqrt(t*t+1); s=t*c
                for k in range(n):
                    akp=A[k][p]; akq=A[k][q]; A[k][p]=c*akp-s*akq; A[k][q]=s*akp+c*akq
                for k in range(n):
                    apk=A[p][k]; aqk=A[q][k]; A[p][k]=c*apk-s*aqk; A[q][k]=s*apk+c*aqk
    return sum(abs(A[i][i]) for i in range(n))
tests=[('sun7',rt.sun(7)),('sun8',rt.sun(8)),('dsun(3,3)',rt.double_sun(3,3)),('dsun(4,3)',rt.double_sun(4,3))]
rng=random.Random(5)
for n in [12,15,17]:
    adj=[[] for _ in range(n)]
    for v in range(1,n):
        u=rng.randrange(v); adj[u].append(v); adj[v].append(u)
    tests.append((f'rand{n}',adj))
for name,adj in tests:
    rt.METHOD='coulson'; ec=rt.randic_energy(adj); ej=jacobi_energy(adj)
    print(name,len(adj),'coulson',repr(ec),'jacobi',repr(ej),'diff',ec-ej)
