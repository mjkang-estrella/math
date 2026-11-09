import sys,itertools,time
sys.path.insert(0,sys.argv[0].rsplit('/',1)[0])
from qm import qm_nsd
def circ(n,S):
    return [sorted({(i+s)%n for s in S}|{(i-s)%n for s in S}) for i in range(n)]
def lex(A,B):  # A[B]
    nb=len(B); adj=[]
    for a in range(len(A)):
        for b in range(nb):
            adj.append(sorted([a*nb+y for y in B[b]]+[x*nb+y for x in A[a] for y in range(nb)]))
    return adj
def strong(A,B):
    nb=len(B); adj=[]
    for a in range(len(A)):
        for b in range(nb):
            nbrs=set()
            for x in A[a]+[a]:
                for y in B[b]+[b]:
                    if (x,y)!=(a,b) and (x==a and y in B[b] or y==b and x in A[a] or x in A[a] and y in B[b]): nbrs.add(x*nb+y)
            adj.append(sorted(nbrs))
    return adj
def cart(A,B):
    nb=len(B); return [sorted([a*nb+y for y in B[b]]+[x*nb+b for x in A[a]]) for a in range(len(A)) for b in range(nb)]
K=lambda m:[[j for j in range(m) if j!=i] for i in range(m)]
C=lambda n:circ(n,[1])
t=time.time(); res=[]
tests=[]
for n in range(5,17):
    for r in range(2,min(n//2,4)+1):
        for S in itertools.combinations(range(1,n//2+1),r):
            tests.append(('Circ%d%s'%(n,S),circ(n,list(S))))
for m in (2,3): tests+= [('C5[K%d]'%m,lex(C(5),K(m))),('C5strongK%d'%m,strong(C(5),K(m))),('C5xK%d'%m,cart(C(5),K(m)))]
tests+= [('C5xC5',cart(C(5),C(5))),('C5strongC5',strong(C(5),C(5))),('C5[K2bar]',lex(C(5),[[],[]])),('C5[K3bar]',lex(C(5),[[],[],[]])),('C7[K2bar]',lex(C(7),[[],[]]))]
for name,adj in tests:
    if any(len(a)==0 for a in adj): continue
    ok=qm_nsd(adj,4)
    if not ok: print('NO4',name,flush=True)
    res.append(ok)
    if time.time()-t>110: print('time cap at',name);break
print('tested',len(res),'all4',all(res),round(time.time()-t,1))
