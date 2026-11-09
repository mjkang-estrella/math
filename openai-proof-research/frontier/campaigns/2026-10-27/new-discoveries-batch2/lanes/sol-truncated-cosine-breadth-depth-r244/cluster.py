from pathlib import Path
import mpmath as m,json,itertools
m.mp.dps=65
P=Path(__file__).resolve().parent
def g(M,d):
 d=abs(d)
 if d>=m.pi:return m.mpf(0)
 s=0j
 for a in range(M+1):
  for b in range(M-1):
   k=2*M-2-2*a-2*b
   I=(m.pi-d) if k==0 else (m.exp(1j*k*(m.pi/2-d))-m.exp(-1j*k*m.pi/2))/(1j*k)
   s+=m.binomial(M,a)*m.binomial(M-2,b)*m.exp(1j*(M-2*a)*d)*I
 return m.re(s)/2**(2*M-2)
def basis(nodes,eps):
 # Exact divided difference coefficients, scaled so limit is h^(k)/k!.
 n=len(nodes);B=m.zeros(n)
 for k in range(n):
  for j in range(k+1):
   B[j,k]=1/(eps**k*m.fprod(nodes[j]-nodes[l] for l in range(k+1) if l!=j))
 return B
out=[]
for M in [3,4,5,6]:
 # Nonuniform rational offsets; monotone increments make all M-step gaps >=pi.
 for pattern in [0,1,2]:
  A=[m.mpf(i*i+i)/2 for i in range(M)]
  D=[m.mpf(0) if pattern==0 else m.mpf(i+1 if pattern==1 else (i==M-1)*M) for i in range(M)]
  for den in [100,1000,10000]:
   eps=m.pi/den
   C=[[A[i]+j*D[i] for i in range(M)] for j in range(3)]
   X=[j*m.pi+eps*C[j][i] for j in range(3) for i in range(M)]
   assert all(X[i]<X[i+1] for i in range(len(X)-1))
   assert all(X[i+M]-X[i]>=m.pi-m.mpf('1e-60') for i in range(len(X)-M))
   K=m.matrix([[g(M,x-y) for y in X] for x in X]);B=m.zeros(3*M)
   for j in range(3):
    b=basis(C[j],eps)
    for u in range(M):
     for v in range(M):B[j*M+u,j*M+v]=b[u,v]
   T=B.T*K*B;E=m.eigsy(T,eigvals_only=True)
   out.append({'M':M,'pattern':pattern,'eps_over_pi':'1/'+str(den),'min_transformed_eigenvalue':str(E[0]),'certificate':False})
(P/'cluster-results.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
