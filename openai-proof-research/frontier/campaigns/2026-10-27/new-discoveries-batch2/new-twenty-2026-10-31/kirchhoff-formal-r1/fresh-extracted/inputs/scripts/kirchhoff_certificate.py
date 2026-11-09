import pathlib,sympy as s,json,itertools,hashlib
D=pathlib.Path(__file__).resolve().parents[1];n=11;k=6;E=list(itertools.combinations(range(k),2))+[(0,k)]+[(v,v+1)for v in range(k,n-1)];A=s.zeros(n)
for u,v in E:A[u,v]=A[v,u]=1
d=[sum(A[i,j]for j in range(n))for i in range(n)];rec=dict(n=n,clique=k,edges=E,degrees=list(map(int,d)),variants={});X=s.symbols('X')
def mat(M):return [[str(M[i,j])for j in range(n)]for i in range(n)]
for a in [1,0,-1]:
 K=s.diag(*[s.Integer(x)**a for x in d]);c=[sum((s.Rational(d[i],d[j])**a)*A[i,j]for j in range(n))for i in range(n)];L=s.diag(*c)-K*A*K.inv();z=s.ones(n,1);w=s.Matrix([s.Integer(x)**(-2*a)for x in d]);P=z*w.T/(w.T*z)[0];G=(L+P).inv()-P;cp=L.charpoly(X).as_expr().expand();coeff=[cp.coeff(X,i)for i in range(n+1)];R=-n*coeff[2]/coeff[1];assert n*s.trace(G)==R
 assert L*G==s.eye(n)-P and G*L==s.eye(n)-P and G*z==s.zeros(n,1)
 assert (K.inv()*L*K).T==K.inv()*L*K
 mp=(s.eye(n)-z*z.T/n)*(L+P).inv()*(s.eye(n)-w*w.T/(w.T*w)[0]);mpR=sum(mp[i,i]+mp[j,j]-mp[i,j]-mp[j,i]for i in range(n)for j in range(i+1,n))
 rec['variants'][str(a)]=dict(L=mat(L),P=mat(P),group_inverse=mat(G),charpoly=str(cp.factor()),charpoly_coeffs=list(map(str,coeff)),spectral_index=str(R),MP_index=str(mpR))
a=s.Rational(rec['variants']['1']['spectral_index']);b=s.Rational(rec['variants']['0']['spectral_index']);rec['strict_difference_R0_minus_R1']=str(b-a);assert b>a
(D/'outputs/kirchhoff-certificate.json').write_text(json.dumps(rec,indent=2));print({a:v['spectral_index']for a,v in rec['variants'].items()},'gap',b-a)
