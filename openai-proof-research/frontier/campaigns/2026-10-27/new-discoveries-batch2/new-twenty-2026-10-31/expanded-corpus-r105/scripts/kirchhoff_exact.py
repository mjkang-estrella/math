import sympy as s,pathlib,json,itertools
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for n,k in [(n,k)for n in range(9,13)for k in range(3,n)]:
 E=list(itertools.combinations(range(k),2))+[(0,k)]+[(v,v+1)for v in range(k,n-1)];A=s.zeros(n)
 for u,v in E:A[u,v]=A[v,u]=1
 d=[sum(A[i,j]for j in range(n))for i in range(n)];vals=[];mps=[]
 for a in [1,0,-1]:
  c=[sum((s.Rational(d[i],d[j])**a)*A[i,j]for j in range(n))for i in range(n)];L=s.diag(*c)-s.diag(*[s.Integer(x)**a for x in d])*A*s.diag(*[s.Integer(x)**(-a)for x in d]);z=s.ones(n,1);w=s.Matrix([s.Integer(x)**(-2*a)for x in d]);P=z*w.T/(w.T*z)[0];grp=(L+P).inv()-P;spec=n*s.trace(grp)
  # unique MP inverse via rank-one repair; right null z, left null w.
  Rp=z*z.T/n;Lp=w*w.T/(w.T*w)[0];mp=(s.eye(n)-Rp)*(L+P).inv()*(s.eye(n)-Lp)
  assert L*mp*L==L and mp*L*mp==mp and (L*mp).T==L*mp and (mp*L).T==mp*L
  index=sum(mp[i,i]+mp[j,j]-mp[i,j]-mp[j,i]for i in range(n)for j in range(i+1,n));vals.append(str(spec));mps.append(str(index))
 z=dict(n=n,clique=k,edges=E,spectral_indices=vals,MP_indices=mps)
 if s.Rational(vals[0])<s.Rational(vals[1]) or s.Rational(vals[1])<s.Rational(vals[2]) or s.Rational(mps[0])<s.Rational(mps[1]) or s.Rational(mps[1])<s.Rational(mps[2]):out.append(z);print(z,flush=True)
 (D/'outputs/kirchhoff-exact.json').write_text(json.dumps(out,indent=2))
