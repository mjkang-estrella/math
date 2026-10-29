from pathlib import Path
L=Path(__file__).resolve().parent
s=(L/'scan.py').read_text().replace('records=[];fails=[];count=0','records=[];fails=[];count=0; eigen=0; row=0; shifted=0; coeff_fail=[]')
s=s.replace('    C=[]','''    if exact:
     from math import prod
     def ev(z):return sum(c*prod(v**k for v,k in zip(z,e)) for e,c in p.items())
     z=[F(j+1) for j in range(n)]
     Dz=F(0)
     for j in range(n):
      zz=z[:];zz[j]*=q
      Dz+=prod((t*z[j]-z[k])/(z[j]-z[k]) for k in range(n) if k!=j)*ev(zz)
     assert Dz==sum(q**l[j]*t**(n-j-1) for j in range(n))*ev(z)
     eigen+=1
    C=[]''')
s=s.replace('    def val(a,x):', '''    if exact:
     def mul(a,b):
      c=[F(0)]*(len(a)+len(b)-1)
      for k,u in enumerate(a):
       for j,v in enumerate(b):c[k+j]+=u*v
      return c
     def add(a,b):return [(a[k] if k<len(a) else 0)+(b[k] if k<len(b) else 0) for k in range(max(len(a),len(b)))]
     def der(a):return [k*a[k] for k in range(1,len(a))]
     for i in range(1,n):
      aa,bb,cc=C[i-1:i+2]
      left=mul(mul(der(bb),aa),cc);right=mul(bb,add(mul(der(aa),cc),mul(aa,der(cc))))
      N=add([2*u for u in left],[-u for u in right]);W=[sum(N[k]*comb(k,j) for k in range(j,len(N))) for j in range(len(N))]
      shifted+=1
      if any(w<0 for w in W):coeff_fail.append({'q':str(q),'t':str(t),'lambda':l,'n':n,'i':i})
     if l[1:]==(0,)*(n-1):
      def poch(a,m):return prod(1-a*q**r for r in range(m))
      # P=Q/b_lambda, b_lambda=(t;q)_d/(q;q)_d
      norm=poch(t,d)/poch(q,d)
      for i in range(n+1):
       expected=[poch(t**i,k)*poch(t**(n-i),d-k)*t**(i*(d-k))/(poch(q,k)*poch(q,d-k))/norm for k in range(d+1)]
       assert C[i]==expected
       row+=1
    def val(a,x):''')
s=s.replace("'finite_only':True", "'finite_only':True,'eigen_checks':eigen,'one_row_arrays':row,'shifted_N_checks':shifted,'shifted_N_failures':coeff_fail")
s=s.replace("'exact-scan.json' if exact else 'float-scan.json'", "'audit.json' if exact else 'audit-float.json'")
(L/'audit.py').write_text(s)
