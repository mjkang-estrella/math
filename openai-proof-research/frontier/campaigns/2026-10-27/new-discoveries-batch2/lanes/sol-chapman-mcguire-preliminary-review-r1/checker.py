from pathlib import Path
import json
L=Path(__file__).resolve().parent
def norm(a):
 a=[v%3 for v in a]
 while len(a)>1 and a[-1]==0:a.pop()
 return a or [0]
def add(a,b):return norm([(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))])
def neg(a):return norm([-v for v in a])
def sub(a,b):return add(a,neg(b))
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,u in enumerate(a):
  for j,v in enumerate(b):c[i+j]+=u*v
 return norm(c)
def div(a,b):
 a=norm(a);b=norm(b);assert b!=[0];q=[0]*max(1,len(a)-len(b)+1)
 while a!=[0] and len(a)>=len(b):
  k=len(a)-len(b);v=a[-1]*pow(b[-1],-1,3)%3;q[k]=v;a=sub(a,[0]*k+[v*t for t in b])
 return norm(q),a
def rem(a,b):return div(a,b)[1]
def gcd(a,b):
 while b!=[0]:a,b=b,rem(a,b)
 return norm([v*pow(a[-1],-1,3) for v in a])
def power(a,n,m=None):
 r=[1]
 while n:
  if n%2:r=mul(r,a);r=rem(r,m) if m else r
  a=mul(a,a);a=rem(a,m) if m else a;n//=2
 return r
z=[0,1];one=[1];g=norm([-1,-1,-1,0,-1,0,1,1]);H=norm([-1,0,-1,1,-1,1,1,1]);T=[1]*4
tests={};evidence={}
def check(name,b):tests[name]=bool(b);assert b,name
for name,f in [('g',g),('H',H)]:
 r=z;seq=[]
 for i in range(7):r=power(r,3,f);seq.append(r)
 check(name+'_frobenius7',r==z)
 check(name+'_no_linear_factor',gcd(f,sub(power(z,3),z))==one)
 evidence[name+'_frobenius_sequence']=seq
check('direct_integer_factor_mod3',mul(g,norm([-1,0,1,-1,1]))==norm([1,1]+[0]*9+[1]))
P=sub(power(T,4),z);phi=[1]*5
check('alpha_factorization',P==mul(mul(sub(z,one),phi),H))
for k in [1,4,5]:
 d=gcd(H,sub(power(z,k),one));evidence['gcd_H_A'+str(k)+'minus1']=d;check('H_coprime_'+str(k),d==one)
check('H_nonzero_constant',H[0]!=0)
elim=sub(sub(sub(sub(sub(power(z,14),power(z,12)),power(z,10)),power(z,8)),power(z,2)),one)
check('elimination_divisible_g',rem(elim,g)==[0])
x=z;alpha=power(x,8,g)
def M(a,b):return rem(mul(a,b),g)
def W(a,n):return power(a,n,g)
def D(a,b):assert b!=[0];return M(a,W(b,3**7-2))
R=add(x,W(x,11));U=sub(one,W(alpha,4));V=sub(one,alpha)
check('R_minus1',R==[2]);check('alpha_nonzero_nonone',alpha not in [[0],one]);check('U_V_nonzero',U!=[0] and V!=[0])
check('alpha5_not1',W(alpha,5)!=one)
check('Eq5',M(x,U)==M(W(x,3),V));check('Eq6',W(x,2)==D(U,V));check('Eq7',M(W(x,3),sub(one,W(alpha,12)))==M(M(alpha,x),sub(one,W(alpha,3))))
check('Eq8',W(x,2)==D(M(alpha,sub(one,W(alpha,3))),sub(one,W(alpha,12))))
B=sub(one,W(alpha,12))
V3=sub(one,W(alpha,3));V9=sub(one,W(alpha,9))
check('Eq9',W(B,4)==M(W(alpha,3),W(V3,4)))
check('Eq10',W(B,12)==M(W(alpha,9),W(V3,12)))
check('Eq11',D(B,W(B,9))==M(W(alpha,(3**7-1)-6),D(sub(one,W(alpha,3)),W(sub(one,W(alpha,3)),9))))
lhs=D(U,W(U,9));rhs=M(W(alpha,3**7-3),D(V,W(V,9)))
check('Eq12',lhs==rhs);check('Eq13',W(alpha,(3**14-1)//8)==one);check('x_in_3pow14',W(x,3**14)==x)
def ev(f,a):
 r=[0]
 for c in reversed(f):r=add(M(r,a),[c])
 return r
check('alpha_H_evaluation',ev(H,alpha)==[0]);check('Talpha_x2',ev(T,alpha)==W(x,2))
check('alpha_printed_residue',alpha==norm([-1,0,0,1,-1,1,1]))
check('alpha5_printed_residue',W(alpha,5)==norm([-1,1,-1,-1,-1,1,-1]))
evidence.update(alpha=alpha,alpha5=W(alpha,5),R=R,Eq12_lhs=lhs,Eq12_rhs=rhs,U=U,V=V,tests=tests,all_pass=all(tests.values()),implementation='fresh standalone coefficient-list arithmetic modulo 3; no scout/root code imported')
(L/'checker-evidence.json').write_text(json.dumps(evidence,indent=2)+'\n');print(json.dumps({'all_pass':True,'checks':len(tests)}))
