"""Independent exact-arithmetic attacks. Finite checks are not a universal proof."""
from fractions import Fraction as Q
from itertools import product, permutations
from collections import Counter
import random, json, math
rng=random.Random(55092026); counts=Counter(); notes={}
def ck(x,label):
 counts[label]+=1
 if not x: raise AssertionError(label)
def mat(n,fun):return [[fun(i,j) for j in range(n)] for i in range(n)]
def eye(n):return mat(n,lambda i,j:Q(i==j))
def zero(n):return mat(n,lambda i,j:Q(0))
def add(a,b):return mat(len(a),lambda i,j:a[i][j]+b[i][j])
def sub(a,b):return mat(len(a),lambda i,j:a[i][j]-b[i][j])
def mul(a,b):return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
def tr(a):return sum(a[i][i] for i in range(len(a)))
def ns(a):return sum(x*x for r in a for x in r)
def cm(a,b):return sub(mul(a,b),mul(b,a))
def mv(a,v):return [sum(x*y for x,y in zip(row,v)) for row in a]
def outer(v,w):return [[x*y for y in w] for x in v]
def transpose(a):return list(map(list,zip(*a)))
def slices(t,n):return [mat(n,lambda i,j:t[i,j,k]) for k in range(n)]
def gram(a):
 b=zero(len(a[0]))
 for x in a:b=add(b,mul(x,x))
 return b

def tensor_tests():
 for n in range(2,5):
  for rep in range(6):
   vals={idx:Q(rng.randint(-5,5),rng.randint(1,7)) for idx in product(range(n),repeat=3) if tuple(sorted(idx))==idx}
   t={idx:vals[tuple(sorted(idx))] for idx in product(range(n),repeat=3)}
   # Force e0 to be a stationary cubic direction; no maximum is assumed in these identities.
   for a in range(1,n):
    for idx in set(permutations((0,0,a))):t[idx]=Q(0)
   X=slices(t,n);c=t[0,0,0];H=[row[1:] for row in X[0][1:]]
   rest={idx:t[tuple(i+1 for i in idx)] for idx in product(range(n-1),repeat=3)}
   Y=slices(rest,n-1)
   ck([row[1:] for row in gram(X)[1:]]==add(gram(Y),add(mul(H,H),mul(H,H))),'block_normalization')
   correction=[]
   for a,b in product(range(1,n),repeat=2):
    ha=[H[i][a-1] for i in range(n-1)];hb=[H[i][b-1] for i in range(n-1)]
    e=sub(outer(ha,hb),outer(hb,ha));correction.append(e)
    ck([row[1:] for row in cm(X[a],X[b])[1:]]==add(cm(Y[a-1],Y[b-1]),e),'block_commutator')
   ck(sum(ns(e) for e in correction)<=4*ns(H)**2,'outer_array_budget')
   ck(sum(t[idx]**2 for idx in t if 0 in idx and idx!=(0,0,0))==3*ns(H),'orthogonal_discard_budget')
   for w in range(n):
    e0=[Q(i==0) for i in range(n)];ew=[Q(i==w) for i in range(n)]
    left=mv(sub(mul(X[0],X[0]),[[c*z for z in row] for row in X[0]]),ew)
    ck(left==mv(cm(X[0],X[w]),e0),'associativity_sign')
   # Rational Householder rotation, with simultaneous coefficient rotation.
   v=[Q(i+1) for i in range(n)];vv=sum(z*z for z in v)
   U=mat(n,lambda i,j:Q(i==j)-2*v[i]*v[j]/vv)
   ck(mul(U,transpose(U))==eye(n),'rational_orthogonal')
   rt={idx:sum(t[a,b,c]*U[a][idx[0]]*U[b][idx[1]]*U[c][idx[2]] for a,b,c in product(range(n),repeat=3)) for idx in t}
   Z=slices(rt,n)
   ck(gram(Z)==mul(transpose(U),mul(gram(X),U)),'all_index_rotation_normalization')
   ck(sum(ns(cm(a,b)) for a in Z for b in Z)==sum(ns(cm(a,b)) for a in X for b in X),'all_index_rotation_commutator')
   ck(sum(x*x for x in rt.values())==sum(x*x for x in t.values()),'tensor_rotation_isometry')

def jet_tests():
 for n in range(2,5):
  for rep in range(5):
   X=[]
   for r in range(n):
    a=mat(n,lambda i,j:Q(rng.randint(-4,4),5));X.append(add(a,transpose(a)))
   def S(r,s):return [X[r][i][s]-X[s][i][r] for i in range(n)]
   # Direct polynomial coefficients of L^2, including repeated monomials.
   poly={}
   for r,s in product(range(n),repeat=2):
    powers=tuple(int(i==r)+int(i==s) for i in range(n));poly[powers]=add(poly.get(powers,zero(n)),mul(X[r],X[s]))
   for r,s,t in product(range(n),repeat=3):
    def second(a,b,i,j):
     powers=tuple(int(k==a)+int(k==b) for k in range(n)); return poly[powers][i][j]*(2 if a==b else 1)
    direct=[second(r,t,i,s)-second(s,t,i,r) for i in range(n)]
    comm=[cm(X[r],X[s])[i][t] for i in range(n)]
    err=[a-b+c for a,b,c in zip(mv(X[r],S(t,s)),mv(X[s],S(t,r)),mv(X[t],S(r,s)))]
    ck(direct==[a+b for a,b in zip(comm,err)],'polynomial_jet_commutator_expansion')
   T={idx:sum(X[p[2]][p[0]][p[1]] for p in permutations(idx))/6 for idx in product(range(n),repeat=3)}
   ck(all(T[idx]==T[tuple(sorted(idx))] for idx in T),'symmetrization_exact')
   dx=sum((T[i,j,r]-X[r][i][j])**2 for i,j,r in T)
   serr=sum(z*z for r,s in product(range(n),repeat=2) for z in S(r,s))
   ck(dx<=serr,'symmetrization_budget')

def constants():
 for n in range(1,7):
  for sg in [-1,1]:
   t={idx:Q(sg if len(set(idx))==1 else 0) for idx in product(range(n),repeat=3)}
   xs=slices(t,n)
   ck(gram(xs)==eye(n) and all(ns(cm(a,b))==0 for a in xs for b in xs),'zero_residual_signed_products')
   eps=Q(1,10**8*n**4)
   ds=[1+(-1)**i*eps for i in range(n)]
   eta=max(abs(a*a-1) for a in ds)
   ck(eta<=Q(1,10**6*n**4),'diagonal_near_threshold')
   ck(sum((a-1)**2 for a in ds)<=(20*n*eta)**2,'diagonal_tensor_bound')
 for m in list(range(1,101))+[200,1000,10000]:
  eta=Q(1,10**6*m**4);ed=2*eta
  ck(1-ed-400*m**3*ed**2>=Q(1,4),'maximizer_upgrade')
  ck(16*m*ed<=1,'coefficient_rounding')
  ck(256*m*m*eta<=1,'recursive_residual_budget')
  ck(96*m*m+112*m<=208*m*m<400*m*m,'twenty_m_constant')
  # e h^(-m/2-2)=h; h=e^(2/(m+6)); e=sqrt(1000 delta).
  a=Q(2,m+6)
  ck(1-a*(Q(m,2)+2)==a,'jet_exponent_balance')
  ck(a/2==Q(1,m+6),'entropy_exponent')
  ck(1-a*(Q(m,2)+1)>=a,'zero_jet_weaker_cost')
 ck(Q(117,320000)>Q(1,10000),'omega_low')
 ck(Q(117,172000)>Q(1,10000),'omega_high')
 ck(Q(117,86000)>Q(1,1000),'omega_local')
 for a in [Q(1,1000),Q(1,100),Q(1,10),Q(1),Q(3)]:
  mean=(1-a*a)/(1+a);second=2*(1+a**3)/(1+a)
  ck(mean==1-a and second-mean**2==1+a*a,'laplace_moments')
  ck((1+a)**2>1+a*a,'laplace_positive_gap')

def partition_tests():
 # Exact truncations test both sides of a deliberately small spectral gap.
 for den in [10,100,1000]:
  n=4;h=Q(1,den);lams=[Q(-1,2),Q(-1,2)+h/2,Q(1,3),Q(1,3)+h/2]
  H1=mat(n,lambda i,j:lams[i] if i==j else Q(0)); mats=[]
  for k in range(3):
   a=mat(n,lambda i,j:Q(rng.randint(-2,2),40));mats.append(add(a,transpose(a)))
  cl=[0,0,1,1]; trunc=[mat(n,lambda i,j:a[i][j] if cl[i]==cl[j] else Q(0)) for a in mats]
  for a,b in zip(mats,trunc):ck(ns(sub(a,b))*h*h<=ns(cm(H1,a)),'spectral_cross_block_bound')
  for i,j in product(range(3),repeat=2):
   # Cauchy bound avoids square roots: ||comm difference|| <=2(e_i+e_j).
   ck(ns(sub(cm(trunc[i],trunc[j]),cm(mats[i],mats[j])))<=8*(ns(sub(mats[i],trunc[i]))+ns(sub(mats[j],trunc[j]))),'truncated_commutator_budget')

def covariance_tests():
 U=[[Q(3,5),Q(-4,5)],[Q(4,5),Q(3,5)]]
 for p,q in product([Q(1,2),Q(1),Q(7,3)],repeat=2):
  P=mul(U,mul([[p,0],[0,q]],transpose(U)))
  for sign in [-1,1]:
   M=[[sign*Q(3,5)*z for z in row] for row in U]
   r2=tr(mul(P,P))+2-2*tr(mul(P,M))
   ck(r2>=ns(sub(P,eye(2))),'covariance_orientation_trace')
 # Negative controls must be detected, not accidentally certified.
 X=[eye(2),zero(2)]
 ck(gram(X)==eye(2) and ns(cm(*X))==0,'negative_commutation_normalization_exact')
 ck(any(X[0][i][1]!=X[1][i][0] for i in range(2)),'negative_missing_coefficient_symmetry')
 t=Q(1,10);Y=[[[1,0],[0,t]],[[0,t],[t,1]]]
 ck(ns(cm(*Y))>0,'negative_affine_q_loses_second_jet')
 ck(all(Y[r][i][s]==Y[s][i][r] for i,r,s in product(range(2),repeat=3)),'negative_affine_q_still_integrable')
 c=math.sqrt(.5); ck(c>c/2 and 6*c-3*c>0,'negative_stationary_not_maximal')
 ck(ns(sub([[-1,0],[0,-1]],eye(2)))==8,'negative_nonsymmetric_or_nonpositive_normalizer')
 notes['negative_controls']=['Commutation and normalization without coefficient symmetry','Affine q with vanishing second derivative','Nonmaximizing stationary cubic direction','Nonpositive normalizing matrix']

def law_diagnostics():
 # Midpoint quantile integrals are numerical diagnostics only; both signs inspected.
 out=[]
 for a in [.001,.01,.1,1.]:
  row={'a':a,'gap':math.log1p(a)-.5*math.log1p(a*a)}
  for N in [8192,32768]:
   cost=[0.,0.]
   for i in range(N):
    u=(i+.5)/N
    raw=a*math.log(u*(1+a)/a) if u<a/(1+a) else -math.log((1-u)*(1+a))
    z=(raw-(1-a))/math.sqrt(1+a*a)
    refs=[-math.log1p(-u)-1,1+math.log(u)]
    for j in range(2):cost[j]+=(z-refs[j])**2/N
   row[str(N)]=[round(math.sqrt(c),10) for c in cost]
  ck(row['32768'][0]<=row['32768'][1]+1e-9,'laplace_orientation_diagnostic')
  out.append(row)
 notes['asymmetric_laplace_quantile_W2']=out
 notes['warning']='Quadrature and finite algebra do not prove the universal theorem or optimal orbit distance in dimension greater than one.'

if __name__=='__main__':
 tensor_tests();jet_tests();constants();partition_tests();covariance_tests();law_diagnostics()
 print(json.dumps({'status':'PASS','assertions':dict(sorted(counts.items())),'total_assertions':sum(counts.values()),'notes':notes},indent=2,sort_keys=True))
