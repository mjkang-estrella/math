"""Independent exact finite diagnostics. No trajectory or entropy computation."""
from fractions import Fraction as F
from itertools import product
import json
checks=0
def check(x):
 global checks
 assert x
 checks+=1

def inverse(A):
 n=len(A);B=[[F(x) for x in row]+[F(i==j) for j in range(n)] for i,row in enumerate(A)]
 for i in range(n):
  k=next(k for k in range(i,n) if B[k][i]);B[i],B[k]=B[k],B[i];z=B[i][i];B[i]=[x/z for x in B[i]]
  for k in range(n):
   if k!=i:z=B[k][i];B[k]=[x-z*y for x,y in zip(B[k],B[i])]
 return [row[n:] for row in B]

def det_jet(diag,der):
 # independent continuant determinant and first derivative (off-diagonals -1)
 a,da,b,db=F(1),F(0),F(1),F(0)
 for i,(v,w) in enumerate(zip(diag,der)):
  if i==0:a,da,b,db=F(1),F(0),v,w
  else:a,da,b,db=b,db,v*b-a,w*b+v*db-da
 return b,db

def run():
 # First-crossing schedules satisfy doubling and nevertheless have unbounded d/u.
 # They are scalar countermodels to a claim using ONLY doubling; SC excludes them.
 schedules=[]
 for t in range(1,19):
  n0=2**(8*t);u=F(1,2**(4*t));e0=u-F(1,n0);d=F(1,2**(2*t));theta=F(1,2**(3*t))
  check(theta*theta==d*u);check(e0<theta<d);check(u/theta==theta/d==F(1,2**t))
  e=lambda j:min(d,e0*2**j)
  j=next(j for j in range(1,100) if e(j)>theta);N=n0*2**j;eps=e(j)
  check(e(j-1)<=theta<eps<=2*theta);check(eps*n0>theta*n0);check(theta*n0==2**(5*t))
  for m in range(7):
   check(e(m)<=2**m*u);check(e(j+m)<=2**m*eps);check(e(j+m)>=eps)
  schedules.append({'t':t,'d_over_u':str(d/u),'u_over_theta':str(u/theta),'crossing_index':j,'epsilon_over_theta':str(eps/theta),'theta_n0':str(theta*n0)})
 # Exact seed exponent bookkeeping, including a family, not a single chosen balance.
 check(F(1,4)+F(1,8)-1==F(-5,8));check(-2*F(1,8)==F(-1,4));check(1-3*F(4,5)==F(-7,5))
 seed_pairs=[]
 for a in [F(1,8),F(1,4),F(1,3),F(1,2)]:
  for b in [F(1,16),F(1,8),F(1,4)]:
   check(a>0 and b>0 and a+b<1);seed_pairs.append([str(a),str(b),str(a+b-1),str(-2*b)])
 # Varied Green curvature: cofactor derivative vs inverse row contraction, mixed signs.
 green_cases=0
 for n in range(1,9):
  for pattern in range(6):
   diag=[F(((-1)**(i+pattern) if pattern%2 else 1)*(8+((i+pattern)%7))) for i in range(n)]
   w=[F((i+1)*(pattern+2)*((-1)**i),3) for i in range(n)]
   D=[[diag[i] if i==j else F(-1) if abs(i-j)==1 else F(0) for j in range(n)] for i in range(n)]
   G=inverse(D);U=[row[0] for row in G]
   for i in range(n):
    check(sum(D[i][j]*U[j] for j in range(n))==int(i==0));check(G[0][i]==U[i])
   dprime=[w[i]*U[i] for i in range(n)]
   den,den1=det_jet(diag,dprime);num,num1=det_jet(diag[1:],dprime[1:])
   check(num/den==U[0]);cofactor_der=(num1*den-num*den1)/(den*den)
   check(cofactor_der==-sum(w[i]*U[i]**3 for i in range(n)))
   # Solving the differentiated boundary equation separately must agree.
   W=[-sum(G[i][j]*w[j]*U[j]**2 for j in range(n)) for i in range(n)]
   check(W[0]==cofactor_der)
   for i in range(n):check(sum(D[i][j]*W[j] for j in range(n))==-w[i]*U[i]**2)
   green_cases+=1
 # Negative control: if a critical diagonal makes the Dirichlet matrix singular, don't invert.
 try: inverse([[0]])
 except StopIteration: singular_rejected=True
 else: singular_rejected=False
 check(singular_rejected)
 # Source shortfall count tested with exact rational vector-log increment paths.
 count_cases=0
 for n in range(1,7):
  for increments in product([F(-1),F(0),F(1,2),F(1)],repeat=n):
   z=[F(0)]
   for x in increments:z.append(z[-1]+x)
   for c in [F(1,2),F(49,50)]:
    bad=sum(any(z[j]-z[i]<c*(j-i) for i in range(j)) for j in range(1,n+1))
    check(bad*(1-c)<=4*(n-z[-1]));count_cases+=1
 # Self-feedback cannot close H, even on exactly rational loss/mass models.
 feedback=[]
 for ell in [100,1000,10000]:
  B=F(ell,1000);d=B/ell;alpha=200*d
  check(alpha<=1);check(B<=F(1)+2*alpha*ell)
  feedback.append({'ell':ell,'unbounded_model_B':str(B),'alpha':str(alpha)})
 return {'status':'PASS','scope':'exact finite algebra and synthetic scalar countermodels, not a proof of SC, G, or entropy','assertions':checks,'green_cases':green_cases,'shortfall_count_cases':count_cases,'singular_negative_control_rejected':singular_rejected,'crossing_schedules':schedules,'seed_exponent_pairs':seed_pairs,'feedback_countermodels':feedback,'floating_trajectories':0}
if __name__=='__main__':print(json.dumps(run(),indent=2,sort_keys=True))
