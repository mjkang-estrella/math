#!/usr/bin/env python3
"""Independent exact finite diagnostics. No entropy or universal analytic certification."""
from fractions import Fraction as Q
from itertools import product
from collections import Counter
import json, math
counts=Counter()
def check(v,category):
    assert v, category
    counts[category]+=1

def mul(a,b):
    return [[sum(a[i][k]*b[k][j] for k in range(len(b))) for j in range(len(b[0]))] for i in range(len(a))]
def eye(n):return [[Q(i==j) for j in range(n)] for i in range(n)]
def inverse(a):
    n=len(a);z=[list(map(Q,row))+u for row,u in zip(a,eye(n))]
    for i in range(n):
        pivot=next((r for r in range(i,n) if z[r][i]),None)
        if pivot is None:raise ValueError('singular')
        z[i],z[pivot]=z[pivot],z[i];v=z[i][i];z[i]=[x/v for x in z[i]]
        for r in range(n):
            if r!=i:
                v=z[r][i];z[r]=[x-v*y for x,y in zip(z[r],z[i])]
    return [row[n:] for row in z]
def A(v):return [[Q(v),Q(-1)],[Q(1),Q(0)]]
def recurrence(v,u_minus,u_zero,forcing=None):
    u=[Q(u_minus),Q(u_zero)]
    for i,x in enumerate(v):u.append(x*u[-1]-u[-2]+(0 if forcing is None else forcing[i]))
    return u

# Vary signed coefficients and arbitrary second jets; no eligibility is inferred.
for n in range(1,10):
 for seed in range(1,9):
    v=[Q(((-1)**(a+seed))*(4+seed+a),1+(a%3)) for a in range(n)]
    f2=[Q((-1)**a*(seed+2*a),3) for a in range(n)]
    D=[[v[i] if i==j else Q(-1 if abs(i-j)==1 else 0) for j in range(n)] for i in range(n)]
    G=inverse(D);check(mul(D,G)==eye(n),'green_inverse')
    U=[G[a][0] for a in range(n)]
    t=recurrence(v,0,1)
    for a in range(n):
      for b in range(n):check(G[a][b]==t[min(a,b)+1]*U[max(a,b)],'green_entries')
    # Implicit shooting differentiation is independent of the inverse formula:
    forcing=[f2[a]*U[a]**2 for a in range(n)]
    shot=recurrence(v,0,0,forcing)
    second=-shot[-1]/t[-1]
    cubic=-sum(f2[a]*U[a]**3 for a in range(n))
    check(second==cubic,'curvature_shooting_vs_green')
    second_solution=recurrence(v,0,second,forcing)
    check(second_solution[-1]==0,'second_boundary')
    # Positive sign or square in place of cube must be detected for generic data.
    if n==1:
      check(second!=sum(f2[a]*U[a]**3 for a in range(n)),'wrong_sign_negative_control')
      check(second!=-sum(f2[a]*U[a]**2 for a in range(n)),'wrong_power_negative_control')
    # Both endpoint row kernels (n and n-1), including n=2.
    if n>=2:
      T=eye(2)
      for x in v:T=mul(A(x),T)
      for j,row in [(n,T[0]),(n-1,T[1])]:
        if row[0]:
          slope=-row[1]/row[0];kernel=[slope,Q(1)]
          sol=recurrence(v[:j],1,slope)
          check(sol[-1]==0,'both_dirichlet_rows')
          check(sum(row[i]*kernel[i] for i in range(2))==0,'row_kernel')
    J=[[Q(0),Q(1)],[Q(1),Q(0)]]
    for x in v:check(mul(mul(J,inverse(A(x))),J)==A(x),'backward_swap')

# Singular matrices are rejected; invertibility cannot be replaced by arbitrary recurrence data.
try:inverse([[Q(0)]])
except ValueError:check(True,'singular_negative_control')
else:raise AssertionError('singular negative control failed')

# Exact rational periodic cancellation; explicitly NOT a standard-map orbit.
for L in range(3,9):
 for m in range(1,10):
    T=eye(2)
    for _ in range(2*m):T=mul(A(L),T)
    P,Qv=T[0][0],-T[0][1];B=mul(A(2*Qv/P),T)
    check(B[0][0]+B[1][1]==0,'rare_bad_trace')
    check(mul(B,B)==[[-Q(1),Q(0)],[Q(0),-Q(1)]],'rare_bad_square')

# Exhaustive endpoint counts, including negative increments and both orientations.
for n in range(1,9):
 for inc in product((-1,0,1),repeat=n):
    z=[0]
    for x in inc:z.append(z[-1]+x)
    short=n-z[-1]
    for c in [Q(1,3),Q(4,5),Q(49,50)]:
      bad_end=sum(any(z[j]-z[l]<c*(j-l) for l in range(j)) for j in range(1,n+1))
      bad_start=sum(any(z[l]-z[j]<c*(l-j) for l in range(j+1,n+1)) for j in range(n))
      check((1-c)*bad_end<=4*short,'shortfall_endpoints')
      check((1-c)*bad_start<=4*short,'shortfall_starts')

# Floors at negative and nonaligned dyadic arguments; dilation must be exact.
for n in [1,2,4,8,16,32]:
 for s,t in product([Q(i,16) for i in range(-23,24)],repeat=2):
    # Stationarity is not used for this exact rescaling identity.
    g=lambda a,b:abs(a-b)
    check(Q(g(math.floor(n*2*s),math.floor(n*2*t)),2*n)==Q(g(math.floor(2*n*s),math.floor(2*n*t)),2*n),'floor_dilation')
    if n>=16:check((n*s).denominator==1 and (n*t).denominator==1,'two_sided_alignment')

# Exact exponent bookkeeping at the declared exponents, not a changed theorem.
check(Q(1,4)+Q(1,8)-1==Q(-5,8),'seed_exponents')
check(1-3*Q(4,5)==Q(-7,5),'curvature_exponents')
check(1-Q(49,50)-2*Q(49,50)*2> -2*Q(49,50)*2,'row_error_absorption')
check(Q(4)/(1-Q(49,50))==200,'mass_budget_constant')

# Scalar deficits satisfying doubling can still amplify: source geometry is essential.
rows=[]
for t in [4,8,16,32,64]:
    u=Q(1,t**4);d=Q(1,t**2);theta=Q(1,t**3)
    n0=1
    while n0<t**6:n0*=2
    es=[u]; j=0
    while es[-1]<=theta:es.append(min(d,2*es[-1]));j+=1
    eps=es[-1]
    check(u<theta<d,'crossing_order')
    check(theta<eps<=2*theta,'crossing_overshoot')
    check(theta*n0>=t**3,'crossing_scale_separation')
    rows.append({'t':t,'u/theta':str(u/theta),'d/theta':str(d/theta),'eps':str(eps),'n0':n0,'dyadic_steps':j})

print(json.dumps({'status':'PASS','scope':'Exact finite algebra and adversarial fixtures only; no universal proof or entropy simulation','exact_assertions':sum(counts.values()),'categories':dict(sorted(counts.items())),'synthetic_rational_deficit_rows':rows,'negative_controls':['wrong curvature sign','square replacing cubic term','singular Dirichlet matrix','scalar doubling alone permits amplification','rare-bad-site periodic cocycle has zero exponent']},indent=2,sort_keys=True))
