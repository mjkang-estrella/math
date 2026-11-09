import math,itertools,json,pathlib
w=pathlib.Path(__file__).parent
def h(p):return -sum(x*math.log(x) for x in [p,1-p] if x>0)
def H(r,t):return (1+t)/2*h((1-r)*(1-t)/2)+(1-t)/2*h((1-r)*(1+t)/2)
def F(l,t):return sum(2**(-i)*H(l**i,t) for i in range(1,100))-H(l,t)
def c(r):return -(1-r)/2*math.log((1+r)/(1-r))-(1-r)/(2*(1+r))
lo,hi=.1,.99
for _ in range(120):
 a=lo+(hi-lo)/3;b=hi-(hi-lo)/3
 if F(a,0)<F(b,0):lo=a
 else:hi=b
l=(lo+hi)/2;out={'diagnostic_only':True,'lambda_approx':l,'P00_approx':(1+l)/2,'value_approx':F(l,0),'transverse_second_derivative_formula':2*(sum(2**(-i)*c(l**i) for i in range(1,100))-c(l)),'finite_entropy_bridge':[]}
for n in range(1,8):
 t=.2;P=[[1-(1-l)*(1-t)/2,(1-l)*(1-t)/2],[(1-l)*(1+t)/2,1-(1-l)*(1+t)/2]];pi=[(1+t)/2,(1-t)/2];words=list(itertools.product(range(2),repeat=n));probs={a:pi[a[0]]*math.prod(P[a[i]][a[i+1]] for i in range(n-1)) for a in words};avg=0
 for mask in range(2**n):
  inds=[j for j in range(n) if mask>>j&1];d={}
  for a,p in probs.items():
   k=tuple(a[j] for j in inds);d[k]=d.get(k,0)+p
  avg-=sum(p*math.log(p) for p in d.values() if p>0)/2**n
 rhs=(1-2**(-n))*h(pi[0])+sum((n-i)*2**(-i-1)*H(l**i,t) for i in range(1,n));out['finite_entropy_bridge'].append({'N':n,'error':avg-rhs})
out['perturbation_checks']=[{'dl':dl,'t':t,'difference':F(l+dl,t)-F(l,0)} for dl in [-.001,0,.001] for t in [-.001,0,.001]]
(w/'markov-diagnostics.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
