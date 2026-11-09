import sympy as s,json,resource,os
resource.setrlimit(resource.RLIMIT_CPU,(110,110));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);t=s.symbols('t');a,b,c,d,e=s.symbols('a b c d e');q=s.Rational
sol=s.solve([a-q(17,20)*d-q(3,80),b-q(17,20)*(t*b+e)/(t+1)-q(3,160),c-q(17,20)*(b+t*e)/(t+1)-q(3,160),d-q(17,20)*(t*a+2*c)/(t+2)-q(1,80),e-q(17,20)*(a+(t+1)*c)/(t+2)-q(1,80)],[a,b,c,d,e]);sol={str(k):s.factor(v)for k,v in sol.items()};print(sol);json.dump({k:str(v)for k,v in sol.items()},open('outputs/pagerank-symbolic.json','w'),indent=2)
