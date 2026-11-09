from pathlib import Path
import sympy as s,json,datetime,os,resource
os.sched_setaffinity(0,set(sorted(os.sched_getaffinity(0))[:2]));resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
t,u,h=s.symbols('t u h');Q=160801*t**3-657640*t**2-187600*t+2224000
F={e:s.expand(((1+t)**2+t*t/400)*((3-t)**2+(1-e*t/20)**2)) for e in [1,-1]}
assert s.expand(F[1]-10-t*Q/160000)==0
assert s.expand(F[-1]-F[1]-t*(32080*t*t+64000*t+32000)/160000)==0
rows=[(0,2,[2224000,s.Rational(6296800,3),s.Rational(3291040,3),504648]),(2,3,[504648,s.Rational(625396,3),s.Rational(44014,3),84067]),(3,4,[84067,s.Rational(460388,3),486048,1242624])]
for a,b,c in rows:
 assert all(v>0 for v in c)
 assert s.expand(Q.subs(t,a+(b-a)*u)-sum(c[j]*s.binomial(3,j)*u**j*(1-u)**(3-j) for j in range(4)))==0
assert s.expand(Q.subs(t,h+4)-(160801*h**3+1271972*h*h+2269728*h+1242624))==0
s0=3+s.sqrt(2)/2
assert s.simplify(s0*s0*((s0-4)**2+1)-(s.Rational(71,4)-2*s.sqrt(2)))==0
s1=(6+s.sqrt(2))/4
assert s.simplify(s1*s1*((s1-2)**2+s.Rational(1,4))-(71-8*s.sqrt(2))/64)==0
assert s.Rational(17,4)/(s.Rational(1601,400)*s.Rational(9,20)**2)==s.Rational(680000,129681)
assert 680000*16>129681*49
bounds=[s.Rational(121,16),s.Rational(25,16)*(4+s.Rational(19,20)**2),4*(1+s.Rational(9,10)**2),9*s.Rational(17,20)**2,16*s.Rational(4,5)**2,25]
assert all(x>s.Rational(153,25) for x in bounds)
D=Path(__file__).resolve().parents[1]
(D/'arithmetic-receipt.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'passed':True,'sympy':s.__version__,'checks':['wedge ray polynomial identities','positive Bernstein coefficients and exact expansions on three intervals','positive shifted tail coefficients','slit stationary minimum values','boundary witness squared ratio and strict rational comparison','six uniform lower bounds'],'scope':'Supplementary exact algebra verification; not a Lean or novelty certificate'},indent=2)+'\n')
print('exact arithmetic PASS')
