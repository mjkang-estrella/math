import os,resource,json,hashlib,zipfile,re,sys
from pathlib import Path
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
sys.dont_write_bytecode=True
import sympy as s
p=Path(__file__).resolve().parents[2]; lane=p/'contact-review-r2'; z,w,x,t,u,L=s.symbols('z w x t u L'); I=s.I
N=(w*z-w-1)*(w*z+w-1); Q=-w*w*z**3+2*w*w*z+4*w*z*z+2*w*z-w-3*z
M=s.Matrix([[-z,1,1,1,0],[1,-w,0,1,0],[1,0,-w,0,1],[1,1,0,-z,1],[0,0,1,1,-z]])
assert s.expand(M.det()-Q)==0; assert s.expand(M.minor_submatrix(0,0).det()-N)==0
F=(L*(1-2*t*t)+t-t**3)*u*u+(-4*L-2*L*t+L*t*t-2*t)*u+3*L+t
assert s.cancel(t*(N-L*Q).subs({z:1/t,w:t*u})-F)==0
p1=1-t+t*t-t**3/2-t**4+(s.Rational(17,4)-1/(2*L))*t**5
assert all(s.expand(F.subs(u,p1)).coeff(t,k)==0 for k in range(6))
p3=3+(3-2/L)*t
assert all(s.expand(F.subs(u,p3)).coeff(t,k)==0 for k in range(2))
R=s.expand(x**3*(Q-I*N).subs(z,-1/x)); A=1-I*x-2*x*x+I*x**3; B=4-(2+2*I)*x-x*x; C=3-I*x
assert s.expand(R-(A*w*w+x*B*w+x*x*C))==0
P=-1-x-x*x-x**3/2+x**4
assert s.expand(A*P*P+B*P+C).coeff(x,5)==-s.Rational(17,2)+I
assert s.expand(9*A-3*B+C).coeff(x,1)==6-4*I
Z,W=s.symbols('Z W'); a=I*(1-Z); b=1+Z; c=I*(1-W); e=1+W
Nc=b*(c*a-c*b-b*e)*(c*a+c*b-b*e)
Qc=-c*c*a**3+2*c*c*a*b*b+4*c*a*a*b*e+2*c*a*b*b*e-c*b**3*e-3*a*b*b*e*e
qb=s.expand(Qc+I*Nc); pb=s.expand(Qc-I*Nc)
assert s.cancel(Z**3*W**2*s.conjugate(pb.subs({Z:1/s.conjugate(Z),W:1/s.conjugate(W)}))-qb)==0
assert s.Poly(pb,Z,W).degree_list()==(3,2)
assert s.Poly(s.gcd(pb,qb),Z,W).total_degree()==0
# Locality objection: reduced stable RIF product, with two distinct points above Z=-1.
p2=2+Z+W; q2=2*Z*W+Z+W
pp=s.expand(pb*p2); qq=s.expand(qb*q2)
assert s.Poly(s.gcd(pp,qq),Z,W).total_degree()==0
assert s.expand(qb.subs(Z,-1)+8*I*(W-1)**2)==0
assert s.expand(q2.subs(Z,-1))==-1-W
assert qq.subs({Z:-1,W:-1})==0
assert s.Poly(s.gcd(pb.subs(W,-W)*(2+Z-W),qb.subs(W,-W)*(2*Z*W+W-Z)),Z,W).total_degree()==0
# q2 zero W=-Z/(2Z+1), radial height quadratic on |Z|=1.
# |2Z+1|^2 = 1+2|Z+1|^2, so 1-|W| = 1-1/sqrt(1+2h^2).
h=s.symbols('h',real=True)
assert s.limit((1-1/s.sqrt(1+2*h*h))/h**2,h,0)==1
replay={}
for name in ['contact-formal-r5/work/extracted-01/replay-logs','contact-manuscript-r1/receipts/fresh-replay']:
 d=p/name; complete=json.loads((d/'complete.json').read_text()); assert complete['status']=='PASS'
 for fn,sha in complete['source_sha256'].items():
  assert hashlib.sha256((p/'contact-formal-r5/formal'/fn).read_bytes()).hexdigest()==sha
 receipts=[json.loads(f.read_text()) for f in d.glob('*.receipt.json')]
 for f in d.glob('*.receipt.json'):
  r=json.loads(f.read_text()); assert r.get('killed') is None
  assert r['returncode']==(1 if f.name.startswith('negative-') else 0)
 replay[name]={'receipt_count':len(receipts),'maximum_sampled_rss_bytes':max(r.get('peak_rss_bytes',r.get('peak_private_bytes',0)) for r in receipts),'maximum_wall':max(r.get('wall',0) for r in receipts),'all_sources_match':True}
with zipfile.ZipFile(p/'contact-manuscript-r1/contact-source-only.zip') as f:
 assert f.testzip() is None
 for fn in (p/'contact-formal-r5/formal').glob('*.lean'):
  names=[n for n in f.namelist() if n.endswith('/formal/'+fn.name) or n=='formal/'+fn.name]; assert len(names)==1
  assert f.read(names[0])==fn.read_bytes()
for name in replay:
 inv=json.loads((p/name/'audit-inventory.json').read_text())
 assert inv['declaration_count']==314
 for decl in inv['declarations']:
  assert not decl['unsafe'] and not decl['partial']
  assert set(decl['axioms']) <= {'propext','Classical.choice','Quot.sound'}
 replay[name]['audited_declarations']=314
for fn in (p/'contact-formal-r5/formal').glob('*.lean'):
 # Show matches, distinguish audit checks from proof gaps manually.
 for i,line in enumerate(fn.read_text().splitlines(),1):
  if re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',line): print('SCAN',fn.name,i,line)
print(json.dumps({'exact_algebra':'PASS','locality_objection':{'product_reduced':True,'q6_at_Z_minus_one':str(s.factor(qb.subs(Z,-1))),'q2_zero':'-Z/(2Z+1)','q2_height_over_displacement_squared_limit':1,'two_true_local_orders_at_different_points':[6,2],'same_named_point_predicate_can_admit':[2,6]},'replay_receipts':replay},indent=2))
