"""Fail-closed partial checker. No SMT imports or subprocesses."""
import json,pathlib,collections,math,time,resource,os
from fractions import Fraction
L=pathlib.Path(__file__).resolve().parent
N=[]
for line in (L/'dag.jsonl').open():
 d=json.loads(line);assert d['id']==len(N);N.append(d.get('atom',tuple(d.get('args',[]))))
def h(i):
 x=N[i];return x if isinstance(x,str) else h(x[0])
def ishead(i,s):return isinstance(N[i],tuple) and h(i)==s
def fmt(i):
 out=[];todo=[i];size=0
 while todo and size<4000:
  z=todo.pop()
  if isinstance(z,str):out.append(z);size+=len(z);continue
  x=N[z]
  if isinstance(x,str):out.append(x);size+=len(x)
  else:
   out.append('(');size+=1;todo.append(')')
   for j in reversed(x):todo.extend([' ',j])
 return ''.join(out)+('... [bounded DAG rendering]' if todo else '')
rules={'rewrite','asserted','mp','hypothesis','monotonicity','intro-def','trans','def-axiom','unit-resolution','th-lemma','lemma','apply-def','not-or-elim'}
root=json.loads((L/'dag-index.json').read_text())['root']
used=set();todo=[root]
while todo:
 i=todo.pop()
 if i in used:continue
 used.add(i)
 if isinstance(N[i],tuple):todo.extend(N[i])
P={i for i in used if isinstance(N[i],tuple) and h(i) in rules}
assert root in P
expr_ops={'+','-','*','<=','>=','<','>','=','~','ite','and','or','not'}
sorts={}
for i in sorted(used):
 x=N[i]
 if isinstance(x,str):
  if x in ['true','false']:sorts[i]='Bool'
  elif x in ['m','H','t','a','b','c','d'] or x.startswith('z3name!') or x.lstrip('-').isdigit():sorts[i]='Int'
  else:assert x in rules|expr_ops
  continue
 op=h(i);a=x[1:]
 if op in rules:
  assert len(a)>=1 and all(j in P for j in a[:-1]),('unrecognized proof dependency',i)
  assert sorts[a[-1]]=='Bool'
  if op in ['rewrite','asserted','hypothesis','intro-def','def-axiom']:assert len(a)==1
  sorts[i]='Proof';continue
 assert op in expr_ops
 if op in ['+','-','*']:
  assert a and all(sorts[j]=='Int' for j in a);sorts[i]='Int'
 elif op in ['<=','>=','<','>']:
  assert len(a)==2 and all(sorts[j]=='Int' for j in a);sorts[i]='Bool'
 elif op in ['=','~']:
  assert len(a)==2 and sorts[a[0]]==sorts[a[1]] and sorts[a[0]] in ['Int','Bool'];sorts[i]='Bool'
 elif op=='ite':
  assert len(a)==3 and sorts[a[0]]=='Bool' and sorts[a[1]]==sorts[a[2]] and sorts[a[1]] in ['Int','Bool'];sorts[i]=sorts[a[1]]
 else:
  assert (op!='not' or len(a)==1) and all(sorts[j]=='Bool' for j in a);sorts[i]='Bool'
def conclusion(i):return N[i][-1]
# Affine normal forms over rational coefficients; unsupported arithmetic raises.
ac={}
def affine(i):
 if i in ac:return ac[i]
 x=N[i]
 if isinstance(x,str):
  try:r={None:Fraction(x)}
  except ValueError:r={x:Fraction(1)}
 else:
  op=h(i);a=x[1:]
  if op in ['+','-']:
   r={}
   for k,v in enumerate(a):
    sign=-1 if op=='-' and (k>0 or len(a)==1) else 1
    for z,c in affine(v).items():r[z]=r.get(z,0)+sign*c
  elif op=='*':
   r={None:Fraction(1)}
   for v in a:
    b=affine(v)
    if any(k is not None for k in r) and any(k is not None for k in b):raise ValueError('nonlinear')
    if all(k is None for k in b):r={k:c*b.get(None,0) for k,c in r.items()}
    else:r={k:c*r.get(None,0) for k,c in b.items()}
  elif op=='ite' and not isbool(i):r={'@ite:'+str(i):Fraction(1)}
  else:raise ValueError('unsupported arithmetic '+op)
 r={k:v for k,v in r.items() if v};ac[i]=r;return r
def relation(i):
 x=N[i];op=h(i);a=affine(x[1]).copy()
 for k,v in affine(x[2]).items():a[k]=a.get(k,0)-v
 # Convert to integer A >= 0, strict bounds to A >= 1.
 if op in ['<=','<']:a={k:-v for k,v in a.items()}
 den=math.lcm(*(v.denominator for v in a.values())) if a else 1
 a={k:int(v*den) for k,v in a.items()}
 if op in ['<','>']:a[None]=a.get(None,0)-1
 c=a.pop(None,0);g=math.gcd(*a.values()) if a else 0
 if not g:return c>=0
 c=c//g;a={k:v//g for k,v in a.items()}
 return ('ge',tuple(sorted(a.items())),c)
# Reduced ordered Boolean decision diagrams. Each normalized arithmetic relation is
# an independent propositional atom; this can prove fewer identities, never more.
B=[None,None];bc={};memo={};atoms={}
def bnode(v,lo,hi):
 if lo==hi:return lo
 key=(v,lo,hi)
 if key not in bc:
  if len(B)>=100000:raise ValueError('bounded BDD capacity 100000 reached')
  bc[key]=len(B);B.append(key)
 return bc[key]
def atom(key):
 if key not in atoms:atoms[key]=len(atoms)
 return bnode(atoms[key],0,1)
def geform(d):
 d={k:Fraction(v) for k,v in d.items() if v};den=math.lcm(*(v.denominator for v in d.values())) if d else 1
 d={k:int(v*den) for k,v in d.items()};c=d.pop(None,0);g=math.gcd(*d.values()) if d else 0
 if not g:return int(c>=0)
 c//=g;d={k:v//g for k,v in d.items()};a=tuple(sorted(d.items()))
 if a[0][1]<0:return neg(atom(('ge',tuple((k,-v) for k,v in a),-c-1)))
 return atom(('ge',a,c))
def neg(a):return app('xor',a,1)
def app(op,a,b):
 key=(op,a,b)
 if key in memo:return memo[key]
 if a<2 and b<2:r=int({'and':a and b,'or':a or b,'xor':bool(a)!=bool(b)}[op])
 else:
  va=B[a][0] if a>1 else 10**9;vb=B[b][0] if b>1 else 10**9;v=min(va,vb)
  al,ah=B[a][1:] if va==v else (a,a);bl,bh=B[b][1:] if vb==v else (b,b)
  r=bnode(v,app(op,al,bl),app(op,ah,bh))
 memo[key]=r;return r
nc={}
def isbool(i):
 x=N[i]
 if isinstance(x,str):return x in ['true','false']
 return h(i) in ['not','and','or','=','<=','>=','<','>','~'] or (h(i)=='ite' and isbool(x[2]) and isbool(x[3]))
def boolform(i):
 if i in nc:return nc[i]
 x=N[i]
 if x=='true':r=1
 elif x=='false':r=0
 elif isinstance(x,str):raise ValueError('non-Boolean atom '+x)
 else:
  op=h(i);a=x[1:]
  if op=='not':r=neg(boolform(a[0]))
  elif op in ['and','or']:
   r=int(op=='and')
   for v in a:r=app(op,r,boolform(v))
  elif op in ['<=','>=','<','>']:
   z=relation(i);r=int(z) if isinstance(z,bool) else geform(dict(z[1])|{None:z[2]})
  elif op=='=':
   try:
    aa=affine(a[0]).copy();bb=affine(a[1])
    for k,v in bb.items():aa[k]=aa.get(k,0)-v
    r=app('and',geform(aa),geform({k:-v for k,v in aa.items()}))
   except ValueError:
    if isbool(a[0]) and isbool(a[1]):r=neg(app('xor',boolform(a[0]),boolform(a[1])))
    else:r=atom(('opaque-integer-equality',min(a),max(a)))
  elif op=='ite':
   c,t,f=map(boolform,a);r=app('or',app('and',c,t),app('and',neg(c),f))
  else:raise ValueError('unsupported Boolean '+op)
 nc[i]=r;return r
def tautological(prem,c):
 b=1
 for p in prem:b=app('and',b,boolform(p))
 return app('and',b,neg(boolform(c)))==0
def constraints(i,truth=True):
 x=N[i]
 if isinstance(x,str):
  if x not in ['true','false']:raise ValueError('non-arithmetic literal')
  return [] if (x=='true')==truth else [{None:-1}]
 op=h(i);a=x[1:]
 if op=='not':return constraints(a[0],not truth)
 if (op=='and' and truth) or (op=='or' and not truth):
  return [c for v in a for c in constraints(v,truth)]
 if op not in ['<=','>=','<','>','=']:raise ValueError('arithmetic Boolean branching')
 if op=='=':
  if not truth:raise ValueError('disequality needs branches')
  aa=affine(a[0]).copy()
  for k,v in affine(a[1]).items():aa[k]=aa.get(k,0)-v
  return [aa,{k:-v for k,v in aa.items()}]
 if not truth:op={'<=':'>','>=':'<','<':'>=','>':'<='}[op]
 aa=affine(a[0]).copy()
 for k,v in affine(a[1]).items():aa[k]=aa.get(k,0)-v
 if op in ['<=','<']:aa={k:-v for k,v in aa.items()}
 if op in ['<','>']:aa[None]=aa.get(None,0)-1
 return [aa]
def row(d):
 d={k:Fraction(v) for k,v in d.items() if v}
 den=math.lcm(*(v.denominator for v in d.values())) if d else 1
 d={k:int(v*den) for k,v in d.items()};c=d.pop(None,0)
 g=math.gcd(*d.values()) if d else 1
 return tuple(sorted((k,v//g) for k,v in d.items())),c//g
def arith_attempt(prem,c,strategy):
 # Exact integer cutting-plane normalization followed by rational elimination.
 rows=set(row(z) for p in prem for z in constraints(p));rows.update(row(z) for z in constraints(c,False))
 for step in range(150):
  if any(not a and b<0 for a,b in rows):return True
  rows={(a,b) for a,b in rows if a}
  if not rows:return False
  variables={k for a,b in rows for k,v in a}
  counts={k:[0,0] for k in variables}
  for a,b in rows:
   for k,v in a:counts[k][v<0]+=1
  k=min(variables,key=lambda k:(counts[k][0]*counts[k][1], sum((j+1)*ord(ch) for j,ch in enumerate(k))*(2*strategy+1)%1009 if strategy else k))
  if counts[k][0]*counts[k][1]+len(rows)>4000:raise ValueError('bounded arithmetic elimination 4000 rows')
  pos=[];negrows=[];zero=[]
  for a,b in rows:
   d=dict(a);v=d.pop(k,0)
   (pos if v>0 else negrows if v<0 else zero).append((d,b,v))
  new={row(dict(d,**{} ) | ({None:b} if b else {})) for d,b,v in zero}
  for d,b,v in pos:
   for e,c,w in negrows:
    z={j:-w*d.get(j,0)+v*e.get(j,0) for j in d.keys()|e.keys()};z[None]=-w*b+v*c;new.add(row(z))
  rows=new
 raise ValueError('bounded arithmetic elimination 150 variables')
def arith_contradiction(prem,c):
 for strategy in range(12):
  try:
   if arith_attempt(prem,c,strategy):return True
  except ValueError:
   if strategy==11:raise
 return False
results={};stats=collections.Counter();examples={};residual=[]
matched=set(json.loads((L/'query-map.json').read_text())['matched_proof_assertions'])
# Validate every extension globally: fresh symbols, unique definitions, acyclic
# dependence, and exactly the two clauses defining an ite. This extends every
# assignment to original variables uniquely, so refutation remains conservative.
definitions={};definition_nodes={}
def symbols(i):
 seen=set();out=set();todo=[i]
 while todo:
  j=todo.pop()
  if j in seen:continue
  seen.add(j);x=N[j]
  if isinstance(x,str):out.add(x)
  else:todo.extend(x)
 return out
for i in sorted(P):
 if h(i)!='intro-def':continue
 c=conclusion(i);assert ishead(c,'and') and len(N[c])==3
 u,v=N[c][1:];assert ishead(u,'or') and ishead(v,'or') and len(N[u])==len(N[v])==3
 np,eq1=N[u][1:];p,eq2=N[v][1:];assert ishead(np,'not') and N[np][1]==p
 assert ishead(eq1,'=') and ishead(eq2,'=')
 z,t=N[eq1][1:];zz,f=N[eq2][1:];assert z==zz and isinstance(N[z],str) and N[z].startswith('z3name!')
 assert N[z] not in definitions
 definitions[N[z]]=(p,t,f);definition_nodes[i]=(z,p,t,f)
for z,trip in definitions.items():
 deps=set().union(*(symbols(j) for j in trip)) & definitions.keys()
 assert z not in deps
visiting=set();done=set()
def visit(z):
 assert z not in visiting
 if z in done:return
 visiting.add(z)
 for dep in set().union(*(symbols(j) for j in definitions[z])) & definitions.keys():visit(dep)
 visiting.remove(z);done.add(z)
for z in definitions:visit(z)
assert {N[i] for i in used if isinstance(N[i],str) and N[i].startswith('z3name!')}==set(definitions)
start=time.monotonic()
for i in sorted(P):
 # Bounds are per rule. Never let earlier diagnostics consume a later rule's budget.
 B[:]=[None,None];bc.clear();memo.clear();atoms.clear();nc.clear()
 x=N[i];op=h(i);args=x[1:];c=args[-1];deps=[j for j in args[:-1] if j in P]
 local=False;reason='unsupported rule';hyps=set().union(*(results[j]['hyps'] for j in deps)) if deps else set()
 try:
  if op=='hypothesis':local=len(args)==1;hyps={c};reason='assumption'
  elif op=='asserted':local=i in matched;reason='exact query membership via independent mapping'
  elif op=='rewrite':
   if ishead(c,'=') and len(N[c])==3:
    l,r=N[c][1:]
    if l==r:local=True
    elif isbool(l) and isbool(r):local=boolform(l)==boolform(r)
    else:
     try:local=affine(l)==affine(r)
     except ValueError:local=False
   reason='independent affine/Boolean normalization'
  elif op=='mp':
   if len(deps)==2:
    p,q=map(conclusion,deps)
    local=ishead(q,'=') and tuple(N[q][1:])==(p,c)
   reason='modus ponens'
  elif op=='trans':
   eqs=[N[conclusion(j)] for j in deps]
   local=bool(eqs) and all(h(conclusion(j)) in ['=','~'] for j in deps) and h(c) in ['=','~'] and N[c][1]==eqs[0][1] and N[c][2]==eqs[-1][2] and all(eqs[k][2]==eqs[k+1][1] for k in range(len(eqs)-1));reason='equality chain'
  elif op=='monotonicity':
   eqs=[N[conclusion(j)] for j in deps]
   if h(c) in ['=','~'] and all(h(conclusion(j)) in ['=','~'] for j in deps):
    l,r=map(lambda v:N[v],N[c][1:]);pairs={(q[1],q[2]) for q in eqs}
    local=isinstance(l,tuple) and isinstance(r,tuple) and len(l)==len(r) and l[0]==r[0] and all(a==b or (a,b) in pairs for a,b in zip(l[1:],r[1:]))
   reason='congruence'
  elif op in ['unit-resolution','not-or-elim']:
   local=bool(deps) and tautological([conclusion(j) for j in deps],c);reason='propositional entailment only'
  elif op=='lemma':
   local=len(deps)==1 and N[conclusion(deps[0])]=='false'
   if local:hyps={j for j in hyps if app('and',neg(boolform(c)),neg(boolform(j)))!=0}
   reason='exact propositional hypothesis discharge'
  elif op=='th-lemma':
   local=arith_contradiction([conclusion(j) for j in deps],c);reason='exact integer normalization and Fourier-Motzkin contradiction'
  elif op=='intro-def':local=i in definition_nodes;reason='globally checked acyclic fresh ite extension'
  elif op=='apply-def':
   if len(deps)==1 and deps[0] in definition_nodes and h(c) in ['=','~']:
    z,p,t,f=definition_nodes[deps[0]];l,r=N[c][1:]
    local=r==z and ishead(l,'ite') and tuple(N[l][1:])==(p,t,f)
   reason='checked definition expansion'
  elif op=='def-axiom':local=boolform(c)==1;reason='propositional tautology'
 except (ValueError,RecursionError,TypeError,IndexError) as e:reason='unsupported normalization: '+str(e)
 valid=local and all(results[j]['valid'] for j in deps)
 closed=valid and not hyps
 results[i]={'local':local,'valid':valid,'closed':closed,'hyps':hyps}
 stats[(op,'local-pass' if local else 'GAP')]+=1
 if not local:
  residual.append({'id':i,'rule':op,'reason':reason,'premises':deps,'conclusion':c})
  examples.setdefault(op,{'id':i,'reason':reason,'expression':fmt(i)[:4000]})
passed=results[root]['closed'] and not residual and N[conclusion(root)]=='false'
report={'status':'independent computational certificate PASS; acceptance HOLD' if passed else 'INCOMPLETE / HOLD','certificate_PASS':passed,'root':root,'root_conclusion':fmt(conclusion(root)),'root_closed':results[root]['closed'],'used_proof_nodes':len(P),'rule_results':{k[0]+':'+k[1]:v for k,v in stats.items()},'unsupported_examples':examples,'gap_nodes':len(residual),'warning':'Not Lean; independent adversarial review and prior/eligibility clearance remain required.','seconds':time.monotonic()-start,'BDD_nodes':len(B),'maxrss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
if not os.environ.get('CERT_VERIFY_ONLY'):
 (L/'partial-check.json').write_text(json.dumps(report,indent=2));(L/'residual.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in residual))
print(json.dumps(report,indent=2))
