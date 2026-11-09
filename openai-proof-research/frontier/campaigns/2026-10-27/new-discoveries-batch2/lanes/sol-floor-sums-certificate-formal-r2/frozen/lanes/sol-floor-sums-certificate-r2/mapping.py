import pathlib,json,re,hashlib,functools,os
L=pathlib.Path(__file__).resolve().parent
def parse(s):
 stack=[];roots=[]
 for t in re.findall(r';[^\n]*|\(|\)|[^\s()]+',s):
  if t.startswith(';'):continue
  if t=='(':stack.append([])
  elif t==')':
   x=stack.pop();(stack[-1] if stack else roots).append(x)
  else:(stack[-1] if stack else roots).append(t)
 assert not stack;return roots
def expand(x,e):
 if isinstance(x,str):return e.get(x,x)
 if x[0]=='let':
  assert len(x)==3;d={k:expand(v,e) for k,v in x[1]};return expand(x[2],dict(e,**d))
 return tuple(expand(v,e) for v in x)
def poly(d):return tuple(sorted((k,v) for k,v in d.items() if v))
def add(terms):
 d={}
 for p,sgn in terms:
  for k,v in p:d[k]=d.get(k,0)+sgn*v
 return poly(d)
@functools.lru_cache(None)
def norm(x):
 if isinstance(x,str):
  try:return ((('const',),int(x)),) if int(x) else ()
  except ValueError:return ((('var',x),1),)
 op,*a=x
 if op in ['+','-']:return add((norm(v),-1 if op=='-' and (k>0 or len(a)==1) else 1) for k,v in enumerate(a))
 if op=='*':
  c=1;non=[]
  for v in a:
   p=norm(v)
   if not p:c=0
   elif len(p)==1 and p[0][0]==('const',):c*=p[0][1]
   else:non.append(p)
  assert len(non)<=1
  return poly({k:c*v for k,v in non[0]}) if non else (((('const',),c),) if c else ())
 if op in ['<=','>=','<','>','=']:
  d=add([(norm(a[0]),1),(norm(a[1]),-1)])
  if op in ['>=','>']:d=poly({k:-v for k,v in d});op={'<=':'<=','>=':'<=','<':'<','>':'<','=':'='}[op]
  return (op,d)
 if op=='ite':return ((('ite',norm(a[0]),norm(a[1]),norm(a[2])),1),)
 raise ValueError(op)
roots=parse((L/'frozen/all-m-query.smt2').read_text())
assert all(x[0] in ['set-info','declare-fun','assert','check-sat'] for x in roots)
assert all(len(x)==4 and x[2]==[] for x in roots if x[0]=='declare-fun')
decl={x[1]:x[3] for x in roots if x[0]=='declare-fun'}
assert decl=={v:'Int' for v in ['m','H','t','a','b','c','d']}
actual=[norm(expand(x[1],{})) for x in roots if x[0]=='assert']
expected=[('>=','m','1'),('>=','H','1'),('<=','H','m'),('>=','t','0'),('>=','m',('*','3','t')),('<=','m',('+',('*','3','t'),'2'))]
expected += [('>=',v,'0') for v in 'abcd']+[('<',v,'m') for v in 'abcd']+[('<=',u,v) for u,v in zip('abc','bcd')]
terms=[]
for mask in range(16):
 for level in range(1,5):
  z=('-',('+',*(v for j,v in enumerate('abcd') if mask>>j&1),'H'),('*',str(level),'m'))
  clip=('ite',('<=',z,'0'),'0',('ite',('>=',z,'H'),'H',z))
  terms.append(('*',str((-1)**(4-mask.bit_count())),clip))
expected.append(('<',('+',*terms),('*','-3','t')))
assert sorted(map(repr,actual))==sorted(repr(norm(x)) for x in expected)
N=[]
for line in (L/'dag.jsonl').open():
 d=json.loads(line);N.append(d.get('atom',tuple(d.get('args',[]))))
@functools.lru_cache(None)
def tree(i):return N[i] if isinstance(N[i],str) else tuple(tree(j) for j in N[i])
matched=[]
for i,x in enumerate(N):
 if isinstance(x,tuple) and N[x[0]]=='asserted':
  assert len(x)==2 and norm(tree(x[1])) in actual;matched.append(i)
out={'literal_query_mapping':'PASS','assertions':len(actual),'integer_declarations':decl,'mask_terms':64,'matched_proof_assertions':matched,'query_sha256':hashlib.sha256((L/'frozen/all-m-query.smt2').read_bytes()).hexdigest(),'scope':'Mapping only; not unsatisfiability or theorem proof'}
if not os.environ.get('CERT_VERIFY_ONLY'):(L/'query-map.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out))
