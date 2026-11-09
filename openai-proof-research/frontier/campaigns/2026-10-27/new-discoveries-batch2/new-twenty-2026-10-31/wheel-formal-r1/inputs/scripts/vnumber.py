import itertools,pathlib,json
D=pathlib.Path(__file__).resolve().parents[1];out=[]
def comps(n,E,S):
 todo=set(range(n))-S;C=[]
 while todo:
  q=[todo.pop()]
  for v in q:
   for a,b in E:
    w=b if a==v else a if b==v else -1
    if w in todo:todo.remove(w);q.append(w)
  C.append(q)
 return C
def rank(rows):
 piv={}
 for col in rows:
  while col:
   l=col.bit_length()-1
   if l not in piv:piv[l]=col;break
   col^=piv[l]
 return len(piv)
for name,n,E,maxd in [('C6',6,[(i,(i+1)%6) for i in range(6)],4),('C7',7,[(i,(i+1)%7) for i in range(7)],4),('C8',8,[(i,(i+1)%8) for i in range(8)],3),('C9',9,[(i,(i+1)%9) for i in range(9)],3),('B2',7,[((i-1)//2,i) for i in range(1,7)],4)]:
 primes=[]
 for mask in range(1<<n):
  S={i for i in range(n) if mask>>i&1};C=comps(n,E,S)
  if all(len(C)>len(comps(n,E,S-{v})) for v in S):primes.append((S,C))
 for degree in range(maxd+1):
  monoms=[]
  for factors in itertools.combinations_with_replacement(range(2*n),degree):
   exp=[0]*(2*n)
   for i in factors:exp[i]+=1
   monoms.append(exp)
  eqs=[]
  for S,C in primes:
   classes={}
   for j,e in enumerate(monoms):
    if any(e[i] or e[n+i] for i in S):continue
    key=(tuple(e[i]+e[n+i] for i in range(n)),tuple(sum(e[i] for i in component) for component in C))
    classes[key]=classes.get(key,0)|(1<<j)
   eqs.append(list(classes.values()))
  fullrank=rank(row for block in eqs for row in block);local=[]
  for p in range(len(primes)):
   other=rank(row for q,block in enumerate(eqs) if q!=p for row in block)
   if fullrank>other:local.append(sorted(primes[p][0]))
  row={'graph':name,'n':n,'degree':degree,'monomials':len(monoms),'minimal_primes':len(primes),'full_stack_rank':fullrank,'separator_cutsets':local,'field':'F2','method':'J radical prime decomposition; separators in intersection of other P_T but outside P_T; row spaces of monomial equivalence classes'};out.append(row);(D/'outputs/vnumber.json').write_text(json.dumps(out,indent=2)+'\n');print(row,flush=True)
  if local:break
