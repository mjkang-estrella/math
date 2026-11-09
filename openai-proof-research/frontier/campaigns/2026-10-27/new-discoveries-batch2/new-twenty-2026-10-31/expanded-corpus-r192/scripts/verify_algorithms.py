import pathlib,runpy,sys,math,itertools,fractions,random,json
D=pathlib.Path(__file__).resolve().parents[1]
s=(D/'scripts/pvanish.py').read_text();ns={'__file__':str(D/'scripts/pvanish.py')};exec(s[:s.index('rows=[]')],ns);parts=ns['parts'];char=ns['char'];deg=ns['deg'];checked=[]
for n in range(0,11):
 P=parts(n);f=math.factorial(n);assert sum(deg(la)**2 for la in P)==f
 sizes=[]
 for mu in P:
  z=1
  for c in set(mu):z*=c**mu.count(c)*math.factorial(mu.count(c))
  sizes.append(f//z)
 table=[[char(la,mu) for mu in P] for la in P]
 for i,row in enumerate(table):
  assert row[-1]==deg(P[i])
  for j in range(i+1):assert sum(x*y*z for x,y,z in zip(row,table[j],sizes))==(f if i==j else 0)
 checked.append({'n':n,'rows':len(P)})
s=(D/'scripts/word_sam.py').read_text();ns={'__file__':str(D/'scripts/word_sam.py')};exec(s[:s.index('rng=random.Random')],ns);comp=ns['complexity'];close=ns['close'];rng=random.Random(987)
for j in range(250):
 w=''.join(str(rng.randrange(2)) for _ in range(rng.randrange(1,65)));brute=max((len({w[i:i+n] for i in range(len(w)-n+1)})/n,n,len({w[i:i+n] for i in range(len(w)-n+1)})) for n in range(1,len(w)+1));assert comp(w)[0]==brute[0]
 for e in [0,1]:
  z=close(w,e);anti=lambda x:x[::-1].translate(str.maketrans('01','10')) if e else x[::-1];assert z.startswith(w) and anti(z)==z
  candidates=[w+anti(w[:k]) for k in range(len(w)+1)];assert len(z)==min(len(a) for a in candidates if anti(a)==a)
(D/'outputs/algorithm-verification.json').write_text(json.dumps({'character_table_orthogonality':checked,'word_crosschecks':250,'closure_minimality_cases':500,'status':'passed; diagnostics only, not Lean certification'},indent=2));print('PASS')
