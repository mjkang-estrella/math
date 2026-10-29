exec(open(__file__.replace('specialization.py','probe.py')).read().split('results=[]')[0])
a,b=s.symbols('a b')
p=R(2,a,b).as_expr();print('n2',s.factor(p));print('disc ym1',s.factor(s.discriminant(p.subs(y,-1),x)))
hits=[]
for n in range(2,7):
 for aa in range(n,n+9):
  for bb in range(aa,n+9):
   if aa==bb and n%2: continue
   p=R(n,aa,bb).as_expr();f=s.factor_list(p.subs(y,-1))[1]
   if len(f)>1: hits.append([n,aa,bb,str(s.factor(p.subs(y,-1)))])
print(hits[:12]);pathlib.Path(__file__).with_name('specialization-results.json').write_text(json.dumps(hits,indent=2))
