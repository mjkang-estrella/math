exec(open('exact.py').read().split('stats={};')[0])
rows=json.loads((root/'logs/exact-result.json').read_text())['selected']
checks=0
for row in rows:
 a=row['a'];w=apery(a);alpha=row['alpha'];h=row['h'];q=row['factorizations'][0];F=max(w)-a[0]
 C=[c for c in range(F+1) if inside(c,w) and not inside(c+alpha,w)]
 B=[c for c in range(F+alpha+1) if inside(c,w) and not inside(c-alpha,w)]
 D=sorted(sum(v*x for v,x in zip(z,a)) for z in product(*(range(t+1) for t in q)))
 assert len(set(D))==len(D) and D==C
 assert len(B)-len(C)==alpha
 N=F+2*alpha+5
 for i in range(N):
  assert int(inside(i,w))-int(inside(i-alpha,w))==int(i in B)-int(i-alpha in C)
  checks+=1
 assert sorted(h-c for c in C)==C
# Exact negative closure witness, independent factorization lists.
a=(5,8,11,14);w=apery(a);assert w==[0,11,22,8,14]
assert pf(a,w)==[17];assert facts(a,16)==[(0,2,0,0),(1,0,1,0)]
# Actual published AIMS failure cases do not meet AP hypothesis.
for a,expected in [((6,8,9,11),[3,10,13]),((7,10,12,13),[15,16,18])]:
 p=pf(a,apery(a));assert p==expected and p[1]-p[0]!=p[2]-p[1]
print(json.dumps({'boundary_generating_coefficients':checks,'source_rows':len(rows),'weak_hypothesis_obstruction':'PASS','published_counterexample_scope_checks':2}))
