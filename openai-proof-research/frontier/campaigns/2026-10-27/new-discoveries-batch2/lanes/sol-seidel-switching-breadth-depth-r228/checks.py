from pathlib import Path
import sympy as s,itertools,json
p=Path(__file__).resolve().parent
V=[(x,y) for x in range(1,8) for y in range(8) if (x&y).bit_count()%2==0]
S=s.Matrix([[0 if a==b else (-1)**(((a[0]&b[1]).bit_count()+(a[1]&b[0]).bit_count())%2) for b in V] for a in V])
old=json.loads((p/'checks/matrix-exact.json').read_text());assert S.tolist()==old['matrix']
assert str(s.factor(S.charpoly().as_expr()))==old['charpoly']
for lam in [-5,3,7]:
 R,piv=(S-lam*s.eye(28)).rref();free=[j for j in range(28) if j not in piv];count=0
 for vals in itertools.product([-1,1],repeat=len(free)-1):
  vals=(1,)+vals
  if all(abs(sum(R[i,k]*v for k,v in zip(free,vals)))==1 for i in range(len(piv))):count+=2
 assert count==old['sign_intersections'][str(lam)]['total_sign_vectors']
print('exact charpoly and all three sign intersections replay PASS')
