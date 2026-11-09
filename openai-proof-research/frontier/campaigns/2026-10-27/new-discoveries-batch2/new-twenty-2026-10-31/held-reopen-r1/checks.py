import pathlib,json
L=pathlib.Path(__file__).parent; B=L.parent
old=json.loads((L/'ledger-excerpts.json').read_text())
def pick(x):
 if isinstance(x,dict):
  if str(x.get('mathdb_id')) in ['330264','352038','324342']:return [x]
  return sum((pick(v) for v in x.values()),[])
 if isinstance(x,list):return sum((pick(v) for v in x),[])
 return []
now=pick(json.loads((B/'ledger.json').read_text()))
(L/'ledger-excerpts-after.json').write_text(json.dumps(now,indent=2))
(L/'ledger-comparison.json').write_text(json.dumps({'whole_ledger_changed':True,'target_entries_unchanged':old==now,'note':'Observed concurrent read-only input change; this lane issued no ledger write. Counts not frozen for this review.'},indent=2))
r=json.loads((B/'conference-mds-resume-r4/data/lean_cert.json').read_text())
W=r['W']; p=19
assert len(W)==20 and all(len(a)==20 for a in W)
assert all(sum(W[i][k]*W[j][k] for k in range(20))==(19 if i==j else 0) for i in range(20) for j in range(20))
assert all(W[i][j]==(-W[j][i]) for i in range(20) for j in range(20))
word=[sum(r['coeff'][i]*W[i][j] for i in range(20))%p for j in range(20)]
assert word==[a%p for a in r['word']]
weight=sum(a!=0 for a in word); assert weight==9
A=[[x%p for x in a] for a in W]; rank=0
for c in range(20):
 t=next((i for i in range(rank,20) if A[i][c]),None)
 if t is None:continue
 A[rank],A[t]=A[t],A[rank];inv=pow(A[rank][c],-1,p)
 A[rank]=[x*inv%p for x in A[rank]]
 for i in range(20):
  if i!=rank:
   a=A[i][c]; A[i]=[(x-a*y)%p for x,y in zip(A[i],A[rank])]
 rank+=1
assert rank==10
sq=sorted({a*a%19 for a in range(1,19)})
one=[a for a in range(1,19) if (a*a+19)%19==0]
two=[(a,b) for a in range(1,19) for b in range(1,19) if (a*a+b*b+19)%19==0]
assert not one and not two and 18 not in sq
(L/'independent-conference-check.json').write_text(json.dumps({'nonzero_squares_mod19':sq,'alpha_solutions':one,'alpha_beta_solutions':two,'gram_verified':True,'rank':rank,'word':word,'weight':weight,'scope':'ordinary exact arithmetic, not fresh Lean clearance; exclusions apply to constructions as described in Armario-Frau Props1.3-1.4 only'},indent=2))
print('target ledger entries unchanged',old==now,'conference check PASS')
