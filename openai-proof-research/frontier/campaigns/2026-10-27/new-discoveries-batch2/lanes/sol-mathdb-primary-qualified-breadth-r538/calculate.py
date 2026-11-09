import pathlib,json
P=pathlib.Path(__file__).resolve().parent
V=[(t,i,j) for t in range(2) for i in range(5) for j in range(5)];N={v:set() for v in V}
for t,i,j in V:
 for s in [-1,1]:N[t,i,j].add((t,i,(j+s*(1 if t==0 else 2))%5))
 if t==0:
  for k in range(5):N[t,i,j].add((1,k,(i*k+j)%5));N[1,k,(i*k+j)%5].add((t,i,j))
assert all(len(N[v])==7 and v not in N[v] for v in V)
for v in V:
 for w in V:
  assert (v in N[w])==(w in N[v])
  assert len(N[v]&N[w])==(7 if v==w else 0 if w in N[v] else 1)
# On 1-perp, A^2+A-6I=0 so eigenvalues are 2,-3;
# trace and dimension give multiplicities 28,21. D=2J-2I-A.
r={'executed':'All 2500 ordered pair common-neighbor counts, 50 degree checks and symmetry checks; integer arithmetic only','vertices':50,'degree':7,'edges':175,'A_squared_identity':'A^2=6I-A+J','derived_not_numerical':'diameter2, girth5; adjacency eigenvalues 7(1),2(28),-3(21); distance eigenvalues91(1),-4(28),1(21)','delta_star':7,'minus_distance_lambda_min':4,'gap':3,'novelty':'Known source Proposition2.3; no discovery claim. Linear algebra deduction not machine-formalized.'}
(P/'bounded-calculation.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
