import pathlib
D=pathlib.Path(__file__).resolve().parents[1]
s=(D/'scripts/dual_min.py').read_text();a=s.index('rows={}');b=s.index('rowlist=',a)
s=s[:a]+'''rows={}
# Add full submodularity rows among nearby-orbit and sampled arbitrary pairs.
import random
rng=random.Random(198)
pairs=[]
for x in reps:
 for j in range(n):
  if not x>>j&1:
   for i in range(j):
    if not x>>i&1:pairs.append((x|1<<i,x|1<<j))
for _ in range(60000):pairs.append((rng.randrange(N),rng.randrange(N)))
for x in fam:
 for y in range(N):
  if y.bit_count()<=6:pairs.append((x,y))
for x,y in pairs:
 terms=[(x&y,1),(x|y,1),(x,-1),(y,-1)];coeff={}
 for q,c in terms:coeff[orbit[q]]=coeff.get(orbit[q],0)+c
 row=tuple(sorted((k,v) for k,v in coeff.items() if v))
 if row:rows.setdefault(row,{'kind':'submodular','terms':terms})
print('rows',len(rows),flush=True)
''' + s[b:]
s=s.replace('submod-dual-min.json','submod-dual-compressed.json');(D/'scripts/dual_compressed.py').write_text(s)
