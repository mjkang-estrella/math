import itertools,json
from pathlib import Path
P=Path(__file__).resolve().parent
n=7
perms=[(0,)+p for p in itertools.permutations(range(1,n))]
counts=[0]*43
# Direct square construction and literal vertical comparisons; no difference profiles.
for sig in perms:
 rows=[tuple(sig[(r+c)%n] for c in range(n)) for r in range(n)]
 for p in perms:
  s=sum(rows[p[i]][c]<rows[p[i+1]][c] for i in range(n-1) for c in range(n))
  counts[s]+=1
assert counts==json.loads((P/'routes-n7.json').read_text())['cyclic_row_symbol_orbit_scaled_counts']
full=json.loads((P/'checks-n6.json').read_text())['first_row_normalized_counts']
assert full[9]**2-full[8]*full[10]==-94443
# A completely separate cell-by-cell Latin enumeration at orders <=5.
def cells(n):
 a=[[0]*n for _ in range(n)];rm=[0]*n;cm=[0]*n;out=[0]*(n*(n-1)+1)
 for j in range(n):a[0][j]=j;rm[0]|=1<<j;cm[j]|=1<<j
 def rec(pos,s):
  if pos==n*n:out[s]+=1;return
  i,j=divmod(pos,n)
  avail=((1<<n)-1)&~(rm[i]|cm[j])
  while avail:
   b=avail&-avail;avail-=b;x=b.bit_length()-1;a[i][j]=x
   rm[i]|=b;cm[j]|=b
   rec(pos+1,s+(a[i-1][j]<x))
   rm[i]^=b;cm[j]^=b
 rec(n,0);return out
small={}
for n in (3,4,5):
 c=cells(n)
 assert c==json.loads((P/f'checks-n{n}.json').read_text())['first_row_normalized_counts']
 small[n]=c
out=dict(direct_order7_orbit_agrees=True,small_independent_cell_counts=small,order6_log_concavity_deficit_at9=-94443)
(P/'independent.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
