import itertools,json,sys
from pathlib import Path
P=Path(__file__).resolve().parent
n=int(sys.argv[1]);assert 4<=n<=7
perms=[(0,)+p for p in itertools.permutations(range(1,n))]
profiles={}
for p in perms:
 d=tuple(sum((p[i+1]-p[i])%n==a for i in range(n-1)) for a in range(1,n))
 profiles[d]=profiles.get(d,0)+1
counts=[0]*(n*(n-1)+1)
for s in perms:
 w=[sum(s[x]<s[(x+d)%n] for x in range(n)) for d in range(1,n)]
 for profile,mul in profiles.items():counts[sum(a*b for a,b in zip(w,profile))]+=mul
assert sum(counts)==len(perms)**2
assert counts==counts[::-1]
# This is an orbit with constant positive multiplicity, hence shape equals its distinct-square distribution.
lo=n+1;hi=(n-1)**2-2
valleys=[(i,counts[i-1:i+2]) for i in range(lo+1,hi) if counts[i]<min(counts[i-1],counts[i+1])]
nonlc=[(i,counts[i]**2-counts[i-1]*counts[i+1]) for i in range(lo+1,hi) if counts[i]**2<counts[i-1]*counts[i+1]]
rows=dict(n=n,cyclic_row_symbol_orbit_scaled_counts=counts,profiles=len(profiles),strict_valleys=valleys,negative_log_concavity_deficits=nonlc)
(P/f'routes-n{n}.json').write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps(rows))
