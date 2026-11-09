from itertools import product,combinations
from collections import Counter
from pathlib import Path
import json
R=Path(__file__).resolve().parent
def pair(p,s):return all((p[i]<p[j])==(s[i]<s[j]) and (p[i]==p[j])==(s[i]==s[j]) for i in range(len(p)) for j in range(i+1,len(p)))
def rank(s):return tuple(sorted(set(s)).index(x)+1 for x in s)
def contains(p,w):
 ss=[tuple(w[i] for i in ix) for ix in combinations(range(len(w)),len(p))]
 a=any(pair(p,s) for s in ss);b=any(rank(s)==p for s in ss)
 assert a==b
 return a
words=[w for w in product(range(1,6),repeat=5) if set(w)==set(range(1,max(w)+1))]
assert len(words)==len(set(words))==541
profiles={}
for p in [(1,1,2,2),(1,1,1,2)]:
 d=Counter(max(w) for w in words if contains(p,w));profiles[str(p)]={'contains_by_max':dict(d),'avoid':len(words)-sum(d.values())}
assert [x['avoid'] for x in profiles.values()]==[520,522]
assert sum(not contains((1,1,2),w) for w in words)==360
assert sum(not contains((1,2,2),w) for w in words)==360
assert not contains((1,1,2,2),(2,2,1,1))
assert not contains((1,1,1,2),(1,2))
(R/'independent-check.json').write_text(json.dumps({'total':len(words),'results':profiles,'controls':'112 and 122 both 360; reverse-order and insufficient-position controls passed','methods':'pairwise strict/equality comparisons and value ranks agree on every subsequence'},indent=2)+'\n')
print('PASS independent counts and controls')
