from pathlib import Path
from itertools import permutations,product
import json
D=Path(__file__).resolve().parents[1]
w=[tuple(map(int,s)) for s in '1234 2341 2413 4231 3421 3214 2134 1243 1423 4123 1342 3412 4132 1324 3142 1432 4321 4213 3241 2314 2143 2431 4312 3124'.split()]
def pairs(t):return set(zip(t,t[1:]+t[:1]))
def score(t):
 variants=[t,[tuple(5-x for x in p) for p in t]]
 variants += [[p[::-1] for p in v[::-1]] for v in variants[:]]
 return max(len(pairs(w)&pairs(v)) for v in variants)
def red(p):return tuple(1+sorted(p).index(x) for x in p)
pos='123412534153214532413254';positive=[red([int(pos[(i+j)%24]) for j in range(4)]) for i in range(24)]
labels='4231 3421 4312 4132 1324 2132 1431 4321 3213 3241 2314 2134 1231 2312 3123 1234 1243 1423'.split()
blocks=[]
for s in labels:
 p=tuple(map(int,s));bs=[q for q in permutations(range(1,5)) if all(p[a]>=p[b] or q[a]<q[b] for a in range(4) for b in range(4))]
 blocks.append([bs] if len(bs)==1 else [bs,bs[::-1]])
results=[score(sum(choice,[])) for choice in product(*blocks)]
r={'printed_1992_max_common_successor_pairs':score(positive),'figure17_expansions':len(results),'figure17_max_common_successor_pairs':max(results),'symmetries':'cyclic rotations implicit in successor sets, alphabet complement, reversal of word (reverse rows and offsets)'}
(D/'printed-comparison.json').write_text(json.dumps(r,indent=2)+'\n');print(r)
