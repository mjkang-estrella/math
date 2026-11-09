# Generates lean/V3Config355701.lean for the 9_3 counterexample to MathDB 355701.
import itertools
LINES=[[0,2,3],[2,4,5],[3,5,8],[2,7,8],[1,3,6],[0,6,8],[0,1,4],[4,6,7],[1,5,7]]
S=[set(l) for l in LINES]
def lt(a,b): return [i for i,l in enumerate(S) if a in l and b in l]
tris=[]
for a,b,c in itertools.combinations(range(9),3):
    l1,l2,l3=lt(a,b),lt(b,c),lt(a,c)
    if l1 and l2 and l3 and c not in S[l1[0]] and a not in S[l2[0]] and b not in S[l3[0]]:
        tris.append((a,b,c,l1[0],l2[0],l3[0]))
assert len(tris)==21
# a maximum mutually intersecting set of size 4
best=None
for k in range(9,0,-1):
    for T in itertools.combinations(range(9),k):
        if all(S[i]&S[j] for i,j in itertools.combinations(T,2)): best=T; break
    if best: break
assert len(best)==4
fs=lambda l:'{'+', '.join(map(str,l))+'}'
Lfun='\n'.join(f'  | {i} => {fs(l)}' for i,l in enumerate(LINES))
trilist=', '.join(f'({a}, {b}, {c}, {x}, {y}, {z})' for a,b,c,x,y,z in tris)

MATCH='\n'.join((f'  | {i} => ' if i<8 else '  | _ => ')+' || '.join(f'p.val == {p}' for p in l) for i,l in enumerate(LINES))
import pathlib
out=pathlib.Path(__file__).with_name('v3_template.lean').read_text()
out=out.replace('MATCHLINES',MATCH).replace('TRILIST',trilist)
out=out.replace('L i = LSPEC','L i = ([' + ', '.join(fs(l) for l in LINES) + '] : List (Finset (Fin 9))).getD i.val ∅')
open('lean/V3Config355701.lean','w').write(out); print('ok',best,len(tris))
