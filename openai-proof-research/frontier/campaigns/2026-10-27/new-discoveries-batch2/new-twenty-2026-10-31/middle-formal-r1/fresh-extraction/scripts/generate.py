from pathlib import Path
from itertools import combinations
L=Path(__file__).resolve().parent.parent
edges=[(0,1),(0,6),(1,6),(2,3),(2,7),(3,7),(4,6),(4,7),(5,6),(5,7),(6,7)]
adj=[{b if a==v else a for a,b in edges if v in (a,b)} for v in range(8)]
def fs(s): return '{'+', '.join(map(str,sorted(s)))+'}' if s else '∅'
sets=[set(c) for k in range(4) for c in combinations(range(8),k)]
text='import MiddleBase\nnamespace R139.MiddleOCD\nset_option maxRecDepth 4000\nset_option maxHeartbeats 2000000\n'
# one independent small certificate per subset
for i,s in enumerate(sets):
    text+=f'theorem bad_{i} : ¬ IsOCD G8 ({fs(s)} : Finset (Fin 8)) := by\n'
    missing=next((v for v in range(8) if v not in s and not(adj[v]&s)),None)
    if missing is not None:
        text+=f'  intro h\n  exact (by decide : ¬ ({missing} ∈ ({fs(s)} : Finset (Fin 8)) ∨ ∃ w ∈ ({fs(s)} : Finset (Fin 8)), G8.Adj {missing} w)) (h.1 {missing})\n'
    else:
        r=set(range(8))-s
        u=min(r); comp={u}
        while True:
            c=comp|set().union(*(adj[v]&r for v in comp))
            if c==comp: break
            comp=c
        v=min(r-comp)
        text+=f'  intro h\n  exact not_preconnected_of_closed G8 ((↑({fs(s)} : Finset (Fin 8)))ᶜ) (↑({fs(comp)} : Finset (Fin 8)))\n    (by decide) {u} {v} (by decide) (by decide) (by decide) (by decide) h.2\n'
# membership enum split in chunks for quick reduction
text+='def smallSets : List (Finset (Fin 8)) := ['+', '.join(fs(s) for s in sets)+']\n'
text+='theorem small_complete : ∀ S : Finset (Fin 8), S.card ≤ 3 → S ∈ smallSets := by decide\n'
text+='theorem ocd_G8_lower (S : Finset (Fin 8)) (h : IsOCD G8 S) : 4 ≤ S.card := by\n  by_contra hn\n  have hs := small_complete S (by omega)\n  simp only [smallSets, List.mem_cons, List.not_mem_nil, or_false] at hs\n  rcases hs with '+ ' | '.join('h' for _ in sets)+'\n'
for i in range(len(sets)):
    text+=f'  · subst S; exact bad_{i} h\n'
text+="theorem ocd'_G8_lower (S : Finset (Fin 8)) (h : IsOCD' G8 S) : 4 ≤ S.card := ocd_G8_lower S ⟨h.1, h.2.preconnected⟩\nend R139.MiddleOCD\n"
(L/'MiddleSmall.lean').write_text(text)
print('generated',len(sets),'certificates in MiddleSmall.lean')
