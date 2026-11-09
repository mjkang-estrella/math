from pathlib import Path
import re
r=Path(__file__).resolve().parent.parent
s='import MetricTransport\n'+''.join(f'import Tree28_{i:03d}\n' for i in range(116))+'namespace Schrijver\n'
s+='def upperRoots28 : List (Fin 3185) := ['+','.join(f'Tree28_{i:03d}.root' for i in range(116))+']\n'
s+='''theorem upperTrees28 (r : Fin 3185) (hr : r ∈ upperRoots28) (v : Fin 3185) :
    ∃ p : (indexedGraph 3185 maskAt28).Walk v r, p.length ≤ 6 := by
  simp only [upperRoots28, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with '''+' | '.join('rfl' for i in range(116))+'\n'
for i in range(116):s+=f'  · obtain ⟨p, hp⟩ := Tree28_{i:03d}.sound.2 v\n    exact ⟨p, hp.trans (by decide)⟩\n'
s+='end Schrijver\n';(r/'src/UpperTrees.lean').write_text(s)
