from pathlib import Path
root = Path(__file__).resolve().parent.parent
s = '123412534153214532413254'
w = list(map(int,s))
rows=[]
for i in range(24):
    a=[w[(i+j)%24] for j in range(4)]
    assert len(set(a))==4
    rows.append([sorted(a).index(v) for v in a])
assert len({tuple(a) for a in rows})==24
vec=lambda a:'!['+', '.join(map(str,a))+']'
(root/'src/Control.lean').write_text('''import Endpoints

namespace MathDB356266

/-- CDG (1992), Section 4, page 50: the printed 24-symbol word. -/
def w_cdg : Fin 24 → Fin 6 :=
'''+vec(w)+'''

/-- Reduced cyclic four-windows of the printed word, with ranks starting at 0. -/
def t_cdg : Fin 24 → Fin 4 → Fin 4 :=
!['''+', '.join(vec(a) for a in rows)+''']

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem cdg_euler : EulerOrdering t_cdg := by
  unfold EulerOrdering Permutation Overlaps Function.Injective
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem cdg_realizes : Realizes t_cdg w_cdg := by
  unfold Realizes
  decide

end MathDB356266
''')
