"""Create reviewer negative controls, each a modified copy of the literal module in its own dir.
Usage: python3 -I make_controls.py SRC_LEAN OUTDIR"""
import sys, os
src, out = sys.argv[1], sys.argv[2]
s = open(src, encoding="utf-8").read()
def put(name, t):
    d = os.path.join(out, name); os.makedirs(d, exist_ok=True)
    assert t != s, name
    open(os.path.join(d, "MathDB378395.lean"), "x", encoding="utf-8").write(t)
# 1. perturbed certificate: b[1][0] = -2 makes w_{1,j,0} negative somewhere
old = "![![0, 0, 0, 0, 0], ![-1, 0, 0, 0, 0], ![-1, -1, -1, 0, 0], ![0, -1, 0, -1, 0]]\n    ![![1, 1, 1, 1, 0]"
assert s.count(old) == 1
put("neg-perturbed-b10", s.replace(old, old.replace("![-1, 0, 0, 0, 0], ![-1, -1", "![-2, 0, 0, 0, 0], ![-1, -1", 1)))
# 2. weakened target: conjecture asks collapsing to (p,q,r) itself; identity makes it true, refutation must break
old2 = "      ObtainedByCollapsing p q r p q q F"
assert s.count(old2) == 1
put("neg-target-pqr", s.replace(old2, "      ObtainedByCollapsing p q r p q r F"))
# 3. sorry injected into slices_distinct
old3 = "∃ i : Fin 4, ∃ j : Fin 4, ¬ (onCol ellZ (i, j, k) = 0 ↔ onCol ellZ (i, j, l) = 0) := by\n  decide +kernel"
assert s.count(old3) == 1
put("neg-sorry", s.replace(old3, old3.replace("decide +kernel", "sorry")))
# 4. make slices k=3 and k=4 share a pattern claim: replace c[3][3]=1 by 0 changes weights of slice 3
old4 = "![![1, 1, 1, 1, 0], ![1, 1, 1, 0, 0], ![1, 0, 0, 0, 0], ![0, 1, 0, 1, 0]]"
assert s.count(old4) == 1
put("neg-perturbed-c33", s.replace(old4, "![![1, 1, 1, 1, 0], ![1, 1, 1, 0, 0], ![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0]]"))
# 5. added axiom used by endpoint
old5 = "theorem collapsing_conjecture_false : ¬ CollapsingConjecture := by\n  intro h"
assert s.count(old5) == 1
put("neg-axiom", s.replace(old5, "axiom cheat : False\ntheorem collapsing_conjecture_false : ¬ CollapsingConjecture := by\n  exact cheat.elim\n  intro h"))
print("ok")
