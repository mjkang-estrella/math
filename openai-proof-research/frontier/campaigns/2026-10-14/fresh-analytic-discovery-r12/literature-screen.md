# Literature and operation screen (dated 2026-10-16)

Author: Myeongjin Kang (no affiliation). Original prose CC BY 4.0.

Reading extent is stated for every item. "Abstract only" means the claim
about that item rests on its abstract or on how other papers cite it.

| Item | Extent read | What it gives for log-concave compactly supported sources |
| --- | --- | --- |
| openai/math 374 (pinned, all build sources) | Full text | `W_2^{1/3}` only for the uniform source on a convex body; sharp on the cube. |
| Wang–Wang, arXiv:2610.09640v1 | HTML intro, Theorem 1, Prop. 4 statement, related-work paragraph (partly truncated) | `W_2` exponent `(p-1)/(4p-2)` (`1/4` at `p = infinity`) for `L^p` changes of BV densities; log-concave sources get `1/4` with polynomial dimension constants. Optimality example uses unbounded disconnected support. Cites 374 as uniform-only. |
| Mérigot, HAL hal-05616391 | Abstract | Sharp `W_1^{1/4}` for bounded compactly supported source densities. |
| Delalande–Mérigot 2023 (Thm 4.2, Prop 4.1) | As cited in 374 and Wang–Wang | `W_1^{1/6}` for densities bounded above and below on a convex body. |
| Letrouit–Mérigot, arXiv:2411.04908 | Search snippet and citations | Gluing; John domains; log-concave sources with full support; no `1/3`. |
| Letrouit, "Unstable OT maps" (CRAS 2026) | As cited in 374 | Obstruction above `1/3` for nonconvex sources; square-root conjecture (disproved by 374). |
| Ford, arXiv:2609.35574v1 | Abstract | Upper Ahlfors regular sources; `W_1`-type exponents via Mérigot's method. |
| Ruan, arXiv:2610.07577v1 | Abstract | Class-uniform conditioning moduli for `L^p` sources; improves Delalande–Mérigot and Letrouit–Mérigot; no log-concave `1/3`. |
| Divol–Niles-Weed–Pooladian, Caja-Lopez–Delgadino–Kitagawa | As cited in 374 | Constants depend on target nondegeneracy or regularity. |
| public-observatory/brenier-mass-stability (GitHub, 2026-10-13) | README | Open question: mass lower bound and square-root stability for the uniform square. Different question. |
| openai/math catalogue (CONTENTS.md) | Grep for Brenier / optimal transport / log-concave | No companion manuscript extends 374 to nonuniform sources. |

Conclusion of the screen. In the items read, the best exponent recorded for
log-concave sources with compact convex support is `1/4` (from the bounded
density results), while `1/3` is recorded only for the uniform source. The
screen is not exhaustive (abstract-level reading for several items, no
journal database search), so any novelty statement must stay at
"not found in this dated screen".

Operation comparison. The pinned proof uses uniformity in exactly three
places (see `original-scope.md`). The new operations needed are:

1. a weighted Knothe midpoint domination whose exact constant uses
   midpoint log-concavity `sqrt(f(X) f(Z)) <= f((X+Z)/2)`;
2. a weighted coordinate-slice interpolation that replaces translation
   invariance of Lebesgue measure by the monotonicity of the one-dimensional
   log-increments `t -> log g(t+h) - log g(t)`, choosing forward or backward
   differences slice by slice so that no lower density bound enters;
3. verification that the cell calculus, prescribed-mass intercepts,
   finite potential estimate, and approximation steps survive with face
   integrals weighted by a density that is only continuous on `int K`.
