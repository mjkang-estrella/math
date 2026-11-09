# Fresh full-scope analytic route

One complete ordinary source resolution is proposed in PROOF.md: Banić–Elezović2610.17046v1 Conjecture7.7. Exact target, dependencies and complete finite evaluation formulas are there. It is uncredited pending independent review and root decision. No Lean/manuscript work performed.

Mechanism 1: Fourier localization. Rather than fit residue limits, retain the origin expansion through order l⁻² inside the singular kernel. The pure singular term alone gives −11√3/(405π), which is **not** the conjectured constant. Two mixed terms, the next regular-kernel Taylor coefficient and regular×regular contribute at exactly the same order. Their sum is −4√3/(81π). The existing source lemma controls remainders, so this is an all-l asymptotic argument, not a finite certificate of an infinite limit. exact.py/exactchecks.json retain every expanded polynomial and exact zero discrepancy.

Mechanism 2: conditional combinatorial summation and a separate step recurrence. Conditioning on X2=y gives, for every l≥0,

    h(l)=3⁻ˡ Σ_(y=0)^l binom(l,y)
             Σ_(x=0)^(l−y) binom(l−y,x)|y−x||l−2y−x|.

The second absolute-product equals (y−x)(l−2y−x) outside the interval between y and l−2y, and its negative inside. This reduces it to full binomial moments plus truncated first/second moments. A telescoping all-order asymptotic proof through those moving cutoffs was not completed; dropping the cutoff terms loses precisely the kink correction. We instead implemented exact integer sums and independently propagated the step counts for increments (−1,0),(1,−1),(0,1). These agree exactly for every l≤30. The integer sums through l=362 match the three predicted residue limits with decreasing O(1/l) scaled residuals. This mechanism is an independent sign/normalization diagnostic, not the proof premise.

Early status/subsumption: 876 immutable original-role history references were hash-checked before the selected calculation. No exact-id or meaningful author hit for this target was found. Current arXiv author search lists Part2 as the newest author-family item; current target history lists only v1. Part1's exact random-walk mean proof and2609.20229 Thm4.1's complete **bounded-offset local** multinomial expansion were read. Neither body supplies the integrated adjacent absolute-product coefficient. Parts3–5 are mentioned prospectively in Part2; no live author-list body was located for them. Search for the exact adjacent-second-order phrase yielded no additional usable proof. This is bounded evidence only, especially with live registry routes unavailable.

Strongest objection: evaluating an explicitly identified next coefficient using the source's own saddle framework may be routine and ineligible under campaign standards. An open conjecture label does not settle that objection. The root must assess it independently; this lane asks for no count change and makes no new-to-literature guarantee.

Failed alternative geometric mechanism: near-resonant gasket cell counts can be stable at a fixed finite depth, but that does not keep infinite intersections alive or give a Frostman measure at zero displacement. The almost-everywhere difference-measure theorem does not upgrade to every nonresonant θ. No claim of a geometric refutation or new theorem was made.
