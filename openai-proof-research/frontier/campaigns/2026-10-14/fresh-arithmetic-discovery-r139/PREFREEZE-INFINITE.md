# Prefreeze feasibility: countable rank at fixed ramification four

No theorem is frozen in this file. This records a candidate bridge before author-proof development.

Let k0=F_(5^8), let D be X^4+Y^4+Z^4=0, and let h:D→E, s=X/Y,w=Z²/Y², E:w²=s⁴+1, with a rational branch point o as origin. Let k be the perfect closure of the union k0(D^m) under generic-coordinate inclusions. Its countably many generic D-points P_i map to Q_i=h(P_i)-o. The connected étale Verschiebung cover of ordinary E has degree five; a nonzero combination of the Q_i pulls it back to a nontrivial cover, as is seen by fixing all but one coordinate at a point mapping to o. The remaining map has degree 2a² prime to five. Adding generic factors and taking perfect closure preserve this nontriviality. Thus Q_i are independent in E(k)/5.

Use V=W(k), A=(V[x,y]/(5+x⁴+y⁴))_(5,x,y), ord_m(5)=4. Base-change the source integral K5 class in O0 to O=V[t]/(t⁴+5); this avoids falsely invoking K4(k)=0. Lift each P_i by smooth Hensel lifting, obtain its horizontal divisor A→O, and push this common class to γ_i∈K5(A), each generically zero. The source four-conjugate orbit would detect 4Q_i.

Unpaid bridge at time of this note: source specialization uses full Bott isomorphisms under low cohomological dimension, which is absent for k. A possible substitute only needs low motivic weights. For K6(J;5), weights begin at 3: weight 3 is H0(J,μ5³), represented by β³; weight 4 is H2(J,μ5⁴), represented by β² times integral K2 modulo five by norm residue. For K5(E;5), weight 3 is H1(E,μ5³), represented by β²K1. If the residue lowers the filtration by one, then after removing β³ and β²z an arbitrary K6 boundary has residues in weight ≥4 and cannot affect the prescribed weight-3 K5 residues. This would give exactly the tame-symbol congruences required by the source surface d1²=0 operation, without full Bott invertibility.

Need actual primary filtered-localization/purity compatibility, convergence, and coefficient-product checks before freezing. There is no claim here of completion, contribution grade, or acceptance. The finite-field amplification in DERIVATIONS.md is already a source/classical composition and is not promoted by this note.

## Later prefreeze corrections and strongest-payment check

The first paragraph above used a wrong sign in the model: the source and the construction use D: X⁴+Y⁴=Z⁴. The formula h(s,w)=(X/Y,Z²/Y²) is for that equation. The affine local ring 5+x⁴+y⁴=0 and substitution x=tX,y=tY,t⁴=−5 are unchanged. This correction occurred before any freeze.

The finite-weight bridge has now been compared with Levine’s actual localization and purity operations (niveau §6.7 Proposition6.8; coniveau Corollary3.2.2 and Proposition4.2.2). It appears to close the abstract boundary reduction, but a stronger classical reduction may render it unnecessary for this candidate: a mixed-characteristic complete discretely valued field with perfect characteristic-five residue field has 5-cohomological dimension at most two. The source’s full Bott operations would then remain applicable to L and J, despite infinite transcendence degree of the residue field. This is under primary verification; no absence-of-cd-bound assertion from the earlier note should be used.

## End of the prefreeze investigation

DERIVATIONS.md §§3–4 now records the low-weight calculation and the full countable-rank construction using it. This avoids depending on the unauthenticated classical cohomological-dimension shortcut. The construction is retained as a source/primary composition; it is not a frozen discovery nominee. The earlier paragraphs are chronology, with the sign and cohomological-dimension corrections explicitly preserved. FINAL.md and UNRESOLVED.md give the disposition and exact limits.
