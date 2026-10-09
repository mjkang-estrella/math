# H040 state geometry — raw Grok report

Unaccepted proposer report; see H040-geometry-disposition.md for scope corrections.

Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h040-stategeometry-grok-20261008-r1`

Provider: grok / grok-4.7; completed.

No worthwhile H040 candidate under the collision-search state and transition-geometry lens. The missing operation is a public transition on canonical states that increases useful nonzero-coefficient collisions per paid step, or shrinks the collision set below the negation quotient, after coalescence, null relations, cycles, and detection are charged.

Verified improvement remains NONE. The working low-memory reference is still Bernstein–Lange–Schwabe negation rho. The working high-memory reference is still the H019 x-only interleaved negation baby-step giant-step schedule. This pass does not reopen the H039 fixed-table/rho hybrid, the safety-stopped H006 and H038 routes, or the consumed H034 run.

## Missing operation

A concrete walk on ordinary prime-field prime-order curves, with only the automorphism \(\{\pm 1\}\), needs all of the following:

- An explicit state set of canonical representatives, together with an explicit successor that is a public function of the current state and a public jump rule.
- Affine labels \((a,b)\) on every stored state, and a collision rule whose difference equation has a nonzero coefficient of the secret scalar.
- A per-step field cost \(C\) and a useful-collision rate \(\kappa\), in the sense of H038’s \(C/\sqrt{\kappa}\) comparison, such that the total is strictly below negation rho at the same detection budget and below x-only interleaved baby-step giant-step at the same memory.
- Coalescence: a hit must put two walks on one future trajectory, or the detector must be priced as noncoalescent storage. Fruitless cycles, null differences, restarts, lookup, and scalar verification are inside the invoice.

I do not have that successor. The constructions below are the natural ones under this lens. Each fails a specific accounting check, so none is submitted as a card.

## What was checked

**Automorphism folds stop at negation.** Bernstein–Lange–Schwabe, `negation-20110102.pdf`, “Use of group automorphisms,” state that rho can use any easily computed small-order group automorphism, and that on most elliptic curves the only such map is negation. The same paper’s Appendix A multiplicative walk does reach the negation-quotient iteration count \((1+o(1))\sqrt{\pi\ell/4}\), but a typical step multiplies by a small integer such as 7 and is much more expensive than one addition, so it loses to additive walks. Their fruitless-cycle overhead on the additive negation walk is \(1+\Theta(1/\sqrt{r})\), not a further reduction of the quotient. A second affine involution \(P\mapsto -P-B\) has orbits of size about \(q/2\), the same birthday scale as negation, and \(x(-P-B)\neq x(P)\), so canonicalization is another addition. Using it together with negation generates a translation on a prime-order group (H017, H022). That is not a larger fold.

**A conjugate side image does not add a coalescent sample.** For a walk point \(W\) and a table jump \(J\), the two slopes share the denominator \(x(W)-x(J)\). The sum of the conjugate abscissae is
\[
x(W+J)+x(W-J)=\frac{2\bigl(y(W)^2+y(J)^2\bigr)}{(x(W)-x(J))^2}-2\bigl(x(W)+x(J)\bigr),
\]
which depends on the inputs only through their abscissae, since each \(y^2\) is the public cubic. Hashing that sum, or hashing \(x(W-J)\) without moving there, is a noncoalescent side image: later distinguished points do not lie on a shared trajectory. H018–H020 already price that detector, including the loss to x-only baby-step giant-step at \(\Theta(\sqrt{q})\) memory. Choosing one of the two branches as the only successor stays on the negation quotient, so the collision set does not shrink, while the second slope and second square are extra field work. A more expensive step would need a proved rise in \(\kappa\) large enough to pay for that work. This map does not supply one.

**Subset retries and longer controller memory move the collision set the wrong way.** Forcing the walk to stay in a coordinate subset of density \(\delta\) by retrying jumps costs about \(1/\delta\) additions per accepted step. The accepted collision wait is then on a set of size about \(\delta q/2\), so total additions scale as \(\sqrt{q/\delta}\). That is the H019 residue-filter ledger, and it is worse for every \(\delta<1\). A length-\(m\) window used as the state identity enlarges the key space. A window used only to choose the next jump is another partition function for an additive walk. Larger tables already buy the \(\Theta(1/\sqrt{r})\) fruitless-cycle term in Bernstein–Lange–Schwabe. They do not shrink the quotient.

**Detection and memory are already on a priced curve.** Distinguished-point negation rho stores recoverable endpoints and pays a tail until the next distinguished point. X-only interleaved baby-step giant-step stores abscissae and indices. The H039 fixed known-log table plus a rho walk is the remaining hybrid detector, and it is a separate branch. A new detector would have to report a useful labeled collision without those records and without that tail. Packed endpoint hashes, replay buckets, and membership filters are already baseline or parked (H020, H030, H031), not a new state.

H038’s bounded-recovery-graph screen does not close this gap. It bounds short dependency graphs on a fixed explicit base with fresh uniform targets. A long rho trajectory is outside that fixed-length model, so the screen is not a reason to drop coordinate-aware walks.

## Reopen condition

Reopen this lens only with one named successor, the state set it acts on, the label update, and a full invoice in which useful collisions, nulls, cycles, and detection are separate lines. The successor has to be negation-compatible, or it has to name a different canonicalization whose cost is part of \(C\). A second sample counts only if the walk actually moves there or the stored record’s lookup cost is in the same invoice.
