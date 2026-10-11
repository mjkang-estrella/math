# I193 parent disposition: pairing symmetry and composition pass; short-gap exchange open at J193

2026-10-11. **Short-gap exchange: UNRESOLVED at J193. The
complementary-pairing symmetry, the central-square composition
identities, and the conditional sufficient subcases PASS at their
stated scopes. Eight accepted, two remaining.** The E183 line and the
local-ear mechanism remain parked. No substantial finding is
nominated.

First dispatch for this brief on the current provider driver
([task archive](iteration193-equality-bridge-task.json)); completed
without interruption with detached hashes for exactly the five assigned
files and no other writes.

## Written proof review

The parent read all five outputs in full. Finite claims were
independently re-derived on exact instances (below); structural
arguments were checked in prose without substantive repairs.

**Equality restatement (§1).** The short-gap reduction (bijections,
$U=V+Z$, $b=r+2z\bmod W'$, $D_G=W'+\langle r\rangle$ in the equality
case, $\eta=0\iff\lambda=-1/2$, anchor independence of $\lambda$) is a
faithful restatement of the parent-reviewed I192 deductions. Verified.

**Manuscript scope (§2).** The continuous reading of lines 60–837 and
the negative conclusions — the cancellation/circulation argument
chooses special weights and proves nothing about the quotient
functional $w$; the Pfaffian orientation parity applies to both even
components of $F_Q$ but constrains orientation signs, not $w$; the P4
corollary supplies existence, not spans — are correctly scoped and
match the parent's own reading record. Verified.

**Complementary-pairing symmetry (§3).** The $A/B/T$ partition (every
Hamiltonian cycle uses exactly two opposite or three square edges), the
functional identity $g=-\sigma$ with $g(C-C^*)=1_A+1_B$, the codimension
equality (6), and the coefficient equality $\alpha_B=\alpha_A$ (7) are
correct; the parent verified the algebra and confirmed (7) numerically
on the prism family: both pairings of a lateral square give
$\alpha=-(m-3)/(m-2)$, i.e. $\lambda=1/(m-2)$, for $m\in\{4,6,8\}$,
computed via exact rational quotient functionals from freshly
enumerated cycle families. On the cube the parent also verified the
partition sizes ($|A|=|B|=1$, $|T|=4$, all four three-edge patterns
realized, every cycle using two or three square edges). The negative
conclusion — the symmetry reproduces the same forbidden coefficient
rather than excluding it — is correct. Verified.

**Central-square composition (§4).** The lift pattern analysis (the
second step's lost family is exactly the original $D_{11}$ fibre), the
relation structure (8), the unconditional identity
$\Delta_c=\eta_{first}$ (9), the transport identity (10), the
coefficient transport $\lambda_c=\lambda/(1+2\lambda)$ (11), and the
conditional recovery $d(H)=d(G)+1$, $d(J)=d(G)+4$ after a hypothetical
failure (12) are all correct; the parent verified (9)–(11) and the
fibre bijection on the cube rung step by direct enumeration and exact
rational ranks: $d(G)=5$, $d(H)=7$, the lost central family equals the
lift of the unique $D_{11}$ element, $\Delta_c=1=\eta$,
$\lambda_c=1/4=\lambda/(1+2\lambda)$ for $\lambda=1/2$, and the
twice-expanded graph $J$ has $d(J)=9=d(H)+2$ by direct enumeration of
its Hamiltonian cycles. The honest conclusion — the recovery is a
compensation, not a contradiction — is correct. Verified.

**Sufficient subcases (§5).** The impossibility of an exact convex
representation of a disconnected two-factor (support containment
forces equality), the alternating-cycle decomposition (13) with the
conditional single-flip nonnegativity, the integer-span sufficient
condition, and the lattice formulation (14) — failure requires
$2k=-m$ in the primitive quotient, so odd $m$ excludes it — are
correct elementary arguments. The prism values $\lambda=1/(m-2)$
(parent-verified: $1/2,1/4,1/6$) show even $m$ and fractional positive
values occur, so neither lattice parity nor integrality can settle the
target universally; the child records this honestly. The brace
matching-decomposition gap (§5.4) is correctly identified as a missing
connectivity/weight step, not an error. Verified.

**Remaining assertion (§6).** J193 — in every short-gap equality case
with $F_Q-C_0\in D_G$, $w(F_Q-C_0)\ne-1/2$ — is exactly equivalent to
the short-gap exchange theorem after the settled branches; the
counterexample accounting (no failing step in the retained 636 steps;
no new graph offered) is inherited finite evidence, correctly not
rerun. Verdict UNRESOLVED is honest. The long-gap front of J192 was
correctly left closed per the brief.

## Limits that remain binding

The short-gap exchange theorem remains UNRESOLVED at J193; the
universal exchange residual J192 (both long-gap clauses) remains open;
no Q164 consequence in either sense. The failure coefficient $-1/2$ is
unexcluded even for quadrilaterals. Paid sufficient conditions:
$\lambda$ positive on all verified instances; $\lambda\ne-1/2$ when the
single-flip Hamiltonicity hypothesis holds, when $z$ is integrally
spanned, or when the primitive lattice value $m$ is odd. The I193
record is unsealed.

## Authentication and independent checks

The [validator](../experiments/i193-parent-validate.py) authenticates
all five detached outputs, exact five-file membership, the five
required anchors and all fifteen input records, and the archive write
scope, and re-authenticates the I192–I183 chain. The
[verification receipt](../experiments/i193-parent-verification.json)
passes: pairing symmetry on $m\in\{4,6,8\}$ via exact rational quotient
functionals; the cube $A/B/T$ partition; the central composition on the
cube rung step ($d(G)=5\to d(H)=7\to d(J)=9$, lost fibre $=$ $D_{11}$
lift, $\Delta_c=\eta=1$, $\lambda_c=1/4$); and the inherited 23-stage
sealed replay in **8.542 seconds** with empty stderr. Four parent-script
defects (back-substitution order, mixed-type vertex ordering, a weak
partition assertion, a hardcoded $\eta$ now sourced from the verified
I192 receipt) were caught and fixed; the child's mathematics needed no
repair. All other arguments are prose-reviewed as written. Neither
acceptance gate is lowered.

## Next bounded step

[I194](iteration194-quotient-sign-brief.md) attacks the sharp residue
of J193: the sign of the quotient functional on the canonical
two-factor. Prove $w(F_Q-C_0)\ge0$ universally (which implies J193,
since $-1/2<0$), exhibit a fully specified step with negative value
(a decisive structural datum), or isolate the exact obstruction; the
paid sufficient conditions (single-flip Hamiltonicity, integer span,
odd lattice index) are the levers to extend. An explicit stopping rule
applies: on another UNRESOLVED without a decisive new constraint, the
short-gap front parks beside E183 and the program reconsiders the
remaining surfaces (long-gap J192, the count bound, (T)). The
five-file policy and both acceptance gates remain unchanged.
