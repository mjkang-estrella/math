# H035 prior-art review: accepted evidence and corrected claims

Claude Opus5.5 round1 completed/acknowledged, no pending children. Raw report:
H035-priorart-opus-raw.md. No source change or numerical run. Main ECDLP
improvement NONE; the H034 capped artifact is a separate completed diagnostic.

## Stronger shifted side-key proposal, with a probability correction

Opus proposes storing X=eta*x+r and the scaled Y, then emitting
L=X(P±J)-3r=kappa*w²-(Xi+Xj), so L=eta*x(P±J)-2r. For kappa=1,
sharing Xi+Xj gives the original6A paired kernel; center/seed keys subtract3r,
and full-point updates add3r, with those costs still charged.

For p=3 mod4 and kappa=-1, the reviewer emits -L=w²+(Xi+Xj) to avoid an
extra negation. Root rejects its assertion that the resulting multiplier is
still uniform on ALL Fp*: the chosen sign depends on eta's quadratic class.
Multiplying a nonsquare eta by -1 makes it square, while the square branch
stays square. Both classes therefore collapse to SQUARE multipliers. It is not
the identical frozen full-affine hash distribution or same-seed bucket mapping.
The uniformly random shift remains uniform after the branch-dependent sign.

The simpler corrected mechanism uses a square-only shifted isomorphism directly:
X=u²*x+r,Y=u³*y and key L=X(P±J)-3r=u²*x(P±J)-2r. Its6A SIDE-KEY count
is a valid algebraic deduction, pending independent final audit. For p=3 mod4,
the earlier ordered-pair reversal proof gives the SAME pair collision probability
as full-affine hashing. That equality does not imply identical joint output
law. The shifted model/general doubling and all center/seed/setup costs remain.
For p=1 mod4 the square-only universality objection still applies.

## Baseline conclusions must remain conditional

Raw coordinate bits cost no separate field hash multiplication, but their
collision behavior on the actual stopped key set is not thereby controlled.
Root does NOT accept the universal conclusion 'saving zero' or 'standard bits
already beat it' without the matching distribution, table-traffic and full-cost
comparison. Conversely, a folded field-operation count does NOT prove it weakly
beats every word hash. Branches, canonical representation, wider intermediates,
setup, cache/layout and finite center updates remain paid. No universal dominance
in either direction is established by the returned report.

Changing a shared kernel lowers both arms' common arithmetic price. Under fixed
other prices/Delta in the previous H034 gate, that reduces its ideal key-count
margin. Delta itself may change with the new implementation, so root qualifies
the report's unconditional 'tightens the gate' claim by those fixed-price
assumptions. No H034-specific gain follows from a shared optimization.

## Primary evidence actually checked by root

[Thorup, High Speed Hashing for Integers and Strings, v9](https://arxiv.org/pdf/1504.06804),
sections2.2 and3.4–3.5: root read the affine-family argument and vector/pair
multiply-shift construction. Theorem3.7 supplies strong universality under its
width conditions. The text explicitly distinguishes input word width from the
larger intermediate width, requiring the latter at least input width plus output
bits minus1. A d- or d/2-multiplication count cannot silently treat arbitrarily
wide output/table indices as one hardware word. These are relevant competing
hash families, not an ECDLP runtime measurement.

[Joye–Tymen, CHES2001 author copy](https://marcjoye.github.io/papers/JT01edpa.pdf),
Corollary1 and the following random-isomorphic-curve construction: root read the
explicit u²/u³ scaling and inverse. It establishes prior art for random curve
models, originally in a side-channel setting. Root did not infer that the exact
hash fusion or changed lookup guarantee is novel from its absence there.

The BLS2011 author-PDF web open returned Internal Error in this round. Its local
prior project analysis and Opus's reported pages remain identified separately;
root has not newly verified the quoted platform rates, fixed76439 multiplier
or exact canonicalization cost here. Do not transfer them as a current hardware
price or a universal recipe. Original Carter–Wegman/Dietzfelbinger papers were
not read in this round; Thorup is the directly inspected author source.

Disposition: retain corrected6A square-family mechanism for focused analysis,
not implementation. Need the matched complete-cost ledger with an explicit
competent hash competitor; no further numerical trial is admitted. Root's
corrections and native final review precede any renewed T3 round.
