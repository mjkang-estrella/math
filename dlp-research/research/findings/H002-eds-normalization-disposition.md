# H002 A1 normalization and bounded diagnostic gate

Root and independent Claude Opus round2 derive the same correction. With W_P(n)
the normalized division-polynomial sequence, prime subgroup order q>3,
gcd(q,p−1)=1, define phi(R)=(W_R(p−1)/W_R(p−1+q))^(1/q² mod(p−1)). For q∤n,

`phi(nP)=phi(P)^(n²)*W_P(n)` and `chi(W_P(n))=chi(phi(nP))*c^n`, c=chi(phi(P)).

Derivation: use W_(nP)(l) W_P(n)^(l²)=W_(lP)(n) W_P(l)^(n²) at l=p−1 and
l'=l+q. Their right-hand point arguments coincide. The ratio yields
phi(nP)^(q²)=phi(P)^(q² n²) W_P(n)^(l'²−l²). Invert q² modulo p−1;
l'²−l²≡q² there, giving the displayed formula. Ratios are nonzero under the
stated hypotheses. For n=1 the older n²−1 expression incorrectly forces phi(P)=1.
Dividing the pointwise phi(nP) by phi(P) produces the normalized n²−1 sequence.

The [Lauter–Stange preprint](https://arxiv.org/pdf/0803.0728), definition3/equation4,
prints n²−1 for pointwise phi; root inspected its actual page and the reviewer
confirmed the inconsistency. No published erratum or SAC-version correction has
been verified. We use the independent derivation, not presumed authority of the
printed exponent. This is a normalization correction, not an ECDLP improvement.

With c=−1 and nonnegative integer offsets A, excluding all identity windows,
G_A(kP)=∏_a chi(phi((k+a)P))=(-1)^(|A|k+Σa)∏_a chi(W_P(k+a)). Correlation with
minimal-residue parity equals the average of this expression times(-1)^k.
Use the unwrapped W indices, whose character sequence is antiperiodic of period q.
Even-size A gives a twisted correlation; it is NOT universally zero. c=+1 also
does not mean a computable coordinate predicate has no information. Correlation
is twice binary prediction advantage. No epsilon^(-2) noisy reconstruction has
been established; wraparound and correlated windows must be handled explicitly.

## Evidence, failure and next test

Round2 reviewer scratch `/tmp/a1check/chk.py` reports the corrected identity on
p13:(a,b,q,P)=(2,4,17,(0,2)) and p19:(2,9,23,(0,16)); the old formula fails.
Root inspected code but has NOT independently rerun this scratch experiment.
Its reported4100 recurrence steps hide field arithmetic: the reviewer admits
low tens of thousands of field multiplications, exceeding the explicit10000
arithmetic-event brief. This is a budget violation, not a compliant experiment;
exact costs were not measured. Retain it only as unreviewed supporting evidence.
Also correct the raw report's 'free' labels: generating known multiples costs work.

Native Sol `/root/small_curve` is implementing a separate diagnostic, with sole
ownership of research/experiments/H002/eds_diagnostic.py and eds_protocol.md.
Only implementation/syntax checks are authorized before independent review.
It must count actual field operations (including exponent/inversion internals),
use declared fixtures/seeds/offsets, preserve signs and exclusion mass, and stop
at global1M instrumented events or60s with explicit partial status. Pointwise phi
is computed independently of the identity under test. Exhaustive labelled tables
are diagnostic work, never free solver advice. Both odd/even offset families and
shuffled labels are included; selecting the best observed correlation is not a
generalizing predictor. No experiment results exist from this implementation yet.

Task provenance: `ecdloop-h002-eds-math-review-20261008-r1` and new independent
round `ecdloop-h002-eds-math-review-20261008-r2`, provider claudeAgent/model
claude-opus-5-5. Full task IDs in the register; raw round reports retained.
Status: focused derivation accepted for diagnostic design, implementation/reproduction
pending; no Lean theorem, solver or complexity improvement claimed.
