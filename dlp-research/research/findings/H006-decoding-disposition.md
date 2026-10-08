# H006 decoding: corrected yield claim, no demonstrated gain

Factory Fable report H006-decoding-fable-raw.md is retained, not accepted wholesale.
Root found a concrete counterexample to its strongest yield assertion; native
Astra /root/h007_lattice_carries independently checked it. Paper only, no trials.
No new Lean theorem or ECDLP improvement.

## Counterexample to blanket no-constant-success assertion

Full odd prime group order n>=7 overFp. Choose a!=O and evaluation set
D=E(Fp) minus{O,a}; N=n-2. SumD=-a. For t=N-1=n-3,d=t-1=n-4,e1, exactly one
t-subset sumsO: T=E(Fp) minus{O,a,-a}. Indeed each subset removes oneP fromD
and its sum is-a-P, zero iffP=-a.

The Fp-rational divisor sum_(P inT)(P)-t(O) is principal, giving h inFp(E)
with exactly those simple zeros and poleorder t. Riemann-Roch givesdim
L(tO)/L((t-1)O)=1. For EVERY g inL(tO) outsideL((t-1)O), unique nonzero c
cancels its leading pole, so f=g-c*h liesinL(dO) and agrees exactlyatT.
Any other output with at leastt agreements would have the samezero divisor
and leading coefficient, hence equal f. Vanishing-subset success isone.

GS asymptotic interpolation margin t²-dN=1>0. Sufficient multiplicity is
permitted by the blanket claim, but may be extremely costly. This is NOT a
small-decoder-parameter claim. If d must be divisibleby3, restrictn≡1mod3.
Construction/reading alreadyOmega(n); this gives no fasterDLP or guarantee of
an informative target coefficient. A theorem explicitly requiringN=o(n) or
smallmultiplicity would need separate analysis.

Consequences: distinct-point sampling is not iid scalar sampling. The raw
exact1/n subset probability and unconditional yield equality are false in this
model. Also E[count]>=1 is not necessary for constant success probability:
any fixed positive success probability gives only a corresponding expectation
lower bound. The raw entropy/repetition conclusions are NOT accepted as a
universal cost theorem. Decoder algorithm upper bounds cannot be silently used
as lower bounds on every possible decoder.

## Translation-folded construction and speculative repair

The robust construction objection remains: translation by nonzero T sends
L(dO) toL(d(-T)), so it does not preserve the stated one-point message space.
Partial translation blocks are not fullorbits; a decodedzero set need not be
an exact unionofblocks. The named folded-code theorems cannot be imported
without the required invariant space and algebraic compatibility.

Do not turn that obstacle into universal claims about all folded/shifted codes,
or equate everypossible fixed-O code-folding gain with known rho constants.
Raw costlowerbounds and unknown-log/extension assertions require their exact
hypotheses. No blanket ECDLP impossibility accepted.

Fable suggests interpolating a linear difference equation among translated
spaces, then searching its affine solution space. It supplies no proven general
small-dimension bound or cheap useful-output selection. A dimension-only toy
experiment would not address that full-cost gap; none authorized. Reopening
requires an actual compatible decoder and charged pruning mechanism.

Primary sources inspected by Fable (not all independently re-read by root):
https://people.csail.mit.edu/madhu/papers/1998/venkat-journ.pdf
https://arxiv.org/abs/0811.4139
https://arxiv.org/abs/1204.4209
https://arxiv.org/html/cs/0507026

Status: named mechanisms provide no accepted improvement. Corrected exceptions
are durable; theorem-like raw exclusions remain unproved. Main work proceeds to
concrete H007 algebraic and carry-circuit candidates, rather than extending this
negative result into general decoder infrastructure.
