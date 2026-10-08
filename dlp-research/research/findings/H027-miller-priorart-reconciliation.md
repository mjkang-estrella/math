# H027 local-coefficient construction: prior-art reconciliation

2026-10-08. Factory Opus5.5 delivered H027-miller-priorart-raw.md; root read the
retained Rück paper in full and Semaev's definitions, Lemmas1–3 and recovery.
The logarithmic-differential/Miller-coefficient technique is established prior
art. H027 has not discovered a new discrete-log attack. Its checked ordinary
q≠p trace identities remain valid constructions without a scalar decoder.

## Attribution and exact applicability

Rück, *On the discrete logarithm in the divisor class group of curves*, Math.
Comp.68 (1999),805–806, DOI10.1090/S0025-5718-99-01043-1, computes local
coefficients of logarithmic differentials by doubling in a cocycle extension.
In genus1 this is the constant coefficient used by the H027 Miller chain.
His recovery theorem concerns p-primary divisor classes in characteristic p.
The source does not assert an ordinary prime-to-p ECDLP attack. Calling H027
an adaptation of that local-coefficient method is more precise than asserting
that the paper stated every ordinary-order trace identity recorded here.

Semaev, *Evaluation of discrete logarithms in a group of p-torsion points of an
elliptic curve in characteristic p*, Math.Comp.67 (1998),353–356,
DOI10.1090/S0025-5718-98-00887-4, uses logarithmic derivative evaluation for
an additive embedding of the p-torsion subgroup. His Lemma3 evaluates it via
a short doubling recurrence. These hypotheses do not match ordinary q≠p.

In H027's explicit formula a_(Q+R)=a_Q+a_R−q*lambda(Q,R), q vanishes in Fp
when q=p, but not under the actual q≠p hypothesis. The same cheap coefficient
calculation therefore does not inherit the characteristic-p recovery theorem.
Moreover every homomorphism from a q-group to an additive p-group is zero
when q≠p. This rejects exact additive-coordinate recovery, not every nonlinear
predicate or post-processing of a_Q. The report's complex zeta, Eisenstein and
universal-extension identifications were memory-based and are not needed or
adopted as independently verified source claims here.

## Explicit small-curve correction

The report's blanket assertion that Hasse excludes q dividing p−1 is false.
For p=7 the nonsingular curve y²=x³+4 has only O,(0,2),(0,5), hence full order
q=3 dividing p−1. This is a direct finite arithmetic counterexample, not a
benchmark run or an inference about large curves.

For p≥11, Hasse does give q≥p+1−2sqrt(p)>(p−1)/2. If prime q divides p−1,
this forces q=p−1, impossible for p≥11. Thus the desired exclusion holds in
that stated regime, or can simply be imposed as a separate hypothesis.
Do not silently extend a large-field argument to all p>3.

## Multiplicative map domain and basis qualification

NEW native Sol audit COMPLETED, reading Joux–Pierrot §2.2,§3.3 and AppendixB.
Root independently read §2.2 and§3.3 from the retained primary text. Psi is a
multiplicative map on evaluable degree-zero DIVISORS admitting a principal
multiple hD with h invertible modulo |L*/K*|. Principal divisors can have
nontrivial images: Psi(div f)=f(F) modulo constants. It does not automatically
descend to Pic^0(E), hence is not thereby a homomorphism on E(Fp).

For D_Q=[Q]−[O],
`Psi(D_Q)*Psi(D_R)/Psi(D_(Q+R)) = g_(Q,R)(F) mod K*`,
and `Psi(D_Q)^q=f_Q(F)`, not necessarily1. Withdraw the raw claim that this Psi
is trivial on E(Fp). This paper concerns finite-field DLP via elliptic extension
representations, not a supplied faster ECDLP solver.
Primary: https://arxiv.org/pdf/1907.02689 .

The elementary conditional target-order fact remains: if q∤p−1 and q≠p, then
((p^q−1)/(p−1)) modq=1. In fact q divides that quotient exactly when q divides
p−1. Thus a separately constructed point-group homomorphism into this quotient
would be trivial in the former case. Here the same coprimality enables the
q-th-root evaluation on divisors; it does not force those divisor values to1.

With q≠p and q∤p−1, Frobenius on E[q] has distinct eigenvalues1,p. A Lang
preimage pi(b)−b=G≠O cannot lie in E[q], so qb≠O and CL's additional basis
condition holds. Without q∤p−1 this conclusion is unavailable. Under full prime
order with q dividing p−1, Frobenius is nonidentity unipotent on E[q], whose
image and kernel under pi−1 coincide. All preimages of nonzero G then lie in
E[q]. This can prevent the CL basis claim while leaving H027's separately proved
trace identity intact. Neither extension size nor this qualification is a
runtime lower bound for an unprovided method.

## Source access and process

Factory Opus reported full AMS papers read and Joux–Pierrot through§3.3 from
arXiv1907.02689 after eprint returned a challenge. Coombes was abstract-only;
no theorem from inaccessible full text is accepted here. Root's AMS web fetch
returned403; root instead read the already retained primary PDF text in
/tmp/h027rev/ruck.txt and semaev.txt. No attempt to bypass access restrictions.
No downloaded paper is added to the repository. Retained PDF SHA256:

- ruck.pdf: e86922d5e0efa525d4490ef81f5a0126861fefc042ec106d212a3a515c6c7dfe
- semaev.pdf: 3a869208d38e45a952c0adf90f627ab499b59c2948a08ddc5be3982ac9bffb91
- jp.pdf: 6535ba729bddd3067560db288e160efc7c02444c51dcc9faf8c95becd1c30b7d

Exact commands: cat /tmp/h027rev/ruck.txt; sed -n '65,215p'
/tmp/h027rev/semaev.txt; sha256sum /tmp/h027rev/{ruck,semaev,jp}.pdf.
The raw report, task handle and objections remain in the H027 register.

## Consequence for the research goal

No cited theorem supplies the missing nonlinear scalar signal under ordinary
prime-order hypotheses. No theorem here rules one out either. Do not run a
generic feature screen merely because the public coefficient is cheap. Reopen
recovery from it only with a specified mathematical or algorithmic premise and
full decoder cost. Other independent H027 proposals remain live. Best supported
ordinary complete work stays square-root; verified improvement NONE.
