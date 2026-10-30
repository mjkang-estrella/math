# r39: third-order Stirling subset half-plane question — incomplete

No full result. Credit 0; no PROOF.md, Lean, paper, nomination, acceptance, or count change. Solo; assigned-lane writes only. Root alone decides acceptance/counts.

## Fresh-source screen

1. **Deb–Sokal, arXiv2507.18959v1, Conjecture7.7, p45 — selected.** Literal all-row half-plane assertion with accessible definitions and an exact second-order differential recurrence. Plausible complete route: prove preservation of a Hurwitz/interlacing invariant. The source has only v1 in current arXiv metadata; latest unversioned PDF and v1 PDF are byte-identical. No journal reference/DOI is advertised in that metadata, and the bounded title search found no journal version; this is not a worldwide assertion of unpublished status. Actual source pp5–7,9–12,38–45 read; p45 rendered and inspected. Companion Conjecture7.5 is for cycle polynomials and is a separate unsolved assertion, not a second nomination.
2. **Altizio, arXiv2511.03847v1, Conjecture1, pp1–3 and Section6.** All nonzero Stern polynomials defined by S0=0,S1=1,S(2n)=xS(n),S(2n+1)=S(n)+S(n+1) have zeros Re(z)<1. Current source proves disk |z-2|<=1 zero-free and prime-index irreducibility, not the full half-plane. Section6 explicitly explains why its parabolic continued-fraction criterion fails at 1+2.5i. No credible complete invariant was obtained from the two Möbius updates, so screened out. The stronger geometric-sum bound in Remark3 is a helper and is not eligible. No numerical Stern search undertaken.
3. **Bridges–Craig–Folsom–Rolen, published SIGMA21(2025)026, Claim3.2 p10.** For both b=0,1 and every n, coefficients in q of sum_m q^(m²+bm)w^m/(q;q)_m have zeros Re(w)<=0, with imaginary parts tending to zero asymptotically. Published full body read pp9–12, especially definition/Claim3.2, rather than abstract. The full asymptotic zero-attractor assertion is substantially stronger than finite stability, and no uniform tail-zero control was identified; not selected for bounded probing. Broad Problem3.1 is not reduced to parameter examples. The current 2026 Heim–Neuhauser search lead concerns Nekrasov–Okounkov polynomials, a distinct object; no abstract-based exclusion is asserted.

These are fresh relative to the searched r-lane summaries and read batch exclusions; not certified globally new. The elliptic Bernoulli root exclusion and r38 obstructions were read and not revisited.

## Exact selected statement

Let A(N,k) count partitions of an N-element labelled set into k blocks of size at least3. Define a(n,k)=A(n+2k,k) and

s_n(x)=sum_(k=0)^n a(n,k)x^k.

This is exactly source(1.4),(1.18) at r3. Source Lemma1.1(b), Eq1.14 gives

a(0,k)=delta(k,0), a(n,0)=0 (n>=1),
a(n,k)=binom(n+2k-1,2)a(n-1,k-1)+k a(n-1,k).

Conjecture7.7: **for every integer n>=0 and every complex z, s_n(z)=0 implies Re(z)<=0.** The source says “left-half plane”; since s_n(0)=0 for n>=1, strict negativity for all roots would contradict the source's own explicitly acknowledged zero. The substantive intended question includes that zero; no endpoint correction is proposed or counted. A stronger sufficient endpoint is all roots of q_n=s_n/x strictly left for n>=1. s_0=1 has no roots. q_1=1.

Initial rows s1=x, s2=x+10x², s3=x+35x²+280x³ agree with the primary source and registry body.

## Current proof-registry and closest-body comparisons

Before sustained investment refreshed all five named heads by public HTTP. Omega dev616c4a3b8dc320665d3645c8da9f5f8ae72981f7, commit2026-10-29T12:32:13Z; main d7af67136d4478875778ac6e75eb5fbb8b3693a5; OpenAI7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a; AIM8729eab98bafe409b66c5e39253bf56569a62327; Countdbf673741a54c7dc9d88a6aec0e8148a538f4a3a. All unchanged versus r38, so no commit delta to retrieve. Copied r38 complete D5(12543 entries) and Problems(1551 entries) trees; inherited complete AIM3541, Count183, OpenAI preprints13578-entry scopes also copied. No whole-dev completeness claim. Old capped compare is not used for absence. Filename matching only; differently named subsumers remain possible. Current MathDB369483 full HTML has no posted solution; its empty state is NOT novelty evidence.

The broader author-name screen found and fetched **D5/S0/Certificates/DebSokalConjectureFourRefutation.lean** at the refreshed immutable dev head. Entire4948-byte body read. It refutes the printed non-real-zero clause Conj1.4(c) at r3,n3, explicitly attributing that observation to Deb2023 thesis. It does not refute or prove Conj7.7; real roots of s3 are perfectly compatible with half-plane stability. No external kernel replay claimed. No novelty claim for this public endpoint repair.

Actual closest primary bodies:

* **Chen–Wang2610.09362**, current metadata/paper fetched. Theorem3.1 p15 establishes row log-concavity for both triangles r3..5 (and eventual r6 subset). Section3 pp15–33 supplies coefficient induction; Section4 Theorem4.2 pp34–37 proves nonreal zeros for s3,n, n>=4. These concern coefficient log-concavity and non-reality, neither of which locates complex roots in the left half-plane. No full half-plane theorem occurs in the read theorem bodies. This is genuine current followup, not ignored by relying on the2025 source alone.
* **Ding–Zhu2106.12176**, Section2.3 pp11–14, Theorems2.14/2.15 and proof read. The preservation criterion is for first-order operators (alpha*x²+beta*x+gamma)I+(mu*x³+phi*x)d/dx, with stated sign/degree restrictions. The selected recurrence has a nonzero second derivative, and no valid factorization into eligible preserving operators was proved. Proposition2.16 concerns alternating-run polynomials of a dual Stirling-permutation set, not s3,n.
* **Shi2610.35783**, pp1–3 definitions(1),(2), Theorems1.1/1.2 and proof setup. This very recent body proves weak Hurwitz stability of extended Turán expressions of Stirling–Whitney–Riordan polynomials and reflected Laguerre polynomials. Its source sequence has a first-order derivative recurrence with constant parameters; its output is a bilinear Turán sum, not s3,n. No representation of s3,n as that output has been established. Similar vocabulary is not theorem subsumption.

Search queries/timestamps, HTTP source bytes and failures are recorded. Crossref attempt with unsupported arxiv filter returned400; no bypass or retry. No403/429/challenge occurred in this lane. No universal novelty PASS is claimed.

## Full-route attempt: differential recurrence

Writing D=x*d/dx, source Eq1.14 implies

s_n=x[2D²+(2n+1)D+n(n+1)/2]s_(n-1)+D s_(n-1).

Removing the known zero and setting c_n=(n+2)(n+3)/2 gives

q_n=T_n(q_(n-1)),
T_n(q)=2x³q''+[(2n+7)x²+x]q'+(c_n*x+1)q.

The coefficient formula for T_n is independently checked against the triangular recurrence and the direct associated-partition recurrence

A(N,k)=k A(N-1,k)+binom(N-1,2) A(N-3,k-1).

A complete induction would follow if T_n preserved an appropriate class containing q_(n-1). Plain real Hurwitz stability, even with positive coefficients and the exact degree n-2, is insufficient:

n=6, q=(x²+x/100+1)²,
T6(q)=136x5+(71/10)x4+(780439/5000)x3+(71003/10000)x2+(901/25)x+1.

All roots of q have real part -1/200. In descending-coefficient Hurwitz convention the output leading principal determinants are

Delta1=71/10,
Delta2=7129129/50000,
Delta3=80601346387/500000000,
Delta4=Delta5=-1767902286863/12500000000.

Thus this output is not strictly Hurwitz. Exact Routh first-column entries, independently obtained without determinant expansion, give a negative entry too. This defeats the proposed general preservation theorem. **It is not a counterexample to the source:** q is not q5, and this q has non-log-concave coefficients. Actual source row log-concavity from Chen–Wang remains additional potentially useful structure.

A bounded exact supplementary search tested1600 products of positive stable real quadratics/linear factors with matching degree;759 had log-concave coefficients. None of those759 images failed the exact Routh check. This neither proves that the intersection is invariant nor justifies treating it as a theorem. No induction on n based on those probes is valid.

## Second route: coupled Hermite–Biehler system

Write q_(n-1)(x)=E(x²)+x O(x²), with derivatives below in t. The exact parity split is

E_new=E+2tE'+(c_n+2n+7)t O+(4n+26)t²O'+8t³O'',
O_new=2O+2tO'+c_n E+(4n+18)tE'+8t²E''.

The symbolic identity was checked independently on generic degree8 input with free coefficients. A plausible all-order proof would establish negative real-rootedness and the correctly oriented interlacing of each actual E/O pair (with the appropriate boundary/degree cases) under this coupled update. The general stability obstruction above shows that arbitrary admissible Hermite–Biehler pairs cannot be sufficient. I did not find additional derivative-ratio or coefficient inequalities that are both preserved by this system and strong enough to force interlacing. Row log-concavity alone has no such implication: 1+x+...+x4 is log-concave and has roots of positive real part. Combining it with a previous-step Hurwitz hypothesis might help, but no preservation proof was obtained.

**Exact remaining mathematical gap:** a preserved all-n invariant for the actual q_n, or a global root-exclusion representation of s_n, or one exact source counterexample. Neither finite root location nor generic-operator failure supplies it.

## Diagnostics, adversarial case, falsifier

`bash run-checks.sh` PASS: all source rows through35 agree between two independent combinatorial recurrences; exact rational Routh columns are strictly positive for q1..q35. Separate SymPy Bareiss determinants reproduce the operator obstruction; separate symbolic differentiation verifies the coupled parity identity. Hard512MiB address-space, finiteCPU/alarm/wall limits, BLAS1 for every script. These are diagnostics, no new theorem. The Routh implementation stops on the first nonpositive pivot and makes no stability inference from such an event without independent analysis; no source row hit that condition.

Strongest objection: the only fully evaluated universal-preservation proposal is false, while the proposed stronger intersection/parity invariant is unproved. There is no complete source resolution to review. A source root with Re(z)>0, certified by exact Routh/Hurwitz and independently recomputed coefficients (or exact rational complex-root isolation), would falsify the actual conjecture. Imaginary-axis boundary phenomena must be distinguished from strict-instability diagnostics because the target is weak half-plane stability.

## Literal Lean feasibility inventory

No Lean started; no compile claim. Future endpoint must define A(N,k) or source Eq1.14, the finite row polynomial over C, and prove `forall n z, eval (sourceRow n) z = 0 -> z.re <= 0`. A supporting strict-q endpoint requires proving s_n=x*q_n, q_n nonzero and treating n0/1 separately. Needed bridges: partition/recurrence agreement, polynomial differential recurrence, parity split, an actually proved all-order interlacing invariant or other root-exclusion theorem, and its complex-half-plane consequence. The essential invariant is missing; assuming it would simply restate the hard question. A finite Routh certificate or the unrelated input q at n6 cannot replace the universal endpoint. No large formalization justified before ordinary proof and independent review. Required future pins, if revived: Lean4.34.1/mathlibd13f23b723b8a846827a245b89c10fc7d3f11612, strict std3, warningAsError, serialRSS<3GiB, only allowed standard axioms, no sorry/admit/axiom/native_decide/unsafe.
