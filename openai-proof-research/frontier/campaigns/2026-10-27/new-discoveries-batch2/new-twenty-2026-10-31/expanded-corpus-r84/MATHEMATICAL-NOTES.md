# Research record and uncredited formal endpoint

This lane adds no accepted result. All conclusions are subject to root review. The current campaign count remains 12/20 beyond 39 prior. The reservation metadata says “Exactly40” in one inherited field; TASK.txt and the explicit assignment require exactly 20, which results.json supplies.

## 334599: complete ordinary refutation under the recovered preprint semantics

Write D(A;B) for the unary supervenience connective, interpreted at a world w by

    for every u,v with S(w,u,v), A(u) iff A(v) implies B(u) iff B(v).

No symmetry, reflexivity, transitivity or factorization of S is assumed. Define

    G(A,B) = D(A; A and B).

Then G(A,B) holds at w exactly when B has equal truth values at every S(w,u,v) pair with A true at both endpoints. Proof: on such a pair the antecedent agreement is automatic and the consequent is just B-agreement. Conversely, on any pair agreeing on A, either A is true at both endpoints and the restricted agreement hypothesis applies, or A is false at both and both A-and-B values are false.

Let C00=A and C, C01=A and not C, C10=not A and C, C11=not A and not C. Then

    D(A,C;B) iff G(C00,B) and G(C01,B) and G(C10,B) and G(C11,B).

Indeed, an S-pair agreeing on A and C lies in exactly one cell. Conversely, any pair inside a cell agrees on both A and C. Thus the right side requires exactly the original forbidden-edge exclusions. This argument is valid for arbitrary ternary frames and arbitrary truth sets, including pairs of different worlds with identical atomic valuations. It does not use a false assumption that S(w,-,-) is a complete relation.

Translate every arity-2 formula recursively: preserve atoms and Boolean operations; replace each dependence connective by the four-cell formula using the translations of all three arguments. Structural induction on formulas, including arbitrary nesting, proves truth equivalence at every pointed model. Therefore every arity-2 formula has an arity-1 equivalent. The strict expressivity step at n=1 is false, so the universal hierarchy conjecture is false. One failed step suffices; no stronger all-arity theorem is being counted.

Lean/Hierarchy.lean formalizes actual recursively generated languages, actual ternary frames and their recursive satisfaction relation, the syntax translation, its semantic correctness, strict expressivity, and the exact negation of the universal conjecture. It is not a bounded truth-table theorem or a surrogate predicate. Nat-indexed atoms represent the customary countable propositional vocabulary. World types are arbitrary small types; the translation is uniform in the type. Model.nonempty is unnecessary and the proof works in the stronger setting allowing empty world types too.

### Qualification objections that remain material

The inspected arXiv preprint has Conjecture 15 and Section 7.2 proposing precisely this hierarchy. Its own Section 6.1 uses Boolean cells to eliminate determinacy arities on ordinary Kripke frames; Proposition 16 follows immediately after those cells. Goranko–Kuusisto, arXiv:1609.07398v2 Proposition 3.3 and proof, likewise gives a Boolean normal form on universal frames. These are actual proof-body reads. They do not directly state this arbitrary-ternary-frame endpoint: applying the ordinary-frame result without a bridge would incorrectly collapse the unary language to the agreement language, contradicting the target's own Proposition 9. However, their same cell decomposition plus the one-line guard identity above gives a complete source-adaptation bridge. Under this campaign's strict significance rules this is a serious routine-adaptation objection, not cleared by a Lean proof or an open label. Root should consider it explicitly before any nomination.

The actual journal body (Notre Dame Journal of Formal Logic 60(2), 2019, 283–309) was not read: Project Euclid returned HTTP 200 containing an Incapsula challenge, retained verbatim with a receipt; there was no retry or bypass. A source correction in that body could independently dispose of the lead. The author's arXiv search catalogue and a subject search for supervenience supplied no exact later resolution in the inspected records, but this is bounded and noisy coverage, not worldwide novelty clearance. No publisher-body equivalence is asserted. A current Omega path hit PhenomenalSupervenience.lean was actually read and concerns factorization of a joint public concept, not this syntax-translation theorem.

The certificate is an uncredited research artifact. No acceptance, significance pass, journal fidelity pass or priority claim is made.

## 337766: sustained stopping-threshold route

The p_n are critical Bernoulli biases, not a probability distribution of stopping times. Let U_k=P(M_k<=1). Let V_k(j) be the optimal win probability with k steps remaining and current maximum-minus-position j. With V_0(j)=1 for j<=1 and 0 otherwise,

    C_k(j)=p V_(k-1)(max(j-1,0))+(1-p)V_(k-1)(j+1),
    V_k(j)=max(U_k,C_k(j)) for j<=1,
    V_k(j)=C_k(j) for j>=2.

The source's formula is U_(2n)=U_(2n+1)=1-sum_(j=1..n) Catalan_j p^(j+1)(1-p)^(j-1). Its terms have degree 2j. We used this to scale every Bellman value to an integer at rational p=a/b: the common denominator is b^k. Thus the second search has no numerical integration, floating values or unproved root comparisons. It covers all horizons 1..160 at p=47/100,48/100,49/100,495/1000,499/1000. It found no reversal of the even-index stop region. Binary64 bisection at 42 iterations separately gives roots 4..160 agreeing with the source table, but those are diagnostic brackets only.

Three attempted routes were distinguished:

1. Two-step semigroup monotonicity: equal adjacent U_(2n),U_(2n+1) is useful, but U_(2n+2) decreases. Monotonicity of V_k in a fixed payoff problem does not compare these changing-payoff problems.
2. Normalize by U_k and try to show continuation ratios decrease on even horizons. The recursion couples j=1 with j=2, while max selects different stopping boundaries at different k and p. No invariant uniform in j survived this coupling. No theorem of monotone Markov stopping was assumed without its hypotheses.
3. Use the source's odd/even interlacing. p_(2m+1)>=p_(2m-1)>=p_(2m) supplies upper bounds but does not order successive even values. Combining interlacing with convergence is logically insufficient.

The decisive missing lemma remains the uniform implication

    U_(2n)>=C_(2n)(1) implies U_(2n+2)>=C_(2n+2)(1)

for every 0<p<1/2 and n>=2, or a replacement comparison strong enough at the threshold. The new author follow-up arXiv:2610.26670v2 proves convergence to 1/2, states the older monotonicity conjecture in its introduction, and cannot be counted as its resolution. No limit proof was substituted for this exact ID.

## 339014 and 336311: generic rank routes

For signatures, piecewise-linear signature coordinates are coefficients in the truncated product of tensor exponentials of the m segment increments. Polynomial-path signatures are iterated integrals of x_i'(t), with x_i(t)=sum_(j=1..m) a_ij t^j. Computing these directly with dual numbers gives the differential with respect to all dm coefficients. Integration divides the time-degree coefficient by its new degree; finite-field primes exceed every denominator used. The affine expected rank is min(lambda_(d,k),dm); homogeneity subtracts one for the projective dimension in Eq49. Both kinds, d=2,3, k=3,4, m=2..4, at three fixed modular samples per case attained expected rank. These cases overlap the source's existing computations and cannot be promoted into discoveries.

A uniform proof would need an explicit nonvanishing minor in every dimension before saturation and free-Lie direction spanning after saturation. A positive modular minor provides characteristic-zero generic lower rank, while deficient modular samples prove neither a characteristic-zero identity nor generic deficiency. We did not obtain such a uniform minor. Reparametrization of a finite-degree polynomial path was considered as a possible kernel mechanism: a generic affine reparametrization preserving both endpoints is trivial, and nonlinear reparametrization generally changes the degree. Hence this does not furnish a generic family of positive-dimensional fibers at the source's fixed m.

For fat-line postulation, fix the fat line ideal (x2,x3)^m in P3. Degree-d monomials with exponent(x2)+exponent(x3)>=m form its vanishing space. Substitution of a general line x_i=a_i s+b_i t gives d+1 linear equations per line. All 224 triples m=1..4,d=1..7,r=1..8, with three deterministic F65521 samples per triple, attain expected rank on this kernel. Points where a minor vanishes are specializations and do not refute generic maximal rank. At d<m-1 the fat-line global-section target requires further accounting; the script expressly does not claim a full generic-theorem proof from the kernel test alone.

## Resource and trust limits

Each substantive experiment and Lean run used the retained limiter: two-CPU affinity, CPU 120 seconds, wall 140 seconds, monitored process RSS 6 GiB, 12 GiB virtual address space. RSS monitoring is sampled, not a cgroup guarantee or an aggregate-descendant monitor. Lean/checker themselves ran with -j1; all runs and failures are retained. The fresh replay deliberately trusts pinned cached upstream oleans and does not claim to rebuild mathlib or Lean. There are no new axioms, unsafe endpoint definitions, sorry/admit, native_decide or ofReduceBool in the final local proof module. Early generated unsafe recursion implementation was eliminated by making the semantic functions noncomputable; the final complete module audit checks safety, axiom status and transitive dependencies for every declaration from the module, not merely a prefix or hand-picked theorem list.
