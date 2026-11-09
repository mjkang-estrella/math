# MathDB 358323: recurring interior zeros

Candidate only; zero campaign credit. Independent review and root adjudication remain outstanding.

## Exact source

Juhoon Chung, *Zero Distribution of Generated Taylor Polynomials*, arXiv:2305.05130, Conjecture 47, printed p.119. Definitions 37–41, printed pp.92–93, specify zero sets in a complex domain, their upper and lower set limits, and define the limit only when the two agree. The conjecture asserts the circle of radius 1/|t₁| for every nonzero real a,b,c with b²−4ac≤0, where t₁ is a denominator root of smallest modulus. The source explicitly discusses and fails to apply BKW because of equal-modulus characteristic roots. This is a set-limit assertion, not weak convergence of normalized root-counting measures. The latter is not refuted here.

The downloaded source PDF, exact raw MathDB record and all hashes are in source-receipts.json and results.json. No publisher-version identity is claimed. The exact source statement and definitions were read, not inferred from the MathDB label.

## Ordinary proof

Set a=b=c=1. All three parameters are nonzero and the discriminant is −3. The roots of t²+t+1 are (−1±i√3)/2; both have modulus1, so either is a smallest-modulus root and the proposed circle is |z|=1.

Write

    A(t)=1/(1+t+t²)=(1−t)/(1−t³).

As a formal power series, its coefficients cₙ repeat 1,−1,0. Multiplication by 1/(1−zt) gives the genuine polynomial sequence

    Pₘ(z)=Σ_{j=0}^m c_{m−j} z^j,
    Σₘ Pₘ(z)t^m = 1/((1+t+t²)(1−zt)).

In particular Pₘ(0)=cₘ, so P₍₃ₖ₊₂₎(0)=0 for every k≥0. Equivalently, grouping terms gives

    P₍₃ₖ₊₂₎(z)=z(z−1)Σ_{j=0}^k z^{3j}.

For every r>0 and N≥0, take m=3N+2>N and w=0. Then Pₘ(w)=0 and |w−0|=0<r. Thus0 belongs to the upper limiting zero set under source Definition38. It does not belong to the proposed unit circle. If the source limit equalled that circle, its upper limit would equal the circle by Definition41, a contradiction. This proves the negation of the full universal conjecture through a single admissible parameter choice. It does not claim an exact replacement zero set, minimality, or a measure-distribution result.

## Lean correspondence

Taylor.lean defines F(z) as the inverse formal power series of the full denominator and Pₙ(z) as its nth coefficient. `generating` proves denominator times F equals1 using its nonzero constant coefficient. `generated_witness` identifies the series built from these actual coefficients. `Generated` is the literal generating identity, not a proxy test.

At z=0, `recur`, `period`, `base` and `recurring` prove the coefficient recurrence, period3, P₂(0)=0 and all P₍₃ₖ₊₂₎(0)=0. `Upper`, `Lower` and `HasZeroSetLimit` spell out the source's ball quantifiers directly. `root_t₁`, `root_norm`, `minimal_root` certify the denominator root and smallest-modulus condition. `exact_mathdb_negation` negates the universal assertion with every parameter, generating-identity and root-selection hypothesis present. No analytic summation, bounded search predicate, numerical tolerance or unproved polynomial-root certificate occurs in that endpoint. The ordinary finite polynomial coefficient formula above explains the standard formal-generating-function interpretation; no infinite analytic convergence assertion is substituted for the source set limit.

The fresh extracted build uses warningAsError. Audit.lean enumerates every namespace constant, including generated auxiliaries, computes transitive axioms and runs #print axioms on all31 names. Only propext, Classical.choice, Quot.sound occur. The auxiliary-name linter alone is disabled in Audit.lean because naming generated declarations is intentional; it is not disabled in the theorem file. No sorry/admit/new axiom/unsafe/native_decide/ofReduceBool occurs in the local theorem source.

## Prior-art and significance limits

Live OpenAI/math HEAD and Omega default HEAD were refreshed with /commits/HEAD and match the inherited current snapshots. The complete preprints tree and the complete Omega D5/Problems scoped trees were searched by path names; this is not an all-proof-body search. Bounded exact-title and identifier searches located no earlier campaign technical review beyond the current assignment. MathDB/Palomar inherited403 is not clearance.

Sokal's arXiv final manuscript cond-mat/0012369v3, Theorem1.5 and the beginning of its actual proof through Lemma3.8 were read. It assumes no degenerate dominance: distinct dominant characteristic functions cannot be constant unit multiples on an open set. Here the two quadratic-pole roots have unit ratio and dominate throughout the interior region, so that theorem does not give the conjectured circle conclusion. Its proof explicitly uses the assumption in Lemma3.8(d),(k). This comparison establishes a failed subsumption route, not novelty against all classical theory. UCL's public copy returned403 and was not retried; arXiv was a lawful distinct public copy.

The algebra is elementary. The nominated content is a persistent interior-zero obstruction to the full source conjecture, not a finite-size exception, domain correction, new coefficient identity, or a positive-density root-measure claim. Whether this meets the campaign significance standard remains for independent review/root. Classical resonance/periodic-section phenomena, uninspected citing papers, other versions and hidden registry bodies remain bounded-search limitations. There is no worldwide-priority claim and no selfacceptance.
