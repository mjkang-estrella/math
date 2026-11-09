# Unresolved local conjugating character conjecture

## Literal source

Christopher A. Schroeder, *Refining invariants of finite groups with class functions*, arXiv:2609.26464v1, submitted22September2026. Actual HTML Section2 Example2.6 and Section3 Theorems3.1–3.6 and their proofs read. The exact target is **Conjecture3.5**, not the discovery service's guessed Section2 numbering.

For every finite group G and every collection π of primes, define Ππ,G(g)=|C_G(g)| if every prime divisor of the order of g belongs to π, and zero otherwise. Identity is always included. The conjecture is that Ππ,G is an ordinary complex character. Equivalently every irreducible χ has nonnegative multiplicity

    mπ(χ)=Σ_{[g] consisting of π-elements} conjugate(χ(g)).

Only primes dividing |G| matter, but no bound on G, rank, degree, number of primes, or χ is permitted. The displayed formula follows by grouping the defining character inner product into conjugacy classes, using |[g]||C_G(g)|=|G|. The source proves integrality by Galois invariance, but that does not prove the sign.

The latest abstract fetched in this session identifies v1 only. The current author homepage lists this work as a2026 preprint and supplies no journal link. This is not a claim that no later publication exists. No forthcoming-proof announcement was found in the inspected source. A separate Robinson question, Kourovka21.113, concerns Ψ(g)=|C_G(g)_p| on p-regular elements; that is a DIFFERENT function and is not substituted.

## Existing results and eligibility boundaries

Source Theorem3.3 already covers π=p′ for arbitrary groups, and arbitrary π for π-separable groups. Its proof uses nonnegative row sums of Brauer/π-partial character tables and decomposition numbers. Source Theorem3.6 already handles the exceptional Weil character of PSU3(q), gcd(3,q+1)=1. Neither is proposed anew.

The symmetric-group test initially looked useful because character values can be computed exactly by rim-hook recursion. But Sheila Sundaram, *Prime power variations of higher Lie_n modules*, arXiv:2107.06389v1, actual Definition3.2 and Theorems3.5–3.6/proofs, explicitly supplies the ALL-n, ALL-π symmetric-group result. If P(π) is the positive integers with prime factors in π, Theorem3.5 identifies Σ_{λ:λ_i∈P(π)}p_λ with a symmetric-power series of actual induced cyclic modules. Theorem3.6(1) gives Schur positivity. Frobenius characteristic of Ππ,Sn is exactly its degree-n part, since the z_λ centralizer factor cancels the characteristic denominator. This is a routine exact bridge; no fresh theorem or review is requested for it. Theorem3.6(3) also covers the even-cycle-type power-sum sum. Journal metadata: JCTA184(2021)105512, DOI10.1016/j.jcta.2021.105512. Actual arXiv PDF read; published body not separately retrieved, so final textual equivalence is not certified.

Robinson2505.03976v4, actual introduction, §§2–3 and8 read, has the generalized-character/root-count formulation and already provides the π-separable/p′ results. Its current arXiv history ends21October2025. Published J.Algebra690(2026)37–74, DOI10.1016/j.jalgebra.2025.11.001, is identified by the author's institutional record. The linked VoR PDF returned403 via web; stopped, no other-host evasion. Its exact published body is an unresolved source-access gap, not cleared from the abstract.

## Exact finite diagnostics and their scope

check.py computes integer Sn characters by the beta-number Murnaghan–Nakayama rule. For a partition λ with L rows, take beta numbers b_i=λ_i+L−i−1. A k-rim-hook removal replaces b by b−k when the latter is nonnegative and unoccupied, with sign (−1) to the number of beta numbers strictly between. Recursing over cycle lengths computes χλ(μ). A Boolean subset zeta transform then sums over all cycle types whose prime support lies in π.

For An, retain even cycle types and double the contribution from distinct odd-part cycle types, precisely the Sn classes splitting into two An classes. Nonsymmetric Young diagrams restrict irreducibly. A self-conjugate diagram splits into two irreducibles, interchanged by an odd permutation; Ππ,An is invariant under that conjugation, so their multiplicities agree and each equals half the computed restriction inner product. The script checks that these halves are integral. n=1 is treated without the index-two splitting rule.

Results: no negative multiplicity through n=18, 269258 row/prime-set tests across both families (conjugate labels can duplicate an An test). Full exact ordinary character row orthogonality is independently checked for n≤8 with rational weights1/z_μ. These are diagnostics, not a new all-order proof, and the Sn checks are covered by the classical theorem above. No interpolation, random sampling, approximate roots or solver inference occurs.

## Failure of a local-to-global positivity shortcut

An attempted proof would restrict Ππ,G to suitable smaller subgroups, invoke existing positivity there, then use character integrality to recover positivity globally. The last step is false even if the class function is rational, integer-valued and pointwise nonnegative, and its restriction to EVERY proper subgroup is a character.

Let G=A5 and χ be its standard degree-four irreducible character (fixed points in the natural five-point action, minus1). On classes of orders1,2,3,5,5 its values are(4,0,1,−1,−1), with class sizes(1,15,20,12,12). Its norm is(16+20+24)/60=1, and its trivial inner product is0. Put

    F=ρ_G−5χ+5·1_G.

Then F takes values(45,5,0,10,10), all nonnegative integers, but [F,χ]=4−5=−1. Restrictions to maximal subgroups A4,D10,S3 have respective nonnegative irreducible multiplicities

    A4:  (5,5,5,10), degrees(1,1,1,3);
    D10: (11,6,7,7), degrees(1,1,2,2);
    S3:  (10,5,15), degrees(1,1,2).

These follow from restriction χ|A4=1+3, χ|D10=2a+2b, χ|S3=1+sign+2 and ρ_G|H=[G:H]ρ_H. All have degree45. Every proper subgroup is contained in one of these maximal types, so further restriction gives characters. route_check.py independently verifies the standard character values by enumerating only the60 even permutations on five letters, its negative inner product and all three restriction multiplicity rows. The maximal-subgroup classification is classical; it is not an alleged new discovery. This falsifies the proposed inference, NOT Conjecture3.5: F(1)=45≠60=Ππ,A5(1) for every π.

## Failure of a power-closure shortcut

A separate attempt drops the prime-set hypothesis and assumes only that the selected classes are closed under taking powers and rational conjugacy. In C6, take X to consist of elements of orders1,2,3, excluding order6. For a faithful linear character the selected value sum is1−1+(ζ3+ζ3²)=−1. Thus ΠX,C6 is not a character despite those closure properties. X cannot equal Gπ: including orders2 and3 forces order6 when the rule is a prime set. This is another proof-method falsifier, not a source counterexample.

## Bounded prior investigation and chronology

Read campaign AGENTS, ledger, prior-campaign-context, NEXT and relevant previous r10/r22/r25/r28 summaries and rejection explanations. No excluded family was revived, and nilpotent Kac2610.37207 was stopped without investigation because of the author announcement. Early Kourovka21.99 was excluded before mathematical investment: latest October update-3 itself supplies Muliarchyk's full refutation, and alunik/kourovka-lean acknowledges a public counterpart. MacHale21.89 was rejected as an economical lead after current OEIS reported finite screening beyond2000000; no new large enumeration was attempted.

Current primary author/source pages and exact-title/statement searches were consulted. No matching full solution was located in those bounded searches. Complete cached Omega D5/Problems, OpenAI preprints and AIM scoped trees were screened by target/character terminology; hashes and exact path hits are recorded. These trees are dated snapshots, NOT current-head clearance and NOT all-body absence. A current raw Omega README fetch succeeded but is just187bytes and does not certify its current head or catalogue. GitHub API had already returned403 in prior work; no API retries, loops or alternative-host access were attempted. No exact current public registry completeness claim is made. OpenAI/Count/AIM heads are inherited dated observations, not renewed here; current Count was not fetched. MathDB solution bodies were not cleared.

## Remaining gap and recommendation

The full finite-group conjecture remains unresolved here. A uniform construction of an actual module for Ππ,G, or an exact negative row sum for an allowed prime-set class function of a genuine finite group, is missing. Integrality, elementary-subgroup restrictions, pointwise positivity, generic power closure and finite classical-family checks do not fill that gap. No full ordinary proof exists in this lane; consequently no PROOF.md or Lean endpoint is supplied.

Strongest substantive objection: the one successful all-order mechanism identified is exactly Sundaram's old symmetric-group theorem, while the remainder consists of diagnostics and falsifiers outside the source's literal class. They earn no discovery credit. Full current registry coverage, Robinson VoR and closest table-sum literature remain prior-art gaps. Independent discovery/acceptance review is NOT warranted yet; a narrowly requested review of the diagnostic arithmetic could be useful but would not advance acceptance. No counts or shared artifacts changed.
