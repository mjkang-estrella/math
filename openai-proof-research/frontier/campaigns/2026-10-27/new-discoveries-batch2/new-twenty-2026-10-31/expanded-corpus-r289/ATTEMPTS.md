# Sustained ordinary attempts and exact gaps

All arguments here are hand reasoning. No numerical search, solver, enumeration program, or Lean was run.

## 342273: search game

See ORDINARY-GAME-342273.md for complete proof. First shortcut, applying the complete-hypergraph k=1 theorem to a restricted hypergraph, fails because its favorable actions need not be allowed. Second approach, equalizing all scaled weights p(S)r(S), is precisely the conjecture and cannot be assumed by LP extreme-point arguments: basic optima need not give equal positive scaled coordinates. Fractional matching supplied a full route. The triangle and disjoint edge need two different positive weights; adding a zero-weight bridge gives a connected example. Source v1/v2 agree on arbitrary hypergraphs. Journal access failed, companion coverage is partial, and routine-classical-bridge exclusion is recommended with the full reduction written out. No qualified candidate.

## 352093: simultaneous data placement

Definitions read from Liu–Zhou v1 introduction and Section 2 selected proofs: blocks are a family indexed by files, so repeated equal blocks are allowed. For a fixed admissible v,k,b the set of indexed placements is finite, yielding an optimum for each individual x; this does NOT interchange ∀x∃F with ∃F∀x. A candidate proof by compactness/minimizing at x=1 fails: all polynomials equal there, and minimizing a derivative or lexicographic coefficients need not dominate for large x.

Second route: put t=x−1≥0 and M_j(F)=Σ_{|U|=j} λ_U(F)^2. The source identity gives P(F,1+t)=Σ_j M_j(F)t^j−b(1+t)^k+b². The last two terms are placement-independent. Hence simultaneous minimization of every M_j suffices. A unit transfer between integer loads a≥b+2 lowers their sum of squares by 2(a−b−1)>0; equal or almost equal j-loads minimize M_j at its fixed total b binom(k,j). This completely explains the source's well-balanced sufficient condition. But the transfers cannot be made independently at different j, since all loads come from the same actual blocks. Nonexistence of a well-balanced design does not disprove an optimum: the source's nearly well-balanced triples address exactly such cases.

Third route: use endpoint competition to refute. At t↓0, any simultaneous optimum must minimize M_1; among tied M_1 it must minimize the next differing M_j. At t→∞ it must minimize M_k, then descending coefficients. A genuine refutation needs admissible parameters where these necessary endpoint minimizer classes are disjoint, plus complete lower bounds over ALL placements. No such concrete pair of disjoint classes or finite object was obtained. Two placements with crossing polynomials alone are insufficient, since a third could dominate both. No sweep was authorized or run. The v<k,b>0 literal defect would be a domain correction only and is excluded.

Actual source lemmas 1.2–1.3 and selected Section 2 defect proofs explain k=2 and broad k=3 cases. Their proof is not an all-k construction. Missing full-scope lemma: existence of a placement with P(F,x)≤P(H,x) for every placement H and every x≥1 for all admissible (v,k,b), or an exact parameter with a proved empty simultaneous-minimizer intersection. Journal landing page is metadata/abstract/references only; full printed construction and all citing/correction bodies remain unread. Park unresolved; do not turn residual triple-design exceptions into a Pi job for the all-k question.

## 319227: Euler difference table

Actual normalization: e_n^n=n!, e_n^{k−1}=e_n^k−e_{n−1}^{k−1}, d_n^k=e_n^k/k!. The real-rooted-coefficient theorem does not apply: the source itself gives the n=2 polynomial 1+x+x². First failed route is therefore PF/real-root preservation. A second route tries to induct L on n using the positive recurrence d_n^k=d_{n−1}^{k−1}+(n−k)d_{n−1}^k. L is nonlinear and expansion introduces mixed neighboring rows; ordinary log-concavity preservation supplies neither all iterates nor an invariant for the transformed arrays. The source's cubic ratio estimate proves 2-log-concavity on 2≤k≤n−2; that proof does not establish the analogous inequalities for L^r d at arbitrary r.

A third route considers a strong ratio cone a_k²≥R a_{k−1}a_{k+1}. If R≥(3+sqrt(5))/2 the standard invariant-cone mechanism is useful, but the Euler rows cannot simply be placed in it: the source's n=2 row (1,1,1) has central ratio 1. One would need an eventual iterate entering a suitable cone, uniformly in n and with the exact boundary convention, while proving all earlier valid interior inequalities. No such entry theorem was obtained.

Boundary check: with ZERO EXTENSION, the row (1,1,1) transforms into (1,0,1), then (1,−1,1). This is exact hand arithmetic, not a full intended refutation: the printed second-order theorem only claims the interior range n≥4,2≤k≤n−2. On the shrinking-interior convention these n=2 second-iterate entries are not defined. The author-hosted revised text also says nonnegative in place of the preprint/MathDB positive. A strict-positivity objection or switching boundary convention is excluded from substantive credit. Actual all-depth interior endpoint and literature remain unresolved; no candidate.

## Other finite prospects

333738 is source-refuted: Slone v3 explicitly prints d=(2,2,2,1,1), a=(2,2), b=(2,1,1), λ=(2,2,2,2), with 16/5>4/3. Majorization after zero-padding holds, d*=(5,3), b*=(3,1). The source notation a⊢p conflates partition weight and vertex-count lengths; do not repair it into discovery credit. The exact printed counterexample is public, not a new witness.

334469 v7 Appendix C explicitly warns that Algorithm 3 used directly has known counterexamples (Kolmogorov personal communication), and the algorithm/tree process must be changed. The corpus omits this warning. Publicly printed warning is evidence against calling the naive tree assertion newly refuted, not a recovered full counterexample proof. Altered-process existence is a different endpoint; no clearing from this warning.

351478: local critical-configuration deletion is plausible, but Section 6 already excludes the G6 configuration. Copying it earns no credit. A full route needs a complete structural classification or deletion bound for every remaining link type; the general crown extremal assertion is still not proved here.

366444: the source proves the result only in classes possessing a Whitney maximum. Its source bridge is: maximum gives coefficientwise domination; any UMR graph then has a reliability polynomial both ≥ and ≤ that maximum, so the polynomials agree; the Bernstein basis is linearly independent, so their connectivity coefficients agree and the UMR graph is a 0-element. This is a complete routine conditional bridge, not a proof that every (n,m) class has such a maximum. No full general result.

371813: at r=1 the literal ball inequality fails already for K2 because the ball has 2 vertices and 1^C=1. This is an endpoint/prefactor correction, not resolution of polynomial growth or diffusive walk. No credit.
