# r98 — two fresh finite/algebraic claims; GIT full scope unresolved

Credit 0. Counts remain **8 additional, 38 total**. No full ordinary result, Lean, paper, acceptance, or novelty clearance is claimed.

## Early duplicate screen and source selection

Read ancestor and batch AGENTS, current NEXT, ledger and prior-campaign context, immutable upstream pin and manuscript catalogue. User's prohibition on Lean/paper overrides batch production requirements. All writes are confined to this lane. No children, git operations, shared edits or external mutations.

Before sustained investment, searched all dates under openai-proof-research for the selected arXiv identifiers, author pairs and mathematical names across SUMMARY/discovery/FINDINGS/PROOF/review/ledger text files. `duplicate-audit.json` records matching lines and hashes, `duplicate-corpus.json` the inspected path/hash corpus. A final expansion includes Markdown throughout review paths. This is a lexical content screen, not a semantic universal duplicate proof. Identical byte contents are screened once. The first inventory implementation exceeded the fixed address-space cap; the streaming replacement passed without raising caps.

Fayers 2508.00074 was retired immediately: r63 and r82 already screened it, and r82 identifies a public proof. It is not one of the two fresh invested claims. GIT matches consisted of an unrelated numbered conjecture in r6, unrelated M4 in an old analysis screen, and bibliographic citations in the r59 Aluffi successor body. Those passages were read; none is an earlier GIT4.10 attempt. Inverse-KL had no matching prior local attempt. The user-listed r92–r96 families and active r97/MMPP lanes were not reused.

## Claim A — Xie–Zhang inverse-KL binomial transform: publicly refuted

Primary: Matthew H. Y. Xie and Philip B. Zhang, arXiv:2504.17567v1, 24 April2025, **Conjecture1.4**. For every simple matroid M, if Q_M has degree d, the polynomial B(Q_M)=sum_i binom(d,i)[t^i]Q_M t^i has only real zeros. Actual source Theorems1.2/1.3 prove the paving case; their Newton-inequality implication and Section3 interlacing proof are present. The current abs record lists only v1.

Latest successor: Braden–Ferroni–Matherne–Nepal, arXiv:2510.01086v2 (22 October2026; v1 posted1 October2025), **Theorems1.5 and5.3**. Actual Section5, preceding corank-two formula/proof and explicit polynomial were read. The rank19, size21 partition matroid dual construction from blocks (4,4,4,3,3,3) is the stated counterexample. It is simple: in the dual rank-two parallel-class model no cocircuit has size1 or2 (complements of parallel classes have size17 or18). Thus the original simple-matroid qualifier does not rescue the claim.

The printed ascending Q coefficients are
(163,1790,10323,39217,106659,215169,323646,350404,232662,71162).
`verify.py` independently multiplies by binom(9,i) and uses exact squarefree/Sturm root counts: seven real roots counting multiplicity, degree9. This corroborates the already public proof body and receives no credit. Source generic log-concavity is a different conjecture and is not declared refuted here. An author-hosted PDF request timed out; the canonical arXiv latest HTML body succeeded. No retry loop.

## Claim B — Choi–Kiem–Lee GIT characteristic polynomial: selected full scope

Primary: arXiv:2505.01087v2, 3 November2025, **Conjecture4.10**, **Definition2.1**, **Proposition4.9**. Current abs lists v2 as latest. Published PLMS DOI10.1112/plms.70096 exists; publisher full body returned403 and was not retried. Typeset-versus-arXiv comparison remains HOLD.

Let n=2r+1>=3 and Y_n=(P^1)^n // SL_2(C) with equal O(1,...,1) linearization and the permutation action of S_n. The conjecture asserts BOTH:

1. For every k with 0<=k<=n, the coefficients in m of [t^k] S_Yn(m,t) are log-concave.
2. The coefficients of S_Yn(m,1) in m are log-concave.

Length log-concavity means a_l^2>=a_(l-1)a_(l+1) for every interior coefficient index l. Degrees k>n-3 give zero rows and cause no difficulty. No domain correction or individual k specialization is nominated.

Write R_a(m)=m(m+1)...(m+a-1), R_0=1, B_(n,j)=R_(n-j)R_j. By actual Proposition4.9, after multiplication by n!, the complete rows are

F_(n,k)(m)=sum_{0<=j<=r-1; j<=k<=2r-2-j; j=k mod2} binom(n,j) B_(n,j)(m),

and the t=1 row is

T_n(m)=sum_{j=0}^{r-1}(r-j)binom(n,j)B_(n,j)(m).

The proposition's proof is read: apply principal specialization to the Kirwan cohomology decomposition4.12. These formulas are public source facts, not new results. Printed Example4.11 has an apparent omitted m in the last term; our calculations use Proposition4.9 and do not nominate an erratum.

## Closest classical proof mechanisms, and exact obstructions

Actual source Lemma2.4 cites convolution closure of nonnegative log-concave sequences with interval support; Lemma2.5 uses real roots to imply log-concavity. Each B_(n,j) is consequently already log-concave. Neither lemma gives closure under the varying sums above. Source Corollary4.4's product-space result is a different object; Section6 asymptotic fixed-index statements for Mbar are not the required all-n GIT result. The current public successor search found no proof of GIT4.10, but this is bounded search, not priority clearance.

**Shortcut1, real-rootedness of source rows, fails on a genuine row.** For n7,k2 the scaled row factors exactly as

2m(m+1)(m+2)(m+3)(m+4)(11m^2+16m+15).

The quadratic discriminant is -404. This row is nevertheless log-concave (all its exact defects are nonnegative). Thus Newton cannot simply be applied to every complete source row. This is not a source counterexample.

**Shortcut2, nonnegative pairwise mixed defects, fails.** If a_i=[m^i]B_(n,j) and b_i=[m^i]B_(n,h), the cross coefficient in the defect of A+wB is

C_i=2a_i b_i-a_(i-1)b_(i+1)-b_(i-1)a_(i+1).

At n17,j0,h7,i7 it is -101773398996093086080. Hence a termwise-positive expansion of source defects cannot work.

**Shortcut3, arbitrary-positive-mixture closure, is actually false.** At n35, A=R_35, B=R_19 R_16, i17, take the positive rational weight w recorded exactly in route-results.json. With D_A=a_i^2-a_(i-1)a_(i+1), D_B similarly, w=-C_i/(2D_B). The verified identity

D(A+wB)=D_A-C_i^2/(4D_B)<0

refutes the broad closure principle. `verify.py` reconstructs the integer coefficient lists and checks the exact rational negative defect. This artificial mixture omits the required intermediate terms and uses the wrong weights; it does NOT refute the GIT assertion or earn helper/partial credit.

## Sustained full-scope route: constrained prefix recurrence

Introduce H_n(m,t)=sum_j binom(n,j)B_(n,j)(m)t^j. The elementary formal generating function is

sum_n H_n(m,t)z^n/n! = (1-z)^(-m)(1-tz)^(-m).

Differentiate with respect to z and multiply by (1-z)(1-tz). Equating coefficients proves, for n>=2,

H_n=(n-1+m)(1+t)H_(n-1) -(n-1)(n-2+2m)t H_(n-2),

with H_0=1 and H_1=m(1+t). This is an exact derivation valid as a formal identity in m,t, not an asymptotic approximation. Let q=min(k,2r-2-k). Then

F_(n,k)=[t^q]H_n/(1-t^2),   T_n=[t^(r-1)]H_n/(1-t)^2.

The first equality follows because the cutoff admits precisely j=q,q-2,...; the second because the coefficient of t^(r-1-j) in (1-t)^(-2) is r-j. Thus the SAME recurrence feeds both full conjecture clauses, without changing source scope.

Coefficient extraction yields a signed recurrence involving neighboring n,k,l values; its negative H_(n-2) term prevents immediate convolution closure. Exact checks verify858 polynomial coefficient identities through n40 and300 prefix/symmetry evaluations. These identities only validate the reduction. To finish, one must prove uniform Turan nonnegativity in m for BOTH specified extractions, at n odd and all admissible q/l, while controlling the negative recurrence term. No such preserved inequality or all-order sum-of-squares identity was established. The arbitrary-mixture counterexample prevents dropping the prescribed kernel/weights. This is the precise mathematical gap, not a claim that the conjecture is false.

Bounded reproducibility:1640 complete source rows (both clauses combined) at odd n<=81 have no negative coefficient defect. Source already reports tests through n400: our smaller census adds no discovery evidence or novelty. Increasing that census is not a replacement for the missing uniform induction.

## Current registries and chronology — HOLD retained

Default public HEAD was freshly read29 October2026: Omega **dce0de1df2fe2e301a5f9d9664ba00eb50f617cd**, OpenAI **7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a**. Immutable OpenAI source pin fd4aeeb2... is distinct. The complete frozen root inventories are from root-edge-irregulator-final-freeze-r1 at18:13, Omega1b999d9f..., with350197 entries and OpenAI174524. Their bytes/hashes were read and lexically screened. Blueprint paths and Lean files are not equated.

Retrieved each comparison in the supplied chain. 1b999→2130:88 commits,300 returned files, CAPPED/POTENTIALLY INCOMPLETE; 2130→d2b0:2 commits/1 file; d2b0→c80:7/3; c80→fresh dce0:3/191. The last three segments are below the file ceiling. The older97commit/300file comparison is NOT used as complete. Because the first segment is still capped, this chain does not prove complete current inventory coverage. No semantic/freshness PASS is asserted. No selected topic filename matched the returned deltas.

Closest apparent OpenAI path was fetched at actual HEAD, and its Introduction Theorem and Background read: combinatorial invariance for Bruhat intervals of Coxeter systems, not inverse matroid KL real-rootedness nor GIT characteristic coefficients. Omega Choi/Kiem filename hits are quantum-entanglement namesakes or English choice words; these are not positively identified relevant proof bodies. Unidentified/unscreened bodies remain a coverage limitation, not cleared absence.

Strongest falsifiers: an odd n and literal k,l with a negative exact defect in F or T; or a public full theorem settling the same quantified assertions. Current source-status and registry holds separately prevent investment/acceptance even if a mathematical proof later appears. No PROOF.md is produced because neither full source clause is proved or refuted here.
