# r87: no full discovery

Credit proposed: **0**. Counts remain 8 additional / 38 total. No PROOF.md, Lean, paper, shared edits or external publication.

## Early source and classical gate

Three distinct primary questions were screened. All use actual downloaded bodies, not database labels.

1. **Merikoski–Haukkanen–Sasaki–Tossavainen, JIS 28 (2025), Article 25.7.1, Conjecture 5, printed pp5–6.** For every integer n>3, with T={1,...,n}, -1 is a generalized eigenvalue of L_T relative to G_T iff the binary expansion of n starts 10. Definitions on p2 are literal lcm(i,j) and gcd(i,j). Generalized eigenvectors are nonzero complex vectors; G_T is positive definite. Thus the claim is exactly singularity of the real integer symmetric matrix A_n=L_T+G_T. Source Theorem 1 and its proof establish the MAX–MIN rank-two mechanism; that mechanism does not extend to arithmetic matrices. Source pp4–5 explicitly disprove its naive all-eigenvalue continuation. Source Theorem 6 proves interlacing, which alone leaves singularity unresolved.

   **Known-public gate:** Korea Superintelligence Labs, *A three-term null vector for L_T+G_T: half of a conjecture...*, actual primary PDF read, especially Lemma 3.1, Theorems 4.1, 5.1, §7 and §11. Its Theorem 4.1 proves the entire 10 direction, Theorem 5.1 classifies all witnesses 2e_m-3e_(2m)+e_(4m), and §7 records exact checks through n=1000. The paper explicitly leaves the 11 converse open. The public data record is dated September 2026; this predates this lane. Neither independently finding the same vector nor extending its finite checks is eligible. Source corrections and general-set variants are also already public. Current API response has snapshot 2026-09-09, commit c74ecadd, not a guarantee of present completeness.

2. **Feng-Zhen Zhao, INTEGERS 26 (2026), A55, Conjecture 1, printed p8.** Set T_n=sum_(k=0)^n (-1)^(n-k) M_k, with M_k the Motzkin numbers. The sequence (T_n^(1/n))_(n>=9) is log-concave: at every center n>=10, T_n^(2/n) >= T_(n-1)^(1/(n-1)) T_(n+1)^(1/(n+1)). Source Theorem 1, pp3–4, proves T_n log-balanced for n>=8 via the two ratio recurrences and rational bounds; its proof was read. This is not the requested root inequality. Closest classical body: Chen–Guo–Wang, *Infinitely Log-monotonic Combinatorial Sequences*, Theorem 3.1 and proof, pp7–10: ratio log-concavity plus an initial root comparison imply the root result. Ratio log-concavity of this alternating T sequence has not been established here. A proof consisting only of verifying this classical criterion by source bounds would require a strict substantive reassessment, not automatic credit. Finite exact root checks below are diagnostics only. No full resolution or priority clearance claimed.

3. **Shenxing Zhang, *On the linearity of the periods of subtraction games*, author version modified 2025-07-30, Conjectures 1.2 and 1.3, p2.** For every fixed finite subtraction set S, there exist positive q,N and integers alpha_r,beta_r,lambda_r,mu_r for 0<=r<q such that for every c>=N with c=r mod q, the minimal preperiod and period of SUB(S union {c}) equal alpha_r c+beta_r and lambda_r c+mu_r. This implies the weaker at-most-linear Conjecture 1.2. Theorem 1.4 already covers four classes, including all intervals and {a,2a}; Proposition 3.1 and proof give explicit word decompositions for the latter. This is a deterministic mex game, distinct from the already accepted randomized all-odd subtraction family. No universal finite-state reduction with bounds uniform in c was found. The ordinary pigeonhole bound is exponential in max(S union {c}), not linear. No attempt to count a special S, a displayed formula, or a source-proposition adaptation.

## Main attempt: the arithmetic converse

Only the LCM–GCD **converse** was pursued beyond screening. Exact remaining statement:

For every k>=2 and integer n with 3*2^(k-1) <= n < 2^(k+1), prove det(A_n) != 0.

Together with the already public 10 direction, this would resolve the full original Conjecture 5. This lane does not prove the converse.

Write E_(i,d)=1 if d divides i and 0 otherwise (1<=i,d<=n), and U=E^(-1), so U_(i,d)=mu(i/d) for d|i. U is unit lower triangular. Classical divisor inversion gives

U G_n U^t = diag(phi(i)).

For L_n the corresponding entry C_(i,j) is

sum_(d|i,e|j) mu(i/d) mu(j/e) lcm(d,e).

Multiplicativity in the pair (i,j) reduces this to prime powers. At a prime p the local factors are: 1 at exponents (0,0); phi(p^a) at (a,0) or (0,a), a>0; -phi(p^a) at (a,a), a>0; and 0 at unequal positive exponents. Hence C_(i,j)=0 if any common prime has unequal valuations; otherwise C_(i,j)=(-1)^omega(gcd(i,j))*phi(lcm(i,j)). Consequently det(A_n)=det(diag(phi)+C). This is a helper reduction, not a source resolution or a novelty claim.

The transformed diagonal is (1+(-1)^omega(i))*phi(i). Its nonnegativity might suggest a sign-definite reduction, but the principal block on indices 1,2 is [[2,1],[1,0]], determinant -1. This exactly falsifies the proposed positive-semidefinite shortcut for every n>=2. Zero diagonals cannot be discarded: they have nonzero cross-entries. The primewise local factorization of entries also does not factor the determinant on {1,...,n}; this set is not a rectangular product of prime-exponent ranges. Taking determinants prime by prime is unjustified. The closest public paper §11 independently warns against a simple Smith-type product formula and reports irregular inertia. Interlacing supplies inequalities, not the strict nonvanishing needed here.

Exact modular row reductions agree with the expected pattern at 68 sample n (4..64 and 95,96,127,128,191,192,255). Full rank modulo 1000003 certifies rational nonsingularity for those sampled 11 values only. Rank deficiency modulo one prime alone does not certify rational singularity; the known public vector supplies that separate direction. These computations are all inside the public n<=1000 range and have no discovery value.

## Strongest objections and falsifiers

- The substantive work still missing is a universal proof that the mixed arithmetic matrix diag(phi)+C has zero kernel in every 11 interval. The derivation above and modular checks do not supply it.
- The easiest complete mathematical component was already publicly proved. Rebadging the known vector, its support classification, a helper transform or finite rank checks would fail the task.
- A single n>=6 starting 11 with an exact nonzero rational null vector refutes the source conjecture. Failure of the PSD shortcut does **not** refute it.
- Zhao's claim is refuted by any n>=10 with T_n^(2(n^2-1)) < T_(n-1)^(n(n+1))*T_(n+1)^(n(n-1)); no such witness appeared at n10..50. Classical ratio-log-concavity needs its full unbounded proof before Theorem 3.1 applies.
- For Zhang, finitely many c cannot refute eventual quantifiers. One needs a fixed S and proof of non-eventual quasi-linearity, or a full uniform construction for every S.

## Coverage limits

All-date project searches used rg -l first across all reports, FINDINGS, discovery, SUMMARY and provenance, then relevant bodies/contexts. Initial aa55 regex matched hexadecimal hashes; these were read and are false positives, not discoveries. Full-tree baseline and compare limitations are recorded in coverage.json. Baseline source inventories are inherited root evidence, not re-created complete current trees. Filename absence was never treated as priority. Live OpenAI head is unchanged; Omega advanced to 6f8ee6614e0faf9dfa2cce46d1eb758dea97c335. The r83 compare from the stipulated root baseline to 23a4ae6f... has 45 commits and 122 changed files, below the usual API file cap; it is compare evidence rather than a newly fetched recursive tree. No universal novelty clearance is asserted. All HTTP attempts/statuses/UTC/hashes are in http.json; no access restriction was bypassed.
