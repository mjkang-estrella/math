# Selected investigations and actual review depth

## 323293: determinant — known complete result, exclude
Read original arXiv:1203.6812v2, Conjecture 8.3 p.17; read Minghua Lin arXiv:1212.1934v1 in full, including Theorem 2 and its proof, dated 9 Dec 2012. The latter explicitly identifies the conjecture and proves the same constant, with sharpness. These are actual proof-body comparisons, not abstract matches. Files and hashes are in receipts.

An independent short ordinary route is also available: D=diag(J_ii); A=D^(-1/2)JD^(-1/2) is positive semidefinite since xᵀJx=sum_{i<j}J_ij(x_i+x_j)^2. It has trace n and eigenvector D^(1/2)1 with eigenvalue 2, using balance. The other n-1 nonnegative eigenvalues sum to n-2; AM–GM bounds their product by ((n-2)/(n-1))^(n-1). Thus det(J)/prod J_ii≤2((n-2)/(n-1))^(n-1). This works also for unequal diagonals: congruence normalization need not preserve row sums. A second route is the trace/variance determinant inequality in Lin's proof. Neither is eligible as a new solution because the exact bound has been publicly proved since 2012. Do not count a Lean translation.

## 323289: torus — original source already reports a counterexample
Read arXiv:1203.6604v1, definitions and Propositions 2.1 onward, the explicit-construction section and Section 3 computation discussion. Source v1 and unversioned download are byte-identical (hash 5786d861...bd57). The literal record proposes a(n) points for every n, where a(n) is the least multiple of the divisor count τ(n) at least n. At n=14, τ(14)=4 and a(14)=16. The SAME ORIGINAL SOURCE, Section 3 p.9, reports that the 14×14 torus has capacity only 12. This is already in the March 2012 source, long before this investigation. The downloaded source does not contain the conjecture phrased as in the MathDB record.

Two possible approaches were checked: (1) use the source's exact finite Gröbner/monomial-independence upper-capacity computation; (2) look for a new small finite obstruction using projections to prime factors. Approach 1 is already a public counterexample, so a formal soundness proof for that computation would be formalization of known work. Approach 2 cannot make another counterexample to the same universal conjecture new. No blind new-capacity sweep was run. The source's reported capacity is a known result being cited, not a newly verified Lean certificate. Exclude credit, with source-fidelity caveat rather than attributing a new refutation.

## 323512: deviation — ordinary full scope closes, routine route
See DEVIATION-PROOF.md for two independent constructions and all three conjuncts. Actual source equations and proof bodies were read. Zero discovery credit; no Lean packet; routine-corollary concern is decisive under this task's rules.

## Fallback 323062: scoring games — exact remaining obstruction
Read arXiv:1202.4655v1, Definitions 3.1–3.2, proof of Theorem 3.1, Lemma 3.1, Conjectures 3.1–3.3 and surrounding explanation. Read Cohensius–Larsson–Meir–Wahlstedt, *Cumulative subtraction games*, EJC 26(4) (2019), #P4.52, Sections 2–3, proof of Lemma 11, Theorem 13, Lemma 14, Corollary 15. This proves eventual greedy play and period 2 max S for a SINGLE unrestricted subtraction heap; it does not, by its literal statement, settle the two-ruleset, fixed-side-heap endpoint here. Do not turn this partial overlap into a claim of full prior resolution.

The MathDB record omits an eventual-n quantifier. Source Conjecture 3.2 prints the same bare equality but its next paragraph explicitly says 'if n is large enough'. An early transient counterexample would be a wording correction, excluded. The probe preserves octal digit semantics: digit1 allows exact emptying only, digit2 allows a positive remainder only, digit3 allows either. Scores equal removed beans, and a position with no moves has value0.

Concrete approach A: exact recurrence

    V(n,m)=max({i−V(n−i,m): legal O moves} ∪
               {j−V(n,m−j): legal P moves}),

with 0 when the option set is empty. Finite-state eventual periodicity alone gives no period-2k conclusion. A repeat certificate for a specific ruleset is only a parameter instance. The bounded single-process probe covers all 240 length4 O digit strings with a continuation move and five P strings, n≤256, m≤6 (1200 rule pairs). It finds no mismatches in the final64 tested positions; maximum last mismatch was n=21. This is diagnosis, not a general theorem, not novelty clearance, and not a formal certificate.

Concrete approach B: extend the 2019 sacrifice argument. Opponent's greedy k-moves bound the number of losing sacrifices before the main-heap endgame, allowing an additive error of at most m for side-heap scores. However, a bounded number of sacrifices does not establish eventual optimal greedy first action. One must also justify a rearrangement lemma in the presence of a side game. Moving a large main-heap action earlier changes which player can terminate and when side moves remain available. The single-heap Lemma11 is not, as stated, this stronger lemma.

Concrete approach C: induction on side-heap size m. Assuming eventual2k for all m'<m makes side-move alternatives periodic forcing terms, but the main-heap max recurrence still could have a cycle whose period exceeds2k. A sufficient next lemma is that this forced max-minus recurrence with genuine side-game options eventually satisfies V(n,m)=k−V(n−k,m). No proof or exact persistent cycle obstruction has closed this step. Park; do not claim the unrestricted result. The public 2019 single-heap theorem must be credited before any future extension.

Live registry and MathDB gaps: target-specific Palomar queries and four live MathDB pages returned403. No retries, bypasses, browser tabs, or account actions. Previously successful revision651 receipts were hash-checked and reused only as provenance, not as clearance. Search results were used to locate primary bodies; no secondary theorem was substituted for primary proof review.
