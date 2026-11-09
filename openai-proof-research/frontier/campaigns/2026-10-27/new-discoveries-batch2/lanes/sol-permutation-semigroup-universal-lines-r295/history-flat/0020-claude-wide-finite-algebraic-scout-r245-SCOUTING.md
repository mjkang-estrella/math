# r245 wide finite/algebraic scout — SCOUTING

Date 2026-10-30 UTC. Counts unchanged: 9 additional / 39 total / next 40. Root alone accepts. No credit is claimed.

## Method and screens

**Search and freezing.**
* Searches went through the arXiv API (`export.arxiv.org`). Results were sorted by date, and every result was flagged against `administrative/seen-arxiv-ids.json`.
* That file holds 20,403 arXiv ids cited anywhere in 272,967 campaign text files. The scan skipped extracted paper bodies and this lane.
* Every scientific PDF was frozen before reading: `primary/` original, `frozen/` copy, and sha256 of both compared. The hash was rechecked before and after `pdftotext`. Hashes are in `http.jsonl` and `extractions.jsonl`.

**History screens.** `work.py history` searched the batch's ledger, NEXT, prior-context and tasks files, plus every lane's SCOUTING/SUMMARY/discovery/STATUS/PROOF file (~840 files, hashed in place, not copied). Results are in `administrative/history-*.json`.

**Exclusions.** Every topic the task excludes was avoided: floor sums, period doubling, truncated cosine, ear triangulations, subsum multiplicity, compact centers, cube CCT, median dynamics, polynomial basins, projection packing, all-even height.

**Routes not used.** No GitHub API/raw, ScienceDirect, Google challenge, browser or proxy routes were used.

**Web search.** Two standard web searches were run for prior-art discovery of the top survivor (summary below).

## Ranked survivors (three)

### 1. Das, Conjecture 5.1 — REFUTED here, all n ≥ 5 (explicit family, proof in discovery.md)

**Source.**
* S. Das, "Sign patterns that allow algebraic positivity", https://arxiv.org/abs/2112.00442v3 (v3 22 Mar 2022).
* Published in Linear Algebra Appl. 653 (2022) 151–182.
* Frozen sha256 `c7ebbffde1cd95c6cf363b9627d3dbd2311d066d0156fffd5a68e6df21198379`.

**Exact statement.** "If A is a minimally AP-irreducible sign pattern matrix of order n with all diagonal entries equal to 0, then A has at most 2n − 2 nonzero entries."

The definitions are verbatim in discovery.md:
* AP-irreducible: irreducible, a `+` in every row and column, and B_A = A⁺ − (A⁻)ᵀ irreducible.
* Minimal: replacing any nonzero entry with 0 destroys AP-irreducibility.

**Nearest proof body.** The source's Lemma 3.10 proves the bound under the extra hypothesis "no `+` in A[α,β] between distinct irreducible components of A⁺". Our family has such `+` entries (x→sᵢ), so there is no contradiction.

**Result.**
* For every n ≥ 4 we give an explicit zero-diagonal minimally AP-irreducible pattern with 4n − 10 nonzeros.
* It has a two-line proof by cut sets.
* It is also brute-force checked for n = 4..30.
* So the conjecture fails for every n ≥ 5. The n = 5 instance (10 > 8) is exhibited.

**Exact small values.**
* The conjecture is true at n ≤ 4: exhaustive search over 3¹² patterns gives f(4) = 6.
* Exact MILP gives f(5) = 10 with gap 0, re-verified by brute force. This is solver evidence.

**Proved upper bound.** f(n) ≤ 6n − 6.

**Prior/duplicate status.**
* None of these sources is in the campaign history (term + id screens returned 0 hits).
* arXiv: the only follow-up is the same author's 2412.06379v4 (Dec 2025, cycle patterns requiring AP). It cites the paper but contains no "conjecture" and no AP-irreducible extremal result.
* Web search (2 queries, 2026-10-30) found no refutation or proof.
* The ISI repository record (https://digitalcommons.isical.ac.in/journal-articles/2892) confirms the published abstract still says "We also propose two conjectures".
* The 2021 IIT Guwahati thesis of S. Das was identified at https://gyan.iitg.ac.in/handle/123456789/1917. Its landing page was frozen; the 19 MB body was **not read**.

**Access limits.**
* The LAA journal body sits behind a denied route (ScienceDirect) and was not attempted. Wording changes in print cannot be excluded.
* No MathSciNet/zbMATH citation crawl was done. Worldwide priority is not certified.

**Substantive objections (for root/reviewer).**
1. It may be judged routine. A random greedy search found an n = 5 counterexample in seconds, and the conjecture is a side remark in a paper's conclusion.
2. The intended scope is clear and the hypotheses are combinatorial. There is no ambiguity of reading: the source's own Definition and the zero-diagonal hypothesis are met literally.
3. The extremal question f(n) = 4n − 10 is open. Proving the matching upper bound would raise the result from a refutation to a sharp theorem.

**Decisive next calculations.**
* (a) Prove f(n) ≤ 4n − 10. A route: bridge-counting on P⁺-condensations, refined from the 6n − 6 argument.
* (b) Decide whether F₅ allows algebraic positivity, i.e. find a real matrix with a simple eigenvalue and positive left/right eigenvectors in Q(F₅). If none exists, Das's Conjecture 5.2 also falls.
* (c) Lean formalization of the n = 5 instance is trivial by decide-free finite reasoning. Not done (no Lean in this lane).

### 2. Abdollahi–Arezoomand–Ebrahimi, Conjecture 1 — unresolved, strong computational support

**Source.** https://arxiv.org/abs/2305.00279v1 (29 Apr 2023), frozen sha256 `06ade1d9…d2dbd9`.

**Exact statement.** "Let T be a set of transpositions in Sₙ. Then Cay(Sₙ,T) is integral, if and only if for some positive integer k, the graph G_T is a generalized complete multipartite graph of type k."

**Nearest proof body.** The source's own Propositions 4–6 (cycles, cubic graphs, k-cyclic graphs with k ≤ 3) and Corollary 1 (trees, cut vertices).

**Reading.** The class equals the cographs once empty weak-join factors are allowed. Under the strict reading, 2K₂ refutes the conjecture, but that is a wording defect only and is not counted.

**Status.**
* No history hits.
* The arXiv follow-ups found (2508.18593 S₃-covers; 2607.17477 Kourovka/Aristotle, about power-graph cographs) do not address it.

**Evidence.**
* Exhaustive search over all graphs on ≤ 9 vertices found no counterexample.
* The 189 Laplacian-integral non-cographs at n = 9 all fail. Almost all fail already in the 2-token irrep (n−2,2).
* The sole exception is K₃□K₃, which fails first at (6,3).

**Objections.**
* This is a global integrality characterization. No proof mechanism was found, and it is plausibly hard.
* The checks are floating-point (Young orthogonal form), not certificates.

**Decisive next.**
* n = 10 restricted to Laplacian-integral, connected and co-connected graphs. Theorem 2 of the source reduces minimal counterexamples to these.
* Or a proof that an induced P4 forces non-integrality in some token module.

### 3. Dwivedi–Blasiak–Grinberg, Conjecture 3.3 — unresolved, exact small cases agree

**Source.** https://arxiv.org/abs/2302.07239v2, frozen sha256 `4248e0ae…6c19`.

**Exact statement.** For λ the p-shifted n-staircase of length k with k ≥ n+1 and p > n,
P(s_λ ↦ 0) = 1 − ∏_{i=1}^{n+1}(1 − q^{−i}).
Here the z_i are uniform in F_q, z₀ = 1 and z_{<0} = 0.

**Nearest proof body.** Theorem 3.2 (the p ≤ n and k < n+1 cases), via multislant matrices. The authors say the method does not adapt.

**Status.** No history hit. The arXiv search for Jacobi–Trudi over finite fields returned no follow-up.

**Evidence.** `diagnostics/jtff.py` counts all F_q-assignments exactly for 28 cases: (n,p,k) ∈ {1,2,3}-ranges, q ∈ {2,3,5}, total ≤ 600k assignments. All 28 match. A counterexample therefore needs larger parameters.

**Objection.** A proof needs a new structural mechanism (a looser multislant recursion). No progress was made here.

**Decisive next.** Find a Toeplitz-block recursion for the outward-shifted case, starting at n = 1. There the matrix is a 2-step Hankel/Toeplitz hybrid.

## Compact rejections and parked items (distinct attributed questions)

| # | Source (frozen) | Question | Disposition |
|---|---|---|---|
| 4 | Das 2112.00442v3 Conj 5.2 | allows AP ⇔ ±A AP-irreducible | Parked behind #1(b). Existential over reals; no mechanism yet. |
| 5 | Best–Wanless 1912.11230v1 Conj 31 (also 15, 44) | t_ac+t_bc+t_ad+t_bd ≡ 0 mod 4 for every Latin square | Open in arXiv. Python-only enumeration at order ≥ 10 is too slow, and small orders were checked by the authors. Parked. |
| 6 | Klanderman–Montee–Piotrowski–Rice–Shader 2406.09697v1 Conj 6.3 | gap in D(n) for all even n ≥ 8 | Reject. The n ≡ 0 mod 4 scope rests on the skew-Hadamard existence problem, and n ≡ 2 mod 4 needs a new determinant-gap theory. |
| 7 | Abdesselam 2023 (as stated in 2408.17212v1 Conj 1) | log-concavity of A(p,n,k) in k | Reject. Verified n ≤ 100 for p ≤ 5; analytic and hard; only partial asymptotic results. |
| 8 | Sziklai Conj 18.11 (via 2409.04045v1) | D_f ⊆ M_d∪{0} ⇒ f = ax^{p^k}+b | Publicly proved by Csajbók, Cor 2.4. |
| 9 | Li–Pantangi–Song–Xie 2403.17783v2 Conj 1.4 | bounded intersecting density for quasiprimitive groups | Reject: CFSG-scale, no finite mechanism. |
| 10 | Ellis–Harper 2408.16064v3 Conj 1 | two orbits of size n/2 ⇒ derangement | Reject. Hard; checked up to order 50000; reduced to perfect groups; partial follow-up by Lee–Popiel–Verret. |
| 11 | 2410.02409v1 Conj 4 | additive complexity of k-automatic is k-regular | Reject: contains the long-standing abelian-complexity conjecture. |
| 12 | Huczynska–Vatter Conj 2.3 (via 2410.05834v2) | monotone grid classes finitely based | Publicly refuted (Prop 5.11). |
| 13 | Hilton (via 2310.01923v1) | N∞ Latin squares for large n | Resolved (Thm 1.1). |
| 14 | Ai–Gutin–Lei–Yeo–Zhou 2407.17051v1 Conj 5.1 | converse-invariant tree orientations | Retired in lane r65. Refuted by Afonso–Colucci–Naia arXiv:2606.24739. |
| 15 | Cooper–Hyatt 2501.02331v1 Question 1 | Ψ(A) for non-Desarguesian affine planes | Reject: open-ended "what is", with no universal finite claim. |
| 16 | Hennecart–Perry 2208.07738v1 Conj 3.1 | quiver analogue of Higman | Reject: generalizes Higman's conjecture (famous). |
| 17 | Sundaram (via 2412.20894v1 Thm 1.8) | invariant vector for n-cycles | Proved (Swanson). |
| 18 | Ueltzen 2411.17362v1 | equality cases of inducibility ≤ 1/e | Answered in the source. |
| 19 | Wilf (2209.05803v1, 2306.14034v2) | Wilf's conjecture | Famous; reject. |
| 20 | Gregor–Hoang–Merino–Mička 2405.01863v2 | strong Lovász conjecture for Cayley graphs | Famous; reject. |
| 21 | Boege–Selover–Zubkov 2407.17826v4 Conj 5.1 | admissible principal-minor sign vector | Parked. Not screened beyond the statement; a 5×5 real-algebraic question. |
| 22 | Satake 2502.12090v2 | via Hardy–Littlewood F | Reject: famous number-theoretic conjecture. |

All sources are https://arxiv.org/abs/<id> with the frozen bytes listed in `http.jsonl`. Rows 4–22 are compact by design.
