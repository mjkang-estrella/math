# 333709: proposed finite refutation, held for Lean completion

**Verdict: strong computational lead; not accepted and not yet a literal Lean refutation.**

The candidate is the Desarguesian projective plane PG(2,5), with infection rate 5. The proposed result is that no inclusion-minimal percolating point set has percolation time exactly 2. This contradicts Gerbner–Keszegh–Mészáros–Patkós–Vizer, arXiv:1608.00531v1, Conjecture 20, and the reserved MathDB 333709 statement. It uses an interior allowed parameter, 4 <= 5 <= 5, rather than a wording or domain correction. No credited campaign family supplies this obstruction.

Source definitions on PDF page 2 use synchronous infection rounds. “Minimal” means inclusion minimal, not minimum cardinality. The conjecture is on PDF page 14. The preceding Proposition 18 only supplies three-round constructions for r <= (q+7)/3, which at q=5 covers r <= 4. It does not supply this obstruction. No numerical verified range for Conjecture 20 was found in that section.

## Ordinary computer-assisted argument

Use the 31 normalized nonzero vectors

    (1,a,b), a,b in F_5; (0,1,a), a in F_5; (0,0,1)

for both point and line indices. A line indexed by u contains the points p with u dot p = 0 modulo 5. The resulting incidence masks are in outputs/percolation.json and lean/PlaneData.lean. They have 6 points per line, 6 lines per point, one common point per distinct line pair, and one common line per distinct point pair. The four points indexed 0,25,30,6 have no collinear triple.

A percolating set A is not contained in a line: if it were, every other line would meet the infected set in at most one point at every round, so infection could not leave that line. Hence A contains three noncollinear points. Their representative vectors are a basis of F_5^3. The inverse of their column matrix induces a projective automorphism sending those three points to indices 0,25,30. Projective automorphisms preserve incidence, infection rounds, percolation, and inclusion minimality. Consequently it is enough to consider sets containing these three fixed points.

Suppose A were inclusion minimal and percolated in exactly two rounds. For every v in A, let B_v be the closure of A minus v. It is closed and omits v: otherwise it contains A and therefore has full closure, contradicting minimality. If v is not in A, set B_v empty.

Encode Boolean variables A_p, P_p, I_l, J_l, and B_vp. Here P is the first-round set, I selects first-round infected lines, and J selects second-round infected lines. The CNF has 1085 variables and 7940 clauses, including the three normalization units.

* I_l implies at least 5 of the 6 points on l belong to A. J_l implies at least 5 belong to P. At least 5 of 6 is encoded by requiring every pair to contain a true variable.
* P_p is equivalent to A_p or an incident selected I_l.
* For every p, P_p or an incident J_l holds. Some P_p is false.
* If A_v, then B_vv is false and all A_p with p != v imply B_vp.
* Every B_v is closed: for each line, each 5-subset S of its 6 points and the remaining point p, the clause (OR_{u in S} not B_vu) OR B_vp holds.
* A_0, A_25, A_30 hold.

These clauses are satisfied by the hypothesized A, its actual first and second rounds, and the closure sets B_v. Thus UNSAT suffices to rule out A. No assumption about closure being achieved in only two rounds after a deletion is made: B_v is an arbitrary closed separator, so deletion minimality is unbounded and exact.

CaDiCaL returned UNSAT and emitted a 23,490,800-byte textual LRAT proof. scripts/check_lrat.py independently checked every addition using only reverse unit propagation and the input clauses. It ignored deletions, a sound monotone-database choice. All 106,465 additions passed; the last derives the empty clause. The dependency-trimmed proof has 82,646 additions and uses 4,400 input clauses. This establishes an ordinary reproducible computational certificate, subject to the correctness of the small Python checker and the stated model-completeness and symmetry arguments. It is not a kernel-checked certificate.

A separate 3-round inclusion-minimal witness is saved in outputs/percolation-three-round.json. Together with the proposed exclusion and the source's one-round impossibility, it suggests that t_5(PG(2,5)) = 3. That strengthened equality is not counted separately.

## Prior-art boundary

The current source remains arXiv v1. The live Lean Pool head is 01db1d7049cf9668bda1e9e106875ee1278b43e6; projects.yml and all candidates files were screened before the substantive SAT route. GitHub repository searches for source ID, conjecture keywords and authors with “lean” found no exact target proof in the inspected results. Current complete Omega D5 and Problems path listings and OpenAI preprints were also screened. Exact receipts and limitations are in outputs/registry-screen.json. Focused live literature searches found the source and its published bibliographic record, not a demonstrated earlier refutation. These bounded non-findings are not worldwide novelty clearance. The SIAM typeset body and every citing paper have not been audited.

## Remaining formal work

lean/PlaneData.lean supplies literal plane data, exact source-semantics definitions, and only auxiliary finite checks. It does not assert TargetNegationOnThisPlane. No sorry, admit, added axioms, unsafe, native_decide or ofReduceBool was used.

The main formal gaps are:

1. Kernel replay of the 82,646-step RUP/LRAT certificate under the resource limits. Lean 4.34.1 includes Std.Tactic.BVDecide.LRAT.check_sound; use its proved checker, not bv_decide's compiled reduction axiom. Split replay into bounded pieces if necessary.
2. A proved semantic completeness bridge from InclusionMinimal and TwoRounds to the generated CNF, including closed deletion separators and the actual synchronous operator.
3. The projective-basis normalization theorem (or an unsymmetrized certificate).
4. Fresh strict extracted rebuild, module-specific leanchecker, transitive axiom audit, independent fidelity/novelty review, and root adjudication.

No full literal Lean endpoint, acceptance, minimal counterexample claim, universal odd-order theorem, or worldwide priority claim is made.
