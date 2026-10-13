# I312 parent note — a rank budget for graded constructions

2026-10-13. **Technical obstruction, not a substantial acceptance.** The next proposed research target is an actual amplification gap C_2(A)<2=C_3(A), where C_k is the disk-bounded k by k polynomial evaluation supremum. No such matrix has been constructed here. Thirteen findings remain accepted.

Consider orthogonal spaces H3,H2,H1,H0 with dimensions m,m+1,m+1,m, m>=1, and the grade-raising nilpotent matrix

    A = [[0,B3,0,0],[0,0,B2,0],[0,0,0,B1],[0,0,0,0]].

Thus B3:H2->H3, B2:H1->H2, B1:H0->H1. In the bipartition (H3,H1 | H2,H0), Re A has off-diagonal block

    C = (1/2)[[B3,0],[B2*,B1]].

Suppose

    CC* = I - DD*

for a matrix D with 2m+1 rows and d columns. This condition implies ||C||<=1. Grading conjugation rotates A by an arbitrary unit complex scalar, so w(A)=||Re A||=||C||<=1.

Write D3 for the m by d block of D corresponding to H3. The upper left block of the identity is

    B3 B3*/4 = I_m - D3 D3*.

If rank(D3)<m, choose a unit v in ker D3*. The identity gives B3 B3*v=4v, hence ||B3||=2. The inequality ||B3||<=2 follows from ||C||<=1, so this is exact equality. Since B3 is a compression of A, ||A||>=2; numerical radius gives the reverse bound ||A||<=2w(A)<=2. Consequently ||A||=2 and the scalar polynomial z itself attains the complete upper bound. Therefore C_1(A)=C_k(A)=2 for every k>=1, using the stipulated complete bound. Such a construction cannot meet the proposed amplification target.

In particular d<m is impossible for a genuine gap. More precisely, avoiding this scalar extremizer requires D3 to have full row rank, whether or not D has redundant columns. Applied to the rank-one-defect ansatz CC*=I-aa*, every m>=2 fails. The m=1 obstruction does not apply to R019's six-dimensional construction. Taking a rank-two defect when m=2 avoids this necessary obstruction only; it does not prove that any suitable A exists or that any level-three polynomial attains two.

This observation prevents a naive enlargement of R019's rank-one support defect from masquerading as a higher amplification example. It is elementary block algebra, not a new substantial theorem, and is not submitted as an extra acceptance.

The parent separately read Davidson–Paulsen–Woerdeman, [Complete spectral sets and numerical range](https://www.math.uwaterloo.ca/~krdavids/Preprints/DPWnum_range.pdf), web-extracted lines 0–527. Theorem 2.3 relates complete operator and numerical-radius norms; its converse builds a test at twice the starting matrix level. It does not state a bound of two on the required amplification level. This is a scope observation, not an inference that a higher-level example exists. No raw PDF hash or image inspection is claimed. The arXiv HTML v2 retrieval returned 404. The research brief asks for fresh verification of any further dependency.

Next work: [I312 prepared research brief](iteration312-amplification-hierarchy-standard-brief.md). No task has yet been launched because three earlier reviews are active.
