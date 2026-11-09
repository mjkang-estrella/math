# A candidate refutation of the adverse-graph conjecture

This note describes the statement proved by the accompanying Lean source. It makes no claim of novelty clearance or campaign acceptance.

Let V = Z/6Z × Z/6Z. Join distinct cells when their rows, columns, or symbols i + j coincide. Let B be the 18 by 36 incidence matrix of the six rows, six columns, and six symbols. Every cell belongs to three lines. Distinct cells share at most one line, so A = BᵀB − 3I.

For every real vector z, zᵀAz = ‖Bz‖² − 3‖z‖². Every adjacency eigenvalue is therefore at least −3. The same identity holds after restricting columns to any induced vertex set. The supplied rational kernel vector is nonzero, vanishes on N((0,0)), and satisfies Bz = 0. At every base v, translate its coordinates by v. The 36 resulting vectors have the same three properties relative to N(v); these facts are separately checked in Lean. Restricting a vector to V \ N(v) gives a nonzero adjacency eigenvector at −3. The full graph and all these induced graphs consequently have attained least eigenvalue −3.

Write y = Bx, also for a restricted column matrix. With τ = −λmin = 3, equation (11)'s objective is

    2 Σ x − xᵀ(A/3 + I)x
      = (1/3) Σ_lines (2y − y²)
      = 6 − (1/3) Σ_lines (y − 1)² ≤ 6.

Here Σ_lines y = 3 Σ x. The supplied rational fractional transversal, translated to each base, is nonnegative, vanishes on N(v), and has every line sum 1. Each identity is checked in Lean at all 36 bases. Thus it attains 6 both globally and after deletion, proving υ = 6 throughout. The original graph has no isolated vertices. Its least eigenvalue and υ are integral and unchanged after every open-neighbourhood deletion, exactly the definition of adversity.

An independent set contains at most one cell in each row, column, and symbol. Its cardinality is at most six. At cardinality six, all three coordinate images equal Z/6Z. The row and column sums are each 0 + 1 + 2 + 3 + 4 + 5 = 3 in Z/6Z. Their sum is 0, while the symbol sum must be 3. This contradicts symbol = row + column. Every independent set therefore has at most five cells. The cells (0,0), (1,1), (2,2), (3,4), (4,5) are independent, so α = 5.

It follows that this graph is adverse and not a Q-graph, since α = 5 < 6 = υ. The graph has an edge, so it refutes the survey's universally quantified statement even with its ambient edge hypothesis. The parity obstruction is classical; any potential novelty concerns the adverse-graph consequence, which remains subject to the inherited prior-art qualifications and independent review.

## Explicit witnesses and ordinary simplification

Coordinates are row-major, residues 0 to 5. The nonzero kernel entries are
z(1,2)=-1, z(1,3)=1, z(2,1)=1, z(2,3)=-1, z(3,1)=-1, z(3,2)=1.
All other entries are zero. Each row, column and symbol sum is zero; the
nonzero symbol residues are 3,4,5, each with opposite signs. All nonzero
entries avoid the open neighbourhood of (0,0). At base v use z(p-v).

The formal packet's fractional matrix is

    1  0   0   0   0   0
    0  1/4 0   3/4 0   0
    0  1/4 0   0   0   3/4
    0  1/4 3/4 0   0   0
    0  1/4 0   0   1/2 1/4
    0  0   1/4 1/4 1/2 0

Each line sum is one. Translate x(p-v) for any base v.
Alternatively, put 1 at the retained base, 1/4 at every other retained cell,
and zero on the deleted open neighbourhood. Lines through the base retain
only that cell; each other line retains four cells. Thus this second witness
also has line sums one. This simplification is ordinary proof only; the Lean
sources use the displayed inherited matrix and are unchanged.

The graph is noncomplete: (0,0),(1,1) are a distinct nonedge. Reviewer.lean,
explicitly reviewer-authored and hash-identical to the independent review,
proves the fully spelled-out stricter source restatement with this condition.
There are 21 retained vertices; the 18 by 21 incidence matrix also has a
nonzero kernel by dimension counting. Neither alternative changes the
formal endpoint or claims an extra discovery. Luz 2020 remains unread;
there is no priority claim and accepted credit is zero.
