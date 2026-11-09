# Candidate 381433: cyclic Latin-square graph of order 6

Unaccepted candidate; no novelty clearance or full Lean endpoint yet.

Let V=Z6×Z6. Distinct (i,j),(i',j') are adjacent iff i=i', j=j', or i+j=i'+j' in Z6. Translation by any (a,b) is a graph automorphism, so a calculation at (0,0) suffices for all vertices. Every vertex has degree 15; no isolated vertices.

Let B be the 18 by 36 incidence matrix for the 6 rows, 6 columns, and 6 symbols. Two distinct cells share at most one line, so A=BᵀB−3I. Thus every real eigenvalue of A or any principal submatrix is at least −3. The nonzero vector z in latin36-certificate.json is supported outside N(0,0) and satisfies Bz=0, by exact rational arithmetic. It supplies eigenvalue −3 both globally and after deleting N(0,0). Translation gives the same after every neighborhood deletion. Thus all least eigenvalues are exactly −3.

For any real x (in particular any nonnegative x), put y=Bx. Since every cell lies in three lines, sum y=3 sum x. The source's quadratic objective at τ=3 equals

2 sum x − (1/3) xᵀ Bᵀ B x = (1/3) sum_lines (2y_l−y_l²) ≤ 18/3 = 6.

The uniform x=1/6 attains 6 globally. The nonnegative rational x in latin36-certificate.json satisfies Bx=1 and vanishes on N(0,0), so it attains 6 on the induced deletion graph. Thus υ(G)=υ(G−N(v))=6 for every vertex v. Both υ and λmin are integers. This proves G is adverse in the source's precise open-neighborhood sense.

An independent set has at most one cell in each row, column and symbol. If it had size 6, it would occupy each exactly once. The sum of the row residues and column residues is 2(0+1+2+3+4+5)=30 ≡ 0 mod 6, whereas the sum of the symbol residues would be 15 ≡ 3 mod 6. Contradiction. Therefore α(G)≤5<6=υ(G), and G is not a Q-graph. A size-5 independent set can be found, but is unnecessary for the refutation.

This is a candidate exact counterexample to Conjecture 4.2 of arXiv:1811.05516, not a claim about recognition complexity. The parity obstruction to a transversal in an even cyclic Latin square is classical and is explicitly uncredited. The proposed new content is its combination with exact neighborhood spectral and quadratic certificates to refute adversity-implies-Q. Whether this is already known or routine remains a material qualification question. The source survey does not discuss Latin squares in the inspected body; its cited foundational papers have not yet been read for this construction.
