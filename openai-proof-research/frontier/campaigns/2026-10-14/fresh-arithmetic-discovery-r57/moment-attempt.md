# Weaker moment route, with homogeneous residues retained

This continues the exact T191V56 scope copied byte-for-byte from r56. No new target or weaker substitute is frozen. All results below are support for an unresolved attempt, not a nominee.

## Parameter order and the estimate actually needed

Fix odd d, then the norm encoding fixes k=k(d), then take r to infinity. Put L=r^A with fixed positive integer A and B comparable, with k-dependent constants, to L^4. The proposed sufficient estimate on the unit-second-pivot stratum is

    Pr(D=1,E>=B^j | the four labels)
       <= C_k^j L^(-4j) r^u,     1<=j<=k,              (W)

where u is independent of k and the labels; constants may depend on k. The target is (W), not the unnecessary five-coordinate estimate mentioned in r56. Tail summation gives E[E 1_(D=1)|labels] <<_k 1+r^u, because B/L^4 is bounded by a constant depending only on k and there are only k terms. No limiting assertion uniform in k is needed.

If the analogous full DE moment, FD4, and all singular estimates were also available, the r56 alteration has normalized expected bad-quadruple contribution

    <<_k (log r)^O(1) r^(3+4A+u-d).

Thus d>4A+u+3 suffices for this part. Since k is an enormous function of d, a bound with u=4k does not fit this hierarchy. A bound whose r exponent is merely renamed a k-dependent constant is not (W). The other requirements remain even if (W) is proved.

## A rigorously available first-layer saving

The primary lead was supplied by parent. Ghosal–Goenka–Keevash, Theorem 2.1 and Proposition 1.9, give O(L^8 log(2L)) integer 4x4 matrices of rank at most two in [-L,L], crediting Katznelson's fixed-rank theorem. Their actual reduction and proof of Proposition 1.9 were read. This is a standard input, not new work. Attempts to retrieve Katznelson's original AMS PDF returned 403; no original-proof reading is claimed.

Let Q=L/r. Conditional on any label configuration, the sixteen constant digits are independent, each with exactly Q possible values. If D=1 and E>=B then all 3x3 minors of the constant coefficient matrix vanish as INTEGERS: their absolute values are <B, so congruence zero modulo B implies equality. Therefore, by discarding the residue constraints only in the numerator of the count,

    Pr(D=1,E>=B | labels) <= C r^16 L^(-8) log(2L).   (1)

This is genuinely uniform over all prescribed residue classes; no equidistribution is assumed. On a specified unit 2x2 pivot, the source Schur recursion gives at most Q^(-4) at each further digit level. There are only finitely many pivot choices. Conditioning on the constant digits, and using (1), gives

    Pr(D=1,E>=B^j | labels)
      <= C log(2L) L^(-4j-4) r^(4j+12).              (2)

The pivot condition only concerns exposed entries. Each later Schur step conditions on twelve new coefficients and fixes at most one possible value for each of the other four, so the conditional bound is valid without independence of different layers.

For homogeneous zero residues, the constant matrix equals r times a matrix in [Q]^(4x4); homogeneity permits the stronger first count O(Q^8 log(2Q)). Hence in this case

    Pr(D=1,E>=B^j | zero residues)
      <= C log(2Q) Q^(-4j-4).                        (3)

The gains (2) and (3) pay only a fixed number of r powers once L=r^A is substituted. At j comparable to k they retain a growing exponent 4j. They therefore do not establish (W). This is the exact limitation of combining the classical first-layer count with the existing recursion.

## Why one cannot apply the integer-rank count at every layer

Over Q[Y], consider

    A(Y) = [[I_2, Y I_2], [Y I_2, Y^2 I_2]]
         = [I_2;Y I_2] [I_2,Y I_2].

It has rank two, whereas its coefficient of Y, [[0,I_2],[I_2,0]], has rank four. This is an exact obstruction to treating each coefficient matrix as an independent rank-two integer matrix.

It survives positive digits and homogeneous zero residue classes. Choose fixed 4x4 positive integer invertible matrices P and Q0, for example a positive Vandermonde matrix and its transpose. All three matrices P A_i Q0 (i=0,1,2) are strictly positive, since each A_i is nonnegative and nonzero. Multiply A(Y) by 1+Y+...+Y^(k-1), truncate modulo Y^k, and conjugate on the two sides by P,Q0. Every coefficient is strictly positive. For k>=2, the coefficient of Y is P(A_0+A_1)Q0, which is invertible because [[I,I],[I,0]] is invertible. Multiply all coefficients by r. For sufficiently large L/r every digit lies in [1,L] and is congruent to zero modulo r. The matrix still has rank at most two modulo Y^k and a nonzero constant 2x2 minor, hence D=1 for sufficiently large B. This example does not contradict (W); it refutes the attempted coefficientwise use of the first-layer theorem.

## A precise obstruction to uniform stepwise removal of r^4

Fix a strictly positive integer matrix M of rank two with a nonzero 2x2 minor, for example P A_0 Q0 above. Its rational tangent space T_M to rank-at-most-two matrices is

    T_M = {Z: alpha^T Z beta=0 for every
                 alpha in ker(M^T), beta in ker(M)}.

It is a rational linear subspace of dimension 12 and contains M, a strictly positive point. Thus there are constants c_M,C_M>0 such that the number of integer matrices Z in T_M with all entries in [1,Q] lies between c_M Q^12 and C_M Q^12 for all sufficiently large Q. For the lower bound, take twelve independent integral tangent vectors, center a sufficiently small box of their coefficients around a positive multiple of M, and count lattice points in that box. For the upper bound, select twelve coordinate entries that injectively parametrize T_M and bound each by Q.

Condition the constant digit matrix to equal rM and take homogeneous zero residue classes for the next level. For C(Y)=rM+rZY modulo Y^2, all 3x3 minors vanish modulo Y^2 exactly when Z belongs to T_M: their constant terms vanish, and their linear coefficients are the differentials of the minors. A nonzero constant 2x2 minor makes these tangent equations sufficient as well as necessary. Carry-free minors turn this into E>=B^2 in the actual base-B construction.

There are Q^16 equally likely next coefficient matrices, so the probability of a successful next step, under this legitimate exposed history, is Theta_M(Q^(-4))=Theta_M(r^4 L^(-4)). Therefore no bound C_k L^(-4), uniform over all exposed histories and independent of r, can replace the source's stepwise Q^(-4) estimate. Such histories may be very rare; the example does NOT refute the global averaged bound (W). It proves that any repair must count whole histories, retaining the cost of their pivot lattices or denominators. A new independent per-digit uniformity assertion is false.

Homogeneous zero residues are treated here as a rigorous stress test for the general digit lemma, not asserted to be an entire actual norm-label configuration. Actual norm prescriptions include nonzero designated residues. Bounds (1) and (2) hold for every actual label configuration. The homogeneous examples show why a proof claiming arbitrary-residue, arbitrary-history uniformity would be invalid.
