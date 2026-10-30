# REJECTED FOR NOVELTY: see STATUS.md

# Exact candidate refutation of Lin Conjecture4.3

MathDB332939, Lin arXiv1604.04141v1 Conjecture4.3 p6 asks, for all positive semidefinite n-by-n matrices A,B and every p>0,

lambda(A^2+|BA|^p) majorizes lambda(A^2+|AB|^p).

Here |X|=(X*X)^(1/2); lambda is sorted decreasing, counted with multiplicities. Credit0: independent prior-art review found a pre-existing public refutation; further formal/paper/packet work stopped. The already-proved determinant statement is not contradicted.

Use the rational A,B,Q,D in lin-rational-svd.json (also formal/SourceDefs.lean). A is strictly positive, B is positive semidefinite of rank2 (explicit positive two-by-two block and zero last row/column). Q is orthogonal; AB=QD and BA=DQ^T. Therefore |AB|=D and |BA|=QDQ^T by uniqueness of the positive square root. All entries are real rational, hence also literal complex matrices satisfying the source hypotheses.

At p=3 write L=A^2+QD^3Q^T and R=A^2+D^3. Their traces agree. Put tau=197/500. The leading principal minors of L-tauI are
164962021007737/231238250510400,
16944916580133891169/453226971000384000000,
78544752135078542548579/235692188263043442000000000,
all strictly positive. Thus L-tauI is positive definite, so every eigenvalue of L is greater than tau.

For v=(-19/100,-1,37/50),
v^T(R-tauI)v=-137006877457/21744240000000<0.
Thus the smallest eigenvalue of R is less than tau. Consequently lambda_min(L)>lambda_min(R). Equal traces now give lambda_1(L)+lambda_2(L)<lambda_1(R)+lambda_2(R), violating the k=2 majorization inequality.

Exact LDL factorizations will certify positivity in Lean over the literal complex matrices, with no eigenvalue approximation or imported symbolic certificate. The sign and trace steps use actual Hermitian eigenvalues and the real functional calculus powers. No minimal dimension/exponent/optimality claims are made; one combined counterexample only.

Source and bounded-novelty investigation: root sources preserved in ../parent-matrix-screen-r5/sources. Ghabries2022 thesis Remark2.5p50 still asks the exact eigenmajorization, whereas its preceding theorem settles only determinants for all p. The 15 indexed citing works and count-ex-machina repository are under independent review. In particular, root ghabries-thesis.pdf is an HTML access-failure payload, not a PDF; relevant author-uploaded primary body was read through ResearchGate. No novelty PASS or priority claim yet.
