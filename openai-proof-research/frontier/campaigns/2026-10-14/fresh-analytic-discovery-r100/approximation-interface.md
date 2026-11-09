# Passing a uniform smooth estimate to the full frozen density class

Paid source approximation plus a standard compactness transfer; supporting only.

Actual source approximation.tex was read in full. Lemma geo:approximation gives smooth strongly convex potentials with finite upper Hessian bounds, densities f_j converging in L1, means a_j and covariances C_j converging, and entropies h(f_j)->h(f). For an isotropic centered f, define X_j=C_j^(-1/2)(Y_j-a_j), Y_j~f_j. Then X_j is centered isotropic and remains smooth strongly log-concave with finite positive Hessian bounds (no uniform bounds are required).

The source's common exponential-tail domination proves convergence of second moments and weak convergence; hence W2(Law(X_j),f dx)->0. Entropy transforms by h(X_j)=h(f_j)-(1/2)log det C_j, so delta_j->delta.

Suppose the full frozen target has been proved for EVERY such smooth normalized law with the SAME dimension-independent C and without a small-deficit restriction. Pick U_j in O(m) attaining or approximating the infimum; compactness of O(m) permits a subsequence U_j->U for this fixed m. Coupling all exponential products to the same E gives W2(U_j(E-1),U(E-1))²<=||U_j-U||F². The triangle inequality passes the desired estimate to f. This use of fixed-m compactness does not manufacture a dimension-independent bound: that bound must already be uniform in the smooth theorem.

The same passage works for a small-deficit estimate only if the limiting deficit lies strictly within its proven threshold (or the proof separately handles the threshold). It cannot turn a small-deficit theorem into the all-deficit target. Thus approximation itself is now explicitly resolved conditional on the unchanged smooth theorem; global algebra and all-deficit extraction are the substantive outstanding steps.
