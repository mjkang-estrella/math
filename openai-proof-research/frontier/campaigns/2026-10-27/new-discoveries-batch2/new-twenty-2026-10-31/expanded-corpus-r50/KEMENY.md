# 356733: independently rediscovered, already publicly refuted

This note preserves the attempt, not a new discovery. Exact target: Albright et al. arXiv2211.01495v2, Section2 perturbation A(t)=A+t(E_uv+E_vu), Section3 K=sum of reciprocal nonzero normalized-Laplacian eigenvalues, Conjecture3.5 p19. Degrees change with t. The path's own O(n^3) growth assertion is not negated.

Take vertices0..10, path edges(i,i+1), plus(0,2),(8,10). This is two triangles joined by a path; it is simple and connected. Add the missing edge(0,9) with weight t. The exact weighted-resistance expression gives

    K_B(t) = (1475 t²+12102 t+4077)/(3(t+12)(22t+3)).

For path P11 with endpoint chord(0,10),

    K_P(t) = 5(67 t²+350 t+67)/((t+10)(10t+1)).

Both denominators are nonzero around0. Their derivatives are respectively -24181/144 and -3267/20, with positive difference3293/720 in the path-minus-barbell order.

Ordinary semantic bridge: for a connected finite weighted graph with positive degrees d and symmetric adjacency A, write L=diag(d)-A, J=11⁻¹11ᵀ, B=(L+J)⁻¹-J, and R_ij=B_ii+B_jj-2B_ij. Then K=dᵀRd/(2sum(d)). The normalized Laplacian is similar to D⁻¹L. On the complement of its stationary zero mode, the trace of the inverse is the reciprocal-nonzero-eigenvalue sum. Projecting B to this complement gives that trace equal to trace(DB)-dᵀBd/sum(d), which expands to the resistance expression. Invertibility follows from connectedness and the energy identity xᵀLx=sum_edges w_ij(x_i-x_j)². For t>=0 this is a genuine weighted graph; the rational functions extend differentiably to a neighborhood of0, giving the same right derivative.

The rational inverse method is reproduced by `exact_kemeny.py`. Independent verification via hitting times avoids reliance on that resistance calculation: for target j, delete j from P(t)=D(t)⁻¹A(t), and solve

    (I-Q_j) h_j = 1,
    (I-Q_j) h'_j = Q'_j h_j.

At t=0 these inverses exist: connected finite chains hit j with a geometric tail, since within10 steps there is uniformly positive probability of following a simple path to j. First-step conditioning uniquely identifies h with actual expected hitting time; the convergent inverse is differentiable under the rational perturbation. With pi=d/sum(d), differentiating H pi gives H'pi+Hpi'. `hitting-certificate.json` supplies all rational H,H',pi,pi' entries, and `hitting_check.py` verifies the values for all11 starting states. These exact scripts are ordinary reproducible algebra certificates, not Lean-certified semantics. They make no claim about minimal counterexample order.

Decisive prior: the complete earlier Omega scoped trees already list `D5/S3/Combinatorics/SpectralGraph/AlbrightKemenyEdgeDerivativeRefutation.lean` (Git blob5a0f96f66bc72f0a2e12485d505fa763b19b61d6) and the matching Problems note (blobc78ddf065c806de2eb0b9d5e819ce630e4b4b262). Actual bodies retrieved through the immutable blob API are retained with decoded SHA256 receipts. The prior `claim` quantifies all connected simple graphs and compares genuine derivatives of spectral K against the endpoint-perturbed path. Its `result` negates exactly that proposition using an order23 barbell and spectral/grounded analytic bridges. Selected actual bridge bodies and the final proof were inspected; no upstream compilation or complete declaration/axiom audit was performed. The earlier inventory at e9b39… /13:06UTC predates this attempt. A smaller instance of this same refutation is not a new eligible family. STOP; zero credit.

Without that prior exclusion a literal local Lean development would still require proving the normalized-spectral/grounded-trace identity, rational inverse update and all finite matrix certificates; no surrogate derivative formula theorem would suffice. None is claimed here.
