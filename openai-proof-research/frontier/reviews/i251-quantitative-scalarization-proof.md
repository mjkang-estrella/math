# I251 — proof gate for quantitative complete-witness scalarization

**Verdict: PASS. No mathematical repairs required.**

Exact reviewed input: `frontier/experiments/i247_quantitative_complete_rigidity/analytic-attempt.md`, SHA256 `7d8b629513741abab53339c19bb05c9f611ecbd0af1b6ace3246dff8af0eae8b`. The positive verdict covers the completed Q1–Q4 theorem and the existence-only active reducing block extension. All pinned OpenAI results at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true. This review checks the new deductions and source contracts, not upstream truth.

Full reasoning, every constant, boundary limit, edge case and counterexample calculation are in [analysis.md](../experiments/i251_quantitative_scalarization_proof/analysis.md). [Reading record](../experiments/i251_quantitative_scalarization_proof/reading-and-failures.md), [source contracts](../sources/i251_quantitative_scalarization_proof/literature.md) and [authentication](../experiments/i251_quantitative_scalarization_proof/input-authentication.json) document exact extent and provenance.

## Result checked

For d>=2, K=W(A) subset R Dbar with interior, boundary spectral distance at least delta>0 and a regular analytic support arc of length at least ell with simple top eigenvalue gap at least g>0, set

    C0=8(d-1)R(3R)^(d-1)delta^(-d)[9pi R²/(g ell)+1/sqrt(6)].

For every finite coefficient size and finite-degree matrix polynomial P with max_K||P||=1 and gamma=||P[A]||>=2-epsilon, 0<=epsilon<=1/2, every maximal unit singular pair x=vec X,y=vec Y has squared Schmidt tails <=min(1,C0 sqrt(epsilon)). Its leading product factors give a scalar compression p=v*P u with max_K|p|<=1 and

    ||p(A)||>=gamma[1-t_X-t_Y-sqrt(t_X t_Y)]
             >=2-epsilon-6C0 sqrt(epsilon).

The product-vector distances in Q3 also hold. There is no dependence on degree, coefficient magnitudes or coefficient size.

## Why the proof passes

1. **Exact residual.** Reading the direct source's full relevant proof gives diagonal bounds D_X,D_Y<=4a²/gamma² and cross norm C=a²+3||X*Y||HS²+sum_{k>=1}||X*b_k(A)Y||HS². The positive block gives E_B=D_X+D_Y-2C>=0. Adding the three slacks and twice the extra cross terms yields exactly 2(4/gamma²-1)a². Thus E_B<=S and 6||X*Y||HS²<=S have the right constants, tensor convention and normalized measure.
2. **Boundary passage.** For fixed P and fixed singular vectors, use F_j=P/M_j on analytic outer approximations; gamma_j=gamma/M_j and M_j tends to 1. Convex exterior Herglotz formulas give |q_j|<=4cap(Omega_j) and strong boundary L² convergence via uniformly square-summable logarithmic Fourier tails. Uniform resolvent convergence away from the fixed interior spectrum gives R_j,H_j convergence. Expanding the quadratic trace passes E_B in L¹. No varying singular-vector limit, polynomial-degree compactness or uniform collar is assumed.
3. **Explicit constants.** ||A||<=2R and the determinant/singular-value identity imply ||(wI-A)^(-1)||<=(3R)^(d-1)delta^(-d), including nonnormal A and repeated eigenvalues. With |q|<=4R this gives a²<=16R²K0². The bound 2(4/gamma²-1)<=4epsilon gives sqrt(S)<=8RK0 sqrt(epsilon).
4. **Rank-deficient field and weighting.** The congruence C*HC=2|q|S_w and s_(d-1)(S_w^(1/2)C^(-1))>=sqrt(g)/||C|| give the least positive eigenvalue >=2|q|g/(9R²). Only the range is inverted. Arclength gives integral_I|q|²>=ell²/(4pi²); weighted averaging then gives hyperplane compression bound eta0=9pi R² sqrt(S)/(g ell), without a lower conformal-speed assumption. Infima at excluded endpoints are handled by a sequence and scalar limits.
5. **Quantitative inertia.** Interlacing bounds lambda_2(D) and lambda_2(-D). On the top two-dimensional spectral subspace of XX*, a unit vector has a preimage under X of norm <=1/sqrt(a2), so a2-kappa²/a2<=eta0, where kappa=||X*Y||op. Hence a2<=eta0+kappa, and similarly for YY*. Summing the smaller eigenvalues proves Q2, also for d=2.
6. **Quadratic scalar loss.** Writing best product vectors as x0=a x+e,y0=b y+f, both linear terms vanish by Tx=gamma y and T*y=gamma x. Therefore y0*T x0=gamma ab+f*T e and its real part has the stated bound. In base-first order, X0=xi u^T and Y0=eta v^T give y0*T x0=eta*(v*P u)(A)xi. There is no conjugation error and no top-singular-value simplicity assumption.
7. **Active block.** For a norm-attaining reducing block B, its local maximum obeys gamma/2<=M_B<=1. Its residual is 2(4M_B²/gamma²-1)a_B², bounded above by the full-normalized expression. The extracted p remains bounded on all W(A). This asserts existence of a channel, not control of all full-A singular pairs.

## Attacks, edge cases and limits

The Crabb chain calculation gives eigenvalues 1,1/2,-1/2,-1 for its supporting Hermitian matrix, support gap 1/2 and B³=2e1e4*, verifying nonvacuity. The shifted doubled-disk family has exactly gamma_t=(1+sqrt(1+t²))/(1+t), maximal superpositions with tails 1/2, and arc gap t cos(theta); it disproves a uniform every-pair estimate omitting g. Restricting to sufficiently small t keeps its deficit within the theorem's epsilon range. The weighted (1,2,1) chain disproves output square-zero rigidity and remains consistent with the extracted scalar input channel. Independent unused coefficients in diag(z,1) disprove whole-polynomial fixed rank-one approximation.

The proof also handles epsilon=0, m=1, reducible A satisfying the stated hypotheses, multiple top singular values, repeated ordinary eigenvalues, corners away from the supplied arc, and arbitrarily large finite degrees. When the lower scalar bound is negative it is simply uninformative; no nonzero scalar ratio is claimed then.

**No geometry verdict is implied:** disk proximity, optimal exponents/constants, global whole-P approximation, a support-gap-free every-pair estimate and classification of inactive summands are excluded. The original discovery's disk-rigidity objective remains unproved. No contribution/significance verdict, acceptance or count change is authorized here. The supplied accepted count remains ten, with a target of twenty and a separate contribution gate still required.

No subagents, live I248/I249/I250 or other live review reads, research code, tests, numerical experiments/scans, snapshots, shared edits, staging, commits, publication or external communications were used. Only the assigned review artifacts and fully read primary excerpts were written.
