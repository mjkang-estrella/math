# r66: Sra's full Macdonald principal-specialization comparison — unresolved

## Exact source and scope

Suvrit Sra, *Monotonicity of Turán-ratios of symmetric polynomials*, author-released v1, 7 October 2026, pp.7–10, Conjecture 4.1. Actual complete PDF and live author version page retrieved 29 October 2026 UTC. The live page lists v1 only; this is an authenticated author preprint, not a claim of journal publication. Source: https://suvrit.github.io/papers/sym-turan/sym-turan-v1.pdf . SHA256 and retrieval records are in provenance.json/http.jsonl.

For EVERY 0<q,t<1, integer n>=2 and partition lambda padded to n parts, put

A_j(x)=(x,xt,...,xt^(j-1),t^j,...,t^(n-1)),
C_j(x)=P_lambda(A_j(x);q,t), T_i(x)=C_i(x)^2/(C_(i-1)(x)C_(i+1)(x)).

The asserted conclusion is T_i'(x)>0 for EVERY x>1 and 1<=i<n if lambda_1>lambda_n. If lambda=(r^n), r>=0, the ratios are identically one. The common principal-specialization normalization in source Eq.(4.2) cancels. This lane has NOT proved or refuted that full statement. Only this one fresh attributed question was selected; no additional source outcomes are claimed.

The source already proves Theorem1.1 for Schur polynomials evaluated at repeated 1,x, Theorem4.3 at x=q^-1, Proposition4.4 near x=1, in n=2, and at infinity for single rows, plus lambda=(2) in the closing paragraph. These known cases are uncredited. Even q=t<1 is an aligned geometric alphabet, not the repeated-argument alphabet in Theorem1.1. A new proof of a finite set, a row family, or a reformulation would not settle the full source.

## Pre-investment registry and campaign screen

Read ancestor/batch AGENTS, NEXT's current entry, ledger and prior-campaign-context (complete JSON parsed; all 37 accepted scopes inventoried), r60–r63 SUMMARY files, r57 discovery warnings and root-polyomino57-acceptance-r1/ACCEPTANCE-PRIOR-LIMITS.json. No accepted family, listed exhausted target, r64 arithmetic or r65 finite/optimization target was pursued. This lane is symmetric-function analysis with a basic-hypergeometric route; it does not duplicate Kalmykov–Karp shift-Turán questions.

Before branch experiments, screened cached Omega Problems paths and an ACTUAL older D5 Lean tree. r57 omega-D5.json was deliberately NOT treated as actual Lean. No Macdonald/Turán-ratio matching path appeared in these bounded inventories. The two Sra-named Problems entries concern reciprocal permanent Lorentzian membership and symmetric alpha-permanent log-supermodularity. Their actual immutable .lean bodies, claims and endpoint proofs were fetched and read: one uses a positive 5x5 inverse-M matrix and a Hessian positive two-plane; the other a symmetric 4x4 inverse-M matrix and alpha^2(alpha+1)(2401alpha^2+1617alpha-16). Neither states a theorem about P_lambda(A_j(x)). No conversion of either into the selected monotonicity theorem was found. They were examined for subsumption, not nominated as fresh targets.

Both were fetched at latest OBSERVED Omega revision 6c27b0a84f560fa3e43d128d8a7f9e5f247e0be3. This is NOT certified current HEAD. Inherited API403 is respected: no retry or alternate-host HEAD acquisition. Inspected prior access records/acceptance limits provide no usable reset clearance. Current-registry freshness remains HOLD; lexical absence is not novelty clearance. Search queries for the exact conjecture name and sym-turan found the primary author release, no complete resolution in the bounded retrieved results. No exhaustive or worldwide claim.

## Closest primary theorem bridge checked

Lascoux–Warnaar, AAM46(2011)424–456, actual published author-hosted PDF, pp.426–427, Eqs.(1.6)–(1.8), gives the exact Macdonald branching rule. This supplies polynomial coefficients, not monotonicity. Source definition and the arm/leg product yield positive weights for 0<q,t<1. It is credited machinery, not a discovery.

Shimazaki, arXiv:2609.21431v3 (PDF dated 19 October2026; live history saved), actual Theorems2.2,3.2,3.3,4.4 and Lemma4.3/proofs read. Theorem4.4 varies a partition (m^g,mu) and proves negative separated zeros for a generating polynomial of evaluations at the SINGLE principal alphabet t^n. Sra's evaluation duality instead needs P_(k^j)(y_lambda)/P_(k^j)(t^n) with y_lambda=(q^-lambda_1,q^-lambda_2 t,...). For n3,lambda=(3,1,0),q=1/3,t=2/3 this is (27,2,4/9); its adjacent ratios are 2/27 and 2/9, so it is not even a scalar geometric alphabet, much less the required principal t-alphabet. Thus direct substitution into Shimazaki4.4 is invalid. No complete positivity-preserving transfer to arbitrary y_lambda or interpolation to all real x was proved. This is a precise failed direct bridge, not a claim that all possible consequences of Shimazaki are excluded.

Sra4.3's first q-step does not provide derivative positivity between steps. Even all discrete q-steps would not prove the required continuous monotonicity without an additional theorem. Neither shortness nor an unprinted endpoint is used as a novelty or routine-exclusion argument.

## Route 1: positive branching and tilted degree distributions

For every polynomial with positive monomial coefficients p_e, specialize exactly:

C_i(x)=sum_e p_e t^(sum_r (r-1)e_r) x^(e_1+...+e_i).

At x=exp(s), let K_i=e_1+...+e_i under the probability distribution proportional to those positive terms. Then

d/ds log T_i(exp(s))=2 E_i[K_i]-E_(i-1)[K_(i-1)]-E_(i+1)[K_(i+1)].

This identity is exact. A uniform nonnegative second difference of these DIFFERENT tilted distributions, strict off rectangular partitions, would solve the full target. Branching alone does not supply this inequality; we did not assume a coupling or differentiate an inequality without justification.

In fact arbitrary positive symmetric homogeneous coefficients are insufficient. Take F(z)=z1^3+z2^3+z3^3+1000z1z2z3, t=1/10 and i=2. Its aligned specializations are

C0=2001001/1000000,
C1=x^3+x+1001/1000000,
C2=(1001/1000)x^3+x^2+1/1000000,
C3=C0*x^3.

At x=11/10, exact substitution yields

x(d/dx)log(C2^2/(C1*C3))=-331808845/7206240054<0.

This is an exact obstruction to the weakened positive-symmetric-polynomial route. F is NOT asserted to be a Macdonald polynomial, hence this is NOT a counterexample to Sra4.1 and earns no credit. A uniform invariant must use more of the Macdonald branching coefficients.

## Route 2: cleared derivative coefficients

Let a=C_(i-1), b=C_i, c=C_(i+1), all positive on x>0. The full target is exactly positivity on x>1 of

N_i(x)=2b'(x)a(x)c(x)-b(x)(a'(x)c(x)+a(x)c'(x)).

For each actual branching specialization one can compute N_i(1+y). Coefficientwise nonnegativity and one strictly positive coefficient would suffice. All381 tested rational cases have nonnegative shifted coefficients. However no proof holds uniformly in n,lambda,q,t, and the coefficients are coupled signed convolutions. This finite sufficient-invariant success is not a theorem. The unresolved precise gap is a uniform inequality for these signed convolutions, or a weaker all-y positivity argument using actual branching weights. One negative shifted coefficient falsifies this proposed invariant but need not refute the source; N_i(x)<=0 at an admissible x does refute the source.

## Route 3: differential maximum principle

Sra's Schur proof uses f_i''(s)=i(n-i)/(4sinh(s/2)^2)(1-exp(-u_i(s))), then a cooperative linear system for u_i'. Importing this identity to the aligned alphabet fails already for genuine lambda=(1),n3,t=1/2 (any q). With x=exp(s)=2, i=1, C0=7/4,C1=x+3/4,C2=3x/2+1/4:

f1''=24/121, whereas the displayed Schur-Toda right side is 120/121.

The exact residual is -96/121. Thus the published differential system cannot simply be reused with changed C_i; a valid deformation and a new sign principle are required. This is a route obstruction, not a refutation of monotonicity, which is true for this known low-degree case.

## Bounded validation and retained failures

Run `sh run.sh` in this lane. Each Python child runs with AS512MiB, process-group RSS512MiB, CPU210s, wall230s, 40ms group sampling, BLAS/OMP/MKL/NumExpr1. No limits increased. Network acquisition is separate and logged; rerunning checks is offline.

- Float branching exploration:108625 derivative signs, n2..5,totaldegree<=10, q,t in {.01,.1,.5,.9,.99}, x in {1.001,1.1,2,10,100}: no negative beyond the stated numeric tolerance. Pure evidence.
- Exact rational exploration:1143 derivative signs, n2..4,degree<=6, (q,t)=(1/3,2/3),(2/3,1/3),(1/2,1/2), x=11/10,2,10: strict positivity in tested nonrectangular cases. The checker records any negative; zeros are not a universal argument.
-171 exact independent Macdonald eigenoperator identities at distinct integer arguments;216 independent one-row coefficient arrays against Sra4.8 plus Q/P normalization;63 independent Schur determinant values;381 exact shifted-N tests. All pass. These are validation, not a full coefficient-formula proof or source theorem.
-1448 isolated monomial-orbit tests found no generic counterexample, but the subsequent18-test mixture search found the exact positive-symmetric obstruction above. The standalone obstructions.py recomputes both rational obstructions without the branching engine.

Initial coefficient builder overwrote rather than added contributions from different interlacing partitions. Its cyclic-symmetry assertion failed; original/diagnostic failure logs retained. Corrected builder adds contributions and passes symmetry, eigenoperator, Schur and one-row checks. Initial audit patch shadowed the b arm/leg function with a local coefficient array; TypeError retained and corrected. No failed run is passed off as a mathematical counterexample. No resource-cap failure occurred.

## Disposition, strongest objection and next falsifier

UNRESOLVED / lanecredit0. Strongest objection to advancement is the missing ALL-PARTITION sign theorem, not merely source access. There is no complete ordinary proof or source counterexample, so no PROOF.md, Lean, formal investment, paper or nomination. FreshnessHOLD independently remains. Root alone can accept; counts remain7 additional/37total.

A useful continuation must prove a Macdonald-specific tilted-prefix comparison or uniform cleared-N positivity, or produce an admissible exact negative derivative. Larger positive grids alone would not close any gap. The positive-symmetric mixture failure blocks an otherwise tempting overgeneralized induction. A primary theorem already asserting this exact tilted-prefix comparison would subsume the target and must be read before any further serious proof investment.
