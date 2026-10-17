# Correlated-root obstruction to copying the scalar comparison

Myeongjin Kang; no affiliation. Original prose CC BY 4.0. Not a counterexample to SOUP.

## An order-one missing term

For fixed observation times t_a, scale their differences by a parameter r>=0 and put C_ab(r)=exp(-r|t_a-t_b| n^(-2/3)). For the centered scaled free energies Y_a under that correlated disorder, define M_n(q;r)=E exp(sum_a q_a Y_a). Ordinary Gaussian covariance differentiation at positive r, followed by grad F_a dot grad F_b = beta² n/2 (<R_ab²>-1/n), gives

    d_r log M_n = -(beta²/2) sum_(a<b) |t_a-t_b| C_ab(r) q_a q_b
                              E_tilt[<R_ab²>-1/n].

The tilted expectation includes the disorder density proportional to exp(sum q_a Y_a), and conditionally independent Gibbs spins at each root. Finite n permits any real fixed q; source moment bounds give uniform local transform control when the sum of their absolute values is sufficiently small. Coincident times can be merged first.

Although 1-C_ab is O(n^(-2/3))=O(x^4), the gradient contraction before multiplication by d_r C_ab is O(n^(2/3)). The perturbation therefore need not vanish. Treating the correlated root block as an O(x^4) error without its derivative factor is invalid. Parent independently derives/checks the two-root specialization.

## The precise unpinning failure

Single-root scalar augmentation uses spin gauge symmetry to pin a terminal spin without changing the law of its free energy. The correlated joint Gaussian law is invariant under a COMMON spin gauge, not arbitrary independent gauges at its roots. The common gauge is not transitive on tuples of spins: their coordinatewise relative spin is preserved.

Already for n=2, put a=beta/sqrt(2), let (G,H) be standard Gaussians with correlation 0<c<1, and let eta_j be the spin product sigma_1^j sigma_2^j. The probability of one fixed spin configuration at root j is (1+eta_j tanh(a G_j))/4. The probability of pinning a pair of configurations is

    (1/16) [1+eta_1 eta_2 E(tanh(aG)tanh(aH))].

The single-tanh terms vanish by simultaneous Gaussian sign symmetry. The cross expectation is strictly positive: condition on |G|=u,|H|=v; the sign-product mean is tanh(cuv/(1-c²))>0. It is not a constant conditional on the two free energies. Indeed these free energies determine u,v, and the conditional pin weight is

    (1/16)[1+eta_1 eta_2 tanh(au)tanh(av)tanh(cuv/(1-c²))].

This is nonconstant in u,v. Thus pinning both roots genuinely changes their joint free-energy law. This calculation invalidates that verbatim multi-root augmentation argument; it neither refutes joint log-concavity by other means nor refutes SOUP.

Marginal Holder DOES give bounded local Lp tilted densities and tightness. It does not supply the deterministic cross-overlap center needed in the source coefficient cancellation.

## Source interfaces actually read

Main limiting-law manuscript sections 02-foundations: the positive tree law has independent normalized branches conditional on their prefix. Equation A4 explicitly states independent roots for distinct active components. The masked overlap identity relies on independent component sign flips. These are assertions about that law, not a theorem for arbitrary correlated quenched roots.

04-reduction prop:increment and full augmentation proof: the stopped increment is scalar; the proof uses a single-pin gauge invariance and explicitly retains independent roots. 11-companion-interface (whole section): optimized comparisons retain a fixed positive matrix margin, normalized conditional future kernels, and common prelimit base.

09-expansion lines1-225: the polynomial E1 uses a common deterministic untilted S_v and scalar q(v), then sums signed coefficients before estimating. The centered allocation argument removes an unobserved child whose future kernel integrates to one, retaining a marginal independent of the moving fork. Correlated external roots cannot silently be inserted as unaffected exterior data: conditioning on them changes that future's Gaussian law. A new normalization/centering calculation is needed.

No argument here proves such a calculation impossible. The full SOUP target remains unchanged and unpaid.
