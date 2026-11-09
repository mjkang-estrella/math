# Deterministic two-sided subset-sum averaging

This is author supporting algebra, not a solution or contribution verdict. It explicitly adapts the stipulated source sampler's pairwise averaging and potential-square identities. The additional choice is a positive potential on a two-sided bad set; no new source estimate is asserted.

Let H be a finite abelian group, 0<=g<=M, mean mu, eta>0. Fix k,j positive integers, and suppose

 beta := 2^(-k) E(g-mu)^2 / eta^2 < 1.

There exist k+j shifts so that their full Boolean average A satisfies

 sup_x |A(x)-mu| <= eta + M [sqrt(beta)/theta + log|H|/(theta 2^j)],
 theta = (1/2)log(1/beta).

If variance is zero the conclusion is immediate with zero error. Otherwise the source's pairwise-independence identity gives expected spatial mean-square error of the first k shifts exactly 2^(-k) Var(g). Therefore SOME first k shifts have two-sided bad set B={|A_k-mu|>eta} of density at most beta. This selection asserts existence, not high success probability.

For subsequent shifts put N_0=1_B and N_(l+1)(x)=N_l(x)+N_l(x-w). With Phi_l=E_x exp(theta N_l(x)), a uniform fresh shift satisfies E_w Phi_(l+1)=Phi_l^2. Select a minimizing shift, so Phi_(l+1)<=Phi_l^2. Induction gives log Phi_j<=2^j log Phi_0. Since Phi_0=1+|B|/|H| (exp(theta)-1)<=1+sqrt(beta), log Phi_0<=sqrt(beta). The summand at x yields

 N_j(x)/2^j <= sqrt(beta)/theta + log|H|/(theta 2^j).

Each good summand differs from mu by at most eta; every bad summand differs by at most M (both A_k and mu lie in [0,M]). Averaging proves the bound. Every selection is over the finite group, so existence is exact and requires no measurable selection or algorithmic oracle.

In the source regime log|H|<=b^4, M<=exp(b^.65), mu in[1/2,2], s>=b^.69, set k=floor(s/2), j=s-k, eta=b^(-.1)mu. Then beta<=4b^.2 exp(2b^.65)2^(-k). For sufficiently large absolute b, theta>=c s and both remainder terms multiplied by M are o(b^(-.1)). Thus the same scale permits deterministic two-sided uniform averaging with error at most 2b^(-.1)mu. This is not the source's quantitative high-probability conclusion.

For N functions bounded by M, with individual variance bounds, the same proof uses the UNION of their first-stage bad sets. The expected union density is at most 2^(-k) sum_a Var(g_a)/eta_a^2. Once this is <1, the common positive-potential choices work for every function. Thus log N=o(s) can be absorbed in the displayed source regime; arbitrary exp(b^4) families cannot be inserted without further analysis. Arbitrary base-point offsets are harmless because the final conclusion is uniform in x.

Remaining full-target debts: this averages bounded functions, whereas lattice overlap counts need upper-tail/size control for all original sections and ALL vertical lattice points. The source covers using selected inner section bodies and retained branches only. Neither a bound on selected weights nor this lemma bounds contributions from discarded branches. Its completion dilation may also create exponential peak overlap (see completion-obstruction.md). No passage from this finite sampler to thin lattice coverage is claimed.
