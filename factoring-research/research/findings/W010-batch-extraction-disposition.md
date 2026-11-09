# W010 batch-extraction parent disposition

2026-10-08. The complete [independent review](W010-batch-extraction-review.md)
has been read. The parent independently verified all 16 artifact sizes
and SHA-256 hashes in its delivery manifest. ACCEPT the conditional
detector and its probability/cost qualifications. New end-to-end
factoring complexity improvement remains NONE.

Exact duplicates modulo N are removed before forming
F(T)=product_i(T-c_i). Monic product and remainder trees over Z/NZ
evaluate F'(c_i) without inverting pairwise differences. A nonunit
derivative identifies an index with a partial collision. Searching its
sibling subtrees recovers a proper factor in O(M) extra residue operations
and O(log M) gcds; exact duplicates cannot produce an unrecoverable leaf.
The review's N=35 example illustrates, but is not the basis of, the proof.

For a fixed map, write w_r=sum mu_r^2, t_r=sum mu_r^3 and
rho=w_p+w_q-2w_p*w_q. Accept the exact shared-index probability kappa
and second moment in the review. Under w_p,w_q<=1/2,
kappa<5*rho^(3/2), and two fresh M-lists with M>=1/sqrt(rho)
give success probability at least 1/12. The moderate-collision
hypothesis matters: a rare-outlier law defeats this uniform conclusion
when both maps nearly collapse to one atom. No reachability is asserted
for that abstract counterexample.

The audit strengthens the parent's conservative repeated-batch note.
One fresh batch per dyadic width already has finite expected cost:
Var(Y)/(E Y)^2 <= 1/(M^2*rho)+10/(M*sqrt(rho)).
Five doublings beyond the critical width make failure at most
321/1024<1/2, so the doubled-work tail has ratio at most 321/512.
Widths can be capped at N and then repeated. Thus no hidden rho, p,
or good-law verifier is needed to run this fixed-map schedule.
A constant success lower bound alone would not prove this tail claim;
the variance bound is the essential additional argument.

Accept the explicit monic polynomial arithmetic, Kronecker packing,
sorting, gcd, sampling and storage costs. Exact uniform sampling uses
rejection, with its random-bit cost charged. A capped version must charge
its failures and replace 1/12 by (1-delta_s)/12. The resulting expected
fixed-map cost is (k+1)/sqrt(rho)*poly(log N) for a length-k evaluator,
with the reviewed polynomial-arithmetic logarithms.

This is a conditional extraction primitive. Acquiring a good map with
probability eta and paid trial bounds A,C gives the stated restart
bound 12(A+C)/eta; bad tapes cannot be discarded for free. The comparison
rho >> (k+1)^2/p and A=o(sqrt(p)) is specific to this evaluator and matched
sqrt(p) control. It is not necessary for all possible factoring algorithms
and does not establish an ECM/GNFS improvement.

Constructive consequence: useful output concentration now has a priced
extraction route. The main bottleneck is paid acquisition plus evaluation,
not an unimplemented collision oracle. W011 explores removing training
and retaining two balanced absorbing colors; W008's compact scalar
product route remains independent.
