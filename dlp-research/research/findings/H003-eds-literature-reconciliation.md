# H003 reconciliation with the general EDS fixed-shift question

Native Astra follow-up derived this scope distinction; root checked the algebra.
No experiment, edit by proposer, or child was used. This supplements the reviewed
fixed-window negative and makes no novelty claim or claim to settle the general
open question. No ECDLP gain follows from a stronger pseudorandomness bound.

Keep q=ord(G) odd prime and gcd(q,p−1)=1 for the existing pointwise phi definition.
Set c=chi(phi(G)), H=[2^-1 modq]G, and v(n)=chi(2y(nH)), zero at q|n. The corrected
normalization gives `s_n=chi(W_G(n))=c^n*v(n)` on INTEGER indices. Thus
`s_n*s_(n+h)=c^h*v(n)*v(n+h)`.
The quadratic twist cancels, so merely distinguishing W from phi does not avoid
the new bound. Reduce the point argument modulo q only AFTER retaining c^n;
there is no canonical-parity mismatch.

For h not divisible by q, the two-factor rational function
`F_h(T)=4*y(T)*y(T+hH)` has degree6 and disjoint translated2-torsion supports,
hence simple geometric zeros. The mixed-character argument already independently
checked in H003-eds-character-collapse.md gives complete Fourier sums <=12sqrt(p).
Zero values at n=0,−h exactly match the original W-product and omitted poles.
Fourier completion bounds the incomplete sum by O(sqrt(p)*log q) for1<=N<=q;
for q<N<=2q split off a complete q-block. The two-factor sequence is q-periodic
even if s_n has period2q. Cancellation is meaningful only for N large compared
with sqrt(p)*log q. If q|h, the product is c^h*v(n)^2 and need not cancel.

The [Bhakta–Shparlinski preprint](https://arxiv.org/html/2507.09271v1), Question1.1
and Theorem1.2, covers general character orders and point orders; its shift-average
results and broad fixed-shift question are not restricted to our odd-order
quadratic subcase. The present deduction therefore supplies a restricted
affirmative case, not a contradiction or a solution in that full scope. It says
nothing about cancellation on genuinely short intervals, even-order points,
general character orders or arbitrary adaptive derived predicates.

Primary character ingredients: [Chen Proposition1](https://doi.org/10.1007/s00605-008-0520-x)
and [Shparlinski–Stange Lemma5](https://arxiv.org/pdf/0912.5246). The main finding
records the geometric nonpower wording correction and the primary PDF read.

Optional algebraic extension, not needed for the accepted A1 decision: Ward's
formula W_(sr+k)=a^(ks)*b^(s²)*W_k implies a^r=b² by comparing a2r shift to
two r shifts. For odd r, chi(a)=1, so s_(n+r)=tau*s_n with tau=chi(b).
Together with s_(2k)=chi(2y(kG)), this recovers s_n=tau^n*v(n) on an odd-order
subgroup without the coprimality assumption needed to define phi. This elementary
extension is not yet a separately reviewed theorem and is not required to enlarge
the project's target claims. No follow-up experiment or generic proof library.
