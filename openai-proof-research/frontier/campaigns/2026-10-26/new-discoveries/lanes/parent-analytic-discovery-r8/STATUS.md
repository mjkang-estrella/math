# Analytical screening round 8 — no claimed discovery

Tally remains22/30 after the separate accepted Hetyei result. This lane has NO
Lean endpoint or accepted new theorem.

Simon2012.11018v2/MathDB349140: actual full source read. Remaining conjectural
regime concerns necessity of log-infinite-divisibility for complete monotonicity;
no proof/counterexample found here.

Area2608.23006v2/MathDB391922: actual primary and full48page companion
2609.29531 retrieved, with source bytes and receipts preserved. Companion
Theorem1.5 ALREADY proves the physical(A,B) sharp law for the formally defined
kappa polynomials. This known theorem must NOT receive discovery credit.
The source's all-order identification with actual Jacobi phases remains conditional
beyond the checked range; do not silently assume it.

A separate precise open question is primary Remark3.8: determine delta_r, the
power of2 in the common coefficient denominator in shifted variables
u=mu_alpha=A-1/4, v=mu_beta=B-1/4. Proposed delta_r=2r+nu2((r-1)!).
Source lower bound depends on Computational Observation3.1, checked r<=20,
not proved universally. The companion's linear-response valuations do not
settle the full shifted polynomial content.

Exact finite experiment shifted_content_check.py evaluates Definition2.1 through
r12. Let P_l(u)=product_{j=0}^{l-1}(u-j(j+1)), and
Ctilde_m=sum_l binom(m,l)P_l(u)P_(m-l)(v)(1+i)^l(1-i)^(m-l).
A_n=sum_m S2(n,m) 2^(n-m) (n!/m!) Ctilde_m = 2^n n! [Z^-n]F.
B_n=A_n-sum_{k=1}^{n-1}binom(n-1,k-1)B_k A_(n-k)
=2^n n! [Z^-n]log F. All are Gaussian integer polynomials.
Then kappa_r=Im B_(2r-1)/(2^(2(2r-1)) (2r-1)!).
The proposed denominator law is equivalent to exact coefficient content
min nu2(coeff Im B_(2m+1))=3m. This matches every r1..12.
Independent literal reciprocal-product expansion and exact logarithmic series
division agree with this path for r1..4 at3integer parameter pairs.
These computations are evidence ONLY, not an all-order proof or novelty claim.

Next: prove universal divisibility and one coefficient attaining it, or find a
counterexample / subsuming theorem. Need independent review before formalization.
No helpers, finite checks or already proved physical sharpness count separately.
