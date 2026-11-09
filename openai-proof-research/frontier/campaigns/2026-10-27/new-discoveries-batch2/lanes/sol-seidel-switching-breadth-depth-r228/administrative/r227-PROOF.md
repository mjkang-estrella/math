# Two complete source-endpoint calculations, both held as routine

These are ordinary mathematical arguments, not independently reviewed discoveries. No Lean/manuscript or acceptance is asserted.

## Simic's smooth-convex constant: alpha*=1/4

Exact source: Slavko Simic, https://arxiv.org/pdf/1611.01905v1, Open Question PDF p2, Theorem 2.1 and its proof p3. The question asks the optimal universal alpha in

 (1/(b-a)) integral_a^b f <= alpha(f(a)+f(b))+(1-2alpha)f((a+b)/2)

for every C-infinity convex mapping f on I and every a<b in I. Affine functions force the displayed normalization; the relevant alpha is the smallest admissible coefficient. Theorem 2.1 already proves alpha=1/4 for all integrable convex f, by applying the trapezoidal convexity bound on each half interval. We only need sharpness within C-infinity.

Route 1 (explicit analytic regularization). Normalize [a,b] to [0,1] and set f_e(x)=sqrt((x-1/2)^2+e^2), e>0. This is smooth on all R and strictly convex, since f_e''=e^2/((x-1/2)^2+e^2)^(3/2)>0. Uniformly, |x-1/2|<=f_e(x)<=|x-1/2|+e. Consequently integral f_e ->1/4, f_e(1/2)=e->0, and f_e(0)+f_e(1)->1. Thus the ratio (integral f_e-f_e(1/2))/(f_e(0)+f_e(1)-2f_e(1/2)) tends to 1/4. For any alpha<1/4, a sufficiently small e violates its proposed universal inequality. Combined with source Theorem 2.1 this proves exactly alpha*=1/4. The functions are globally smooth, so choosing a compact interval does not introduce an endpoint-domain loophole.

Route 2 (polynomial convex approximation). Let n=2m and

 P_n(x)=sum_{k=0}^n |k/n-1/2| binom(n,k)x^k(1-x)^(n-k).

On [0,1], P_n'' is n(n-1) times a Bernstein sum of the nonnegative second differences of the convex sequence |k/n-1/2|. Hence P_n is convex, and as a polynomial is C-infinity on an interval containing [0,1] on which convexity holds (or take I=[0,1], as the source does for its own example). For a version avoiding any extension issue, use subintervals [eta,1-eta] and then eta down to zero; polynomial continuity transfers any strict violation. The exact values are

 P_n(0)=P_n(1)=1/2,
 P_n(1/2)=binom(n,n/2)/2^(n+1),
 integral_0^1 P_n=(n+2)/(4(n+1)).

The last identity uses integral binom(n,k)x^k(1-x)^(n-k)=1/(n+1). The central binomial quotient tends to zero, e.g. from the binomial random variable bound E|K/n-1/2|<=1/(2sqrt(n)). Thus the same sharp ratio tends to 1/4. checks.py verifies exact rational values for five n; the universal proof is the preceding bound, not those cases.

Strongest objection: the full bridge is just density of smooth convex functions plus the midpoint hinge extremizer for a classical quadrature inequality. This meets the source wording but is a ROUTINE endpoint specialization. No campaign nomination or credit is justified from it. A narrow live search returned only the target paper; that does not establish new-to-literature status. Cover says 2016 arXiv; internal print stamp is 2018, a chronology discrepancy retained without inventing an intervening version.

## Niculescu–Prajitura weighted density: sparse-block refutation

Exact source https://arxiv.org/pdf/1201.5156v1, Problem 3 PDF pp9–10: for EVERY A subset N, does limsup |A intersect [1,n]|/(n/log n)>0 imply sum_{n in A}1/n=infinity?

No. Put N_k=2^(2^(k+3)), M_k=floor(N_k/log N_k), k>=1, and A=union_k {N_k-M_k+1,...,N_k}. These disjoint blocks have M_k/N_k<=1/log N_k, while M_k>=N_k/(2 log N_k). At n=N_k the normalized count is at least 1/2, so the required upper weighted density is positive. Each block contributes at most M_k/(N_k-M_k) <=2/log N_k, and sum_k 2/log N_k converges geometrically. Hence the harmonic subseries converges. All integers are positive, the blocks eventually lie in [N_k/2,N_k], and discarding a finite initial prefix changes neither conclusion.

The same mechanism treats each fixed iterated-log weight in the source by selecting N_k sufficiently sparse so that phi(N_k)/N_k is summable. This is not claimed as another result. It is the elementary distinction between positive upper limsup density and a lower density condition. The source's nearby Lemma 6 and Corollary 2 address ordinary positive upper density; they do not imply this weighted statement.

Strongest objection: this is a routine sparse-block construction, and prior literature/current registries are not cleared. The exact source question is refuted, but the campaign's substantive-newness rule still blocks a nomination. No arithmetic-progression or Erdos conjecture assertion is used.
