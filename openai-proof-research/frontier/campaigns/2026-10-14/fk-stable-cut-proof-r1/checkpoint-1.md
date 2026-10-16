# Mathematical checkpoint 1 — independently reconstructed conditioning

Original prose CC BY 4.0. No contribution verdict.

For increments Y=xi-1>=-1, let a_m(z)=P(S_m=z), pi_s=a_s(-1)/s,
and F_j be total size of j unconditioned GW trees (F_0=0).
Writing tau_j for the first hitting time of -j gives exactly
P(tau_j=t)=P(F_j=t). On {S_m=-j}, tau_j<=m, so the strong Markov
property yields sum_{t=0}^m P(F_j=t)a_{m-t}(0)=a_m(-j).
This includes m=0 and j=0; no forest asymptotic is used.

For the root toll g(k)sum_i F(S_i), cyclic fringe counting and selection
of one child give N/a_N(-1) times
sum_s F(s)pi_s sum_k k p_k g(k) sum_t P(F_{k-1}=t)a_{N-1-s-t}(0).
Substitution of the exact convolution proves candidate (3.5).
At m=0 only k=1 can contribute, and the exact source has p_1=0.
For odd N, the maximal actual child size is N-2; then m=1 and the
k=2 residual term is p_0. There is no lost root or endpoint term.

The uniform local bound gives a_m(1-k)<=C/(m+1)^(1/2), hence for a>1/2
E sum_v g(k_v)sum_i S_i^a <= C N^(3/2) E[xi g(xi)]
  times sum_{s<N} s^(a-3/2)(N-s)^(-1/2)
<= C_a N^(a+1/2) E[xi g(xi)].
Split the sum at N/2: the first half is bounded by
C N^(-1/2) N^(a-1/2), the second by C N^(a-3/2) sqrt(N).
Thus g(k)=k 1_{k>K} costs E[xi^2;xi>K], exactly as required.
Nested fringe sizes/marks were never treated as independent.

The p_2/2 spine thinning and M=2n tensor normalization have also been
checked directly against source contracts. Interval endpoint and all-g
injectivity audits remain active; no verdict yet.
