# T153M64: exact Markov transfer and the missing arithmetic mean bound

Full target: scope.md, unchanged and unresolved. Put r=1−2q, so |r|<1. The stationary sign chain has E epsilon_i=0 and E(epsilon_i epsilon_j)=r^{|i−j|}. All constants below may depend on the fixed q and beta. No uniformity at q=0,1 or1/2 is asserted. The source-paid q=1/2 case is kept separate wherever invertibility is used.

## 1. Source interface actually used

The source's entire salem.tex was read. It constructs algebraic integers

 A_m=product_{h≤m}(beta^{k_h}−beta^{−k_h}), b_m=sum k_h,
 c_m=product(z^{k_h}−z^{−k_h}), delta_m=|c_m|, L_m=log(1/delta_m),
 u_{m,j}=A_m beta^j,
 T_{m,j}=u_{m,j}+(−1)^m u_{m,−j}+2Re(c_m z^j) in Z.

Here z,conjugate z are the unit-circle conjugates. Its statements sal:construction and sal:loss give a fixed cosine floor gamma>0, negative-index logarithmic loss S_m=sum_{j≤0}−log|cos(pi u_{m,j})|=o(L_m), L_{m+1}≥2.1L_m eventually, and H_m=ceil(b_m+D L_m)≤exp(.75L_m), with D=10/log beta. The exact shift is

 u_{m+1,j}=u_{m,j+k_{m+1}}−u_{m,j−k_{m+1}}.

The source is not a Markov theorem. Its mean lower bound multiplies independent scalar cosines. Its growth and floor statements alone do not include an operator lower bound.

## 2. Localization and concentration do extend, with complete elementary proof

For any finitely supported real coefficients a_j, covariance and 2|a_i a_j|≤a_i²+a_j² give

 E|sum a_j epsilon_j|² ≤ C_r sum a_j², C_r=(1+|r|)/(1−|r|).

The same holds for square-summable coefficients by L2 completion. The source trace replacement is still valid because exp(i pi T epsilon)=(-1)^T for integer T and either sign. Thus, for W_{m,n}=exp(i pi A_m beta^n Y), its window approximation on indices[n−H_m,n+H_m] satisfies

 ||W_{m,n}−Wtilde_{m,n}||_2²
 ≤ C_{q,beta}( beta^{2(b_m−H_m)}+n delta_m² ).

Indeed subtract the phase angles, discard integer trace factors, apply |exp(ix)−exp(iy)|≤|x−y| and the displayed covariance bound. The source's geometric-tail sums are unchanged. At n≤exp(1.5L_m), the norm is O_q(exp(−L_m/4)).

If bounded complex functions U,V of two disjoint sign blocks are separated by d transitions, then |Cov(U,V)|≤|r|^d when |U|,|V|≤1. Condition on the last sign of the first block and the first sign of the second. Their conditional expectations are functions a+b epsilon and c+d' epsilon; the constant terms cancel in covariance, and |b|,|d'|≤1. The remaining correlation is r^d. This also proves the complex-conjugated version needed for L2.

Use the source equally spaced centers with spacing2H_m+1 and M_m windows. For centers differing by j spacings, the gap between blocks is1+(j−1)(2H_m+1). Summing the covariance bound yields variance of the window average≤C_q/M_m. Adjacent windows need not be independent: the geometric bound is enough. No mixing-rate theorem is invoked without proof.

By stationarity, all unprefactored window expectations are the same real scalar

 C_m=E exp(i pi sum_{j=−H_m}^{H_m} u_{m,j} epsilon_j),

where a stationary two-sided extension may be used for notation. Global sign symmetry makes it real. Each source trace prefactor is a deterministic sign, so it can be removed in the coefficient of the corresponding Fourier exponential.

Consequently, if along any unbounded subsequence |C_m|≥exp(−kappa L_m) for some fixed kappa<1/4, the target singularity follows by the source's phase-average argument. Choose signs so the window means become |C_m|. The mean of the actual phase average differs by O_q(exp(−L_m/4)), while its centered L2 norm is O_q(M_m^{−1/2}+exp(−L_m/4)). Since M_m≥exp(.7L_m), Chebyshev gives sets with measure tending to one for the Markov law. Their Lebesgue measure tends to zero because the distinct-frequency integral bound C(1+log M_m)/M_m is entirely deterministic. Passing to a subsequence with summable complements gives a full-measure null Borel set; no pure-type theorem is needed.

One can optimize this sufficient threshold without changing the target. Use J_m=floor(exp(a L_m)) for .75<a<2, preserving H_m and the source construction. Then M_m≥exp((a−.75−o(1))L_m), the L2 phase error is O_q(exp(−(1−a/2)L_m)), and the same proof works for

 kappa < min(1−a/2,(a−.75)/2).

The maximum is5/16 at a=11/8. This is merely a sufficient mean-bound interface, not an established bound on C_m.

## 3. First attempted mean proof: transfer stability from scalar phase loss

Represent a conditional characteristic function by f(epsilon)=a+i b epsilon, with a,b real. Transition P sends (a,b) to(a,r b), and multiplication by exp(i t epsilon) sends it to(cos t a−sin t b, sin t a+cos t b). Thus the combined D(t)P operation is

 (a,b) -> (cos t a−r sin t b, sin t a+r cos t b).

Small phases preserve a neighborhood of the even direction and lose amplitude quadratically after projective control. However the source permits finitely or sparsely many non-small phases, controlled only by the cosine floor and scalar logarithmic loss. Those conditions do not prevent the even coordinate from vanishing.

Exact two-step example: take0<r<1 and t=arctan(r^{−1/2}). Then

 D(t)P D(t)(1,0)=(cos²t−r sin²t,(1+r)sin t cos t)=(0,sqrt r).

The scalar characteristic expectation vanishes, although cos t=sqrt(r/(1+r))>0. This is an exact algebraic counterexample to a general lower bound from the source scalar contract. It is not a claim that these two phases occur as the source geometric coefficients for some beta and m.

## 4. Second attempted mean proof: reversible reflection

Let theta_j=pi u_{m,−j},1≤j≤H, and let

 psi(s)=E[ exp(i sum_{j=1}^H theta_j epsilon_{−j}) | epsilon_0=s ]=a+i b s.

Reversibility of the symmetric chain and the Markov property make the negative and positive half-blocks independent conditional on epsilon_0. Sign symmetry gives psi(−)=conjugate psi(+). Ignoring the small trace errors for the moment, at EVEN m the positive coefficients are negatives of the reflected negative coefficients, modulo integer traces. The ideal full mean is therefore

 cos(pi A_m)(a²+b²).

At ODD m they have the same sign, and the ideal mean is

 Re(exp(i pi A_m)(a+i b)²)
 =cos(pi A_m)(a²−b²)−2 sin(pi A_m)ab.

All deterministic integer-trace signs may be put outside these expressions. Actual and ideal window means differ by O_q(sqrt(H)delta_m), by the covariance estimate; at the source H≤exp(.75L) this is O_q(exp(−.625L)).

For r≠0, a finite conditional half-block vector cannot vanish: each D(t) is orthogonal, P has smallest singular value |r|, and the terminal vector is(1,0). In particular its norm is at least |r|^H. This proves qualitative nonvanishing of the ideal even mean, since the source gives |cos(pi A_m)|≥gamma. The bound gamma|r|^{2H} can be enormously smaller than exp(−kappa L), and can also be smaller than the trace-error bound. Thus it does not prove that the actual even C_m is nonzero or useful.

There is an exact obstruction to inferring a quantitative even-block bound solely from the scalar phase contract. Take the two phases t,t from §3 and put n−1 zero phases between them and the conditioning center. The conditional vector is

 P^n D(t)P D(t)(1,0)=(0,r^{n+1/2}).

Reflect this half-block antisymmetrically about a center phase zero. Its full mean is r^{2n+1}. All cosine factors have a fixed positive floor, and their total logarithmic loss is −4log(cos t), independent of n. Nevertheless the mean tends to zero exponentially in n. The even reflected-square identity prevents exact cancellation, but not prolonged decay in the odd transition eigenvector. This arbitrary-phase example is a transfer-interface obstruction only; it does not refute T153M64 or prove failure on the actual source multipliers.

## 5. Third route: source-aware propagation of an even cone

The parent proposed using the actual shift identity to put the old complete window far from the new conditioning endpoint. This is more specific than the failed arbitrary-phase transfer. Here is its exact local estimate.

Suppose k>H_m. In the new negative half, the shift expresses coefficients as u_{m,j+k}−u_{m,j−k}. The old complete window −H_m≤j+k≤H_m is located at distance k−H_m from the conditioning endpoint. Replacing the old positive tail by integer traces and dropping the negative tail and the u_{m,j−k} correction, the new conditional vector differs from a deterministic sign times C_m times the even vector by at most

 C_{q,beta}( sqrt(k)delta_m + beta^{b_m−H_m} + beta^{b_m−k} + |r|^{k−H_m} ).

The conditional L2 replacement estimate follows from the unconditional one with a factor sqrt2, since the conditioning event has probability1/2. The last term is the exact rank-one mixing bound. Infinite negative tails converge absolutely, so finite truncation and passage to the limit justify the formula.

If this error is small relative to |C_m|, then the new conditional vector has |b/a| small. A cone |b|≤epsilon|a| with epsilon≤gamma/8 makes BOTH reflection parities safe: the odd expression differs from cos(pi A)a² by at most(epsilon²+2epsilon)a² and hence has magnitude at least gamma a²/2; the even expression has magnitude at least gamma a². With trace errors also smaller than this margin, scalar losses can then approximately double while L grows faster than doubling.

But the required seed and compatibility have not been proved. The source k≤exp(1.9L_m) only makes sqrt(k)delta_m≤exp(−.05L_m); the finite conditional-vector lower bound is exp(−C_q H_m), not a comparable exponential in L_m. Enlarging an initial multiplier changes its seed vector as well as L_m. It is invalid to fix the seed lower bound and then vary the same initial multiplier to make errors small. Also k≥2b_m+D L_m gives k−H_m≥b_m, not automatically a chosen multiple of L_m. A modified lower cutoff k≥2H_m would supply that mixing gap and seems compatible with the source Dirichlet selection after rechecking constants, but that modification alone does not solve initialization and is not asserted as a completed new construction here.

Using two identical factors to keep reciprocity parity even gives

 u_new,j=u_old,j+2k−2u_old,j+u_old,j−2k,

so it introduces the doubled harmonic2A_old. No closed simultaneous control of those harmonics has been established. Two distinct factors yield four translates, and a direct matrix treatment might avoid the intervening odd scalar projection, but no bound proving this has been found. These are exact remaining tasks, not impossibility conclusions.

## 6. Full-target status

Classical entropy gives singularity when h(q)=−q log q−(1−q)log(1−q)<log beta; source153 gives q=1/2. Neither is nominated. The remaining full target needs an actual arithmetic conditional-mean lower bound or a compatible seed plus propagated even cone, for EVERY beta and q in scope. The calculations here neither supply that bound nor refute the target. No generic-q, restricted-q or conditional result is offered as a replacement.

Parent contributions are credited in §§3 and5: even/odd transfer coordinates, the warning about finite-state stability versus substantive novelty, and the source-shift even-cone strategy. The reflected identities, explicit traps, and completed Markov concentration interface were developed in this author lane and discussed collaboratively. This is author research, not an independent review.

Original prose and derivations: Myeongjin Kang, CC BY4.0.
