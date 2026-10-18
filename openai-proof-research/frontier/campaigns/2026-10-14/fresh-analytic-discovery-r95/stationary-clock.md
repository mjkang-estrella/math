# Stationary physical clocks — local realization and unpaid iteration

Live author proof development. This supporting construction is not the full smooth simple-Lebesgue-flow objective and is not a nominee. Parent proposed Fourier compensation and highlighted the global zero-compatibility issue; both are author collaboration, not review.

## 1. Exact period map

In physical coordinates (theta,q,a), let H_N'=N(V+Delta_N), with H_N(q+1)-H_N(q) an integer, and use the zero-jitter passage vector field

 X_N=N^-1[H_N'(q) partial_theta+partial_q].

The straight coordinates are (q,w,a), w=theta-H_N(q), and X_N=N^-1 partial_q. For a physical clock1+b_N>0, replace X_N by X_N/(1+b_N). Its orbit period at(w,a) is

 N[1+A_N(w,a)],  A_N(w,a)=integral_0^1 b_N(w+H_N(q),q,a)dq.       (1)

This is an exact orbit integral. The invariant volume is proportional to(1+b_N)dtheta dq da. For the mean-zero theta Fourier clocks used below this can be returned explicitly to standard volume by the physical map Theta=theta+integral_0^theta b_N(t,q,a)dt, keeping q,a fixed. Its Jacobian is1+b_N, it is a smooth circle diffeomorphism, and it converges to the identity in C∞. Thus no unproved volume-normalization theorem is hidden in this step. The straightened angular coordinate is

 Q(q,w,a)=[q+integral_0^q b_N(w+H_N(v),v,a)dv]/[1+A_N(w,a)].      (2)

It is a circle diffeomorphism since1+b_N>0, and the new angular speed is1/[N(1+A_N)]. No averaging theorem is used.

If V+Delta_N is bounded below by a positive constant with N-uniform smooth derivative bounds, periodic integration by parts for every nonzero theta Fourier mode yields, for each fixed k,r,

 ||A_N-average_w A_N||_(Ck) <= C_k,r N^-r ||b_N||_(C^{k+2r+2}).   (3)

The integer degree of H_N cancels boundary terms, and every integration divides by N times a uniformly nonzero V+Delta_N. Thus physical C∞-small clocks have insufficient phase-dependent spreading at scale1/N in this positive-speed architecture. This estimate does not apply at a zero of V.

## 2. Realizing a prescribed smooth jitter through one simple zero

Suppose V has a simple zero q*, and choose a fixed smooth chi supported in a small neighborhood containing no other zero, with chi(q*) nonzero. A periodic V cannot have just one simple zero globally; only the support of chi isolates one. Let q_N be the unique zero of V+Delta_N in that neighborhood. All local derivative and nondegeneracy bounds are uniform for large N.

For every nonzero integer l, one-dimensional stationary phase gives

 integral chi(q) exp(2 pi i l H_N(q))dq
 = chi(q_N) exp(2 pi i l H_N(q_N)+i pi sgn(l V'(q_N))/4)
       /sqrt(N |l| |V'(q_N)|) + O((N|l|)^(-3/2)).              (4)

The remainder constant is uniform in l and N. A parameter-uniform Morse change of coordinate reduces the phase to a signed quadratic; the Fourier-transform evaluation of that quadratic integral bounds the first remainder by t^(-3/2) integral |xi|² |amplitude_hat(xi)| dxi. The latter integral is uniformly finite using four derivatives of a compactly supported transformed amplitude. The nonstationary complement is handled by repeated integration by parts. This explains the claimed uniformity rather than assuming a separate estimate for each l.

For any fixed real C∞ periodic mean-zero function J(w)=sum_(l nonzero) J_l exp(2 pi i l w), set

 B_N(theta)=sqrt(|V'(q_N)|)/chi(q_N)
   *sum_(l nonzero) sqrt(|l|) J_l
     exp(-i pi sgn(l V'(q_N))/4)
     exp(2 pi i l(theta-H_N(q_N))),
 b_N(theta,q,a)=N^(-1/2) chi(q) B_N(theta).

The Fourier series converges in C∞. Conjugate symmetry makes B_N real. Phase translation depending on N does not enlarge any physical derivative norm. Hence ||b_N||_(Ck)<=C_k,J N^(-1/2), and the clock is positive for large N. Substitution into(1), followed by(4), gives

 A_N(w)=J(w)/N+O_(Ck)(N^-2)                                  (5)

for every fixed k. Indeed the remainder sum is bounded by C N^-2 sum_(l nonzero) |l|^(k-1)|J_l|. A desired constant term J_0 can be supplied by adding J_0/N to b_N. Thus this local operation realizes an arbitrary fixed smooth jitter, rather than only the arcsine law produced by a cosine.

## 3. Exact packet normalization before any cancellation claim

Take old packets A_m(q,a) exp(2 pi i m theta), supported in a common compact arc I where V' is nonzero, V is bounded away from0, and I is disjoint from the clock support. Choose the origin of q so the clock support has not been crossed on reaching I. On I equation(2) becomes Q=q/P_N(w), with P_N=1+A_N.

In straightened coordinates the invariant probability has density P_N(w)/Z_N relative to dQ dw da, where Z_N=integral P_N. For mean-zero clocks above, Z_N=1 exactly. The j-th angular coefficient contributed by old mode m is exactly

 C_(m,j)(w,a)=P_N(w)^(-1) exp(2 pi i m w)
    * integral A_m(q,a) exp(2 pi i[m H_N(q)-j q/P_N(w)])dq.     (6)

At its real temporal frequency lambda=j/[N P_N(w)], the stationary equation is m(V(q)+Delta_N)=lambda. Thus its leading coefficient has squared amplitude

 [N P_N(w)^2]^-1 |A_m(q_m(lambda),a)|²/|m V'(q_m(lambda))|.     (7)

Multiplication by the invariant weight P_N and division by the frequency Jacobian |d lambda/dw|=|lambda A_N'(w)|/P_N leave precisely

 |A_m(q_m(lambda),a)|² / [N |lambda A_N'(w)| |m V'(q_m(lambda))|]. (8)

This is the normalization needed for a real-line weighted Riemann-sum calculation. Using(5), roots satisfy j-N lambda=lambda J(w)+O(1/N); the O(1/N) and its derivatives are uniform on any fixed compact lambda interval away from0.

For two old modes m,m', the leading relative phase in(6) is

 exp(2 pi i N[S_m(lambda)-S_m'(lambda)])
    * exp(2 pi i(m-m')w) * a fixed Maslov phase.               (9)

The first factor is independent of the root index j at fixed lambda. If the common packet arc lies after the clock support instead, the additional j-dependent phase from the accumulated clock is common to all m and cancels in(9).

For a profile J(w)=Lw+beta on a good arc and cutoff psi supported there, the roots form a grid of mesh1/(|lambda|L) in w. The leading cross-density for m!=m' therefore contains the Riemann sum for

 integral psi(w)^2 exp(2 pi i(m-m')w)dw.

Its quadrature error is bounded by C ||(psi² exp(2 pi i(m-m')w))'||_1/(|lambda|L), uniformly in the fast grid offset. The integral itself is small when psi=1 outside an arc of small measure, since the full nonzero Fourier harmonic has integral0. This is actual strong cancellation after summing roots, not merely weak cancellation of the action phase in(9). Diagonal terms recover their old real-line density with the same quadrature bound. Stationary-phase mass errors must still be summed before pushforward, as in the pinned source.

This establishes a concrete route to a one-pass neutral matrix-density estimate for fixed finite packet data. It is not a proof of the full iterative construction, and no source biased-prediction lemma is being silently transferred.

## 4. Global compatibility remains unpaid

An initial sign-changing V is compatible with the local construction, e.g. V=sin(2 pi q), clock supported near q=1/2 and packets inside(0,1/4). The resulting straightened angular speed1/[N(1+A_N)] is everywhere positive. It does not inherit a zero suitable for simply repeating the same formula.

Forcing a zero of c+sigma in the preceding chart changes the physical principal theta speed by an order-one amount where the preceding V was nonzero. Placing that zero outside packet support only controls observables, not the global C∞ norm. This invalidates an automatic iteration claim.

A different iteration could track critical points of a fixed physical coordinate along later circle orbits, or retain a coherent spectral frame across several coupled passages. Their uniform phase normal forms, number of stationary points, strong density control, elimination of all invariant slow variables and the biased color-prediction step are not yet supplied. The one-pass clock is therefore supporting research only. No weaker spectral subspace is substituted for the entire centered representation.

## 5. Quantifiers for the one-pass neutral estimate

For fixed finite packet data, assume each amplitude is smooth and compactly supported strictly inside the common arc I. Set v_*=min_I |V|>0 and m_*=min |m|>=1. For all sufficiently large N, every stationary packet frequency satisfies |lambda|>=lambda_*=m_*v_*/2. A common finite upper bound follows from the finite mode set and max_I |V|. The inverse stationary amplitude is extended by zero across its support endpoints; smooth compact support of the original amplitude makes this extension smooth. Nonstationary frequency tails must be included in the summed-mass remainder, not set to zero by fiat.

Let 0<=psi<=1 vanish on the ramp-reset arc and equal one outside a slightly larger arc E of measure eta. The loss is controlled BEFORE frequency pushforward. On packet support the physical clock is zero, so its invariant physical density is exactly 1/Z_N. Integrating in the old theta variable is equivalently integrating w=theta-H_N(q). For a vector packet with h old modes, pointwise Cauchy--Schwarz gives

 ||(1-psi) f||²_(new volume) <= (h eta/Z_N) sum_m ||A_m||².

Thus even coherent cross terms cannot give hidden reset mass after normalization. Here Z_N=1 for the mean-zero clock; with a fixed constant jitter it is 1+O(1/N), bounded below by 1/2. The total variation difference of scalar spectral measures is at most ||f-g|| (||f||+||g||), and polarized versions give the same control for each matrix entry. This follows directly from the spectral projection Cauchy--Schwarz inequality and does not require density pointwise bounds on the reset arc.

For the retained packets, every Riemann-sum error is bounded uniformly by C_(fixed data,psi)/ (lambda_* L), while the nonzero harmonic's integral is bounded by the measure of the discarded region times a fixed amplitude constant. First choose eta small and a smooth cutoff, then choose L large enough to absorb its derivative norms, then choose N large enough for the fixed Fourier-designed jitter and all stationary remainders. One must not take eta to zero simultaneously with L or N without preserving this order. The O_Ck(N^-2) error in the realized period profile yields a vanishing perturbation of the finite root sum on the compact good arc; the cutoff vanishes at its endpoints, preventing a root-entry discontinuity there.

These bounds address lower frequency, support endpoints, and weighted reset normalization for the single pass. They do not assert the additional biased color-prediction construction, nor an infinite iteration.
