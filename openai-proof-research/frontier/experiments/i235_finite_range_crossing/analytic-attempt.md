# I235 — early analytic checkpoint

The target is the finite-range extension of quantitative forward crossing, or directly the finite expectation of the source's marked regeneration duration. All pinned OpenAI results and lower operations at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true in their stated scopes. I232 A232 and B232 are technical inputs only.

Exact base class: stationary ergodic uniformly elliptic complete nearest-neighbor transition rows on Z^d, with sigma-fields on deterministic sets at infinity-distance greater than r independent (also for infinite sets). Assume almost-sure escape in a fixed direction. A possible restricted target is d>=4 with a finite row alphabet; neither restriction by itself supplies product structure.

Route 1: read the complete iid crossing argument and investigate whether independent spatial marked words with finite mean radius control overlaps of independent walks. The first issue is to identify the law of the transverse difference process and the exact summability needed, without assuming an unavailable second moment.

Route 2: read the entropy/stationary contradiction and the actual finite-range marked-renewal law. Test finite-color or collar comparisons relative to Q itself. A product-reference entropy may be infinite even for finite alphabets, and conditioning on revealed collars need not preserve independence.

No theorem is claimed at this checkpoint. In particular a small positive inverse moment is not a first inverse moment, and overlapping halfspace survival variables are not independent. No subordinate agents or live I231/I234 outputs are used.

## Checkpoint 2: the shifted-renewal obstruction can be paid

Here is an elementary lemma that does not require nonnegative adjacent differences of the marked renewal masses. Let L be a positive integer renewal width with renewal sequence b_0=1, b_n=0 (1<=n<M), and b_n=xi u_(n-M) (n>=M), where xi>0, u_0=1, u_n decreases to p>0. Set d_n=u_n-u_(n+1)>=0. If sum (n+1)^k d_n<infinity for every integer k>=0, then L has all polynomial moments, and indeed sum (n+1)^k P(L>n)<infinity for every k.

Proof. For 0<=t<1 let U(t)=sum u_n t^n, B(t)=sum b_n t^n, D(t)=sum d_n t^(n+1), and G(t)=sum P(L>n)t^n. The renewal identity gives B(t)G(t)=1/(1-t). Meanwhile (1-t)U(t)=1-D(t), so

    G(t)=1/A(t),
    A(t)=(1-t)+xi t^M(1-D(t)).

All derivatives of D have finite left limits at 1 by the moment assumption. A(1)=xi p>0. Consequently every derivative of 1/A has a finite left limit at 1 (differentiate the identity A G=1 inductively). Since G has nonnegative coefficients, monotone convergence applied to each derivative shows sum (n)_k P(L>n)<infinity. This also gives all ordinary polynomial weighted tail sums. No defective-convolution assertion is made for b_n-b_(n+1): it is negative at n=M-1. QED.

This is a technical completion of I232's conditional renewal conversion, not a derivation of the missing crossing estimate. The full confinement and duration deductions, with a finite-range buffer at a tilted record, will be recorded below after checking the source dependencies.

# Completed continuation

## 1. Exact scope and dependencies

Let d>=3, U={+/-e_j:1<=j<=d}, and let Q be a stationary ergodic Borel law of full transition rows on (Delta_U)^(Z^d). Fix kappa>0 and integer r>=0. Assume Q-a.s. omega(x,e)>=kappa for every x,e and independence of the row sigma-fields on every two deterministic sets at infinity-distance >r, including infinite sets. Fix a nonzero real ell and assume P_0(X_n.ell -> +infinity)=1. No common null set over all directions, quantitative mixing beyond this assumption, rowwise drift condition, or iid representation is assumed.

Use I232 A232 as the previously established technical input: the source's marked words have integrable full spatial radius and give a deterministic limiting ray with positive ell-projection. Relabel a signed coordinate of that ray as e1. Use I232 B232, also technical: for q(x)=P_(x,omega)(X never below x_1), q(x)>0 simultaneously at all sites, and E_Q q(0)^(-alpha)<infinity for some alpha>0. Decreasing alpha if necessary is permitted. Neither input is a nominated finding here.

Use the pinned finite-range `prop:cut-law`, `prop:mean-width`, and `prop:exact-cut-bridges` exactly as stated. Fix 0<2lambda<kappa, M>dr+1, and xi=lambda^M. Under P_0 conditioned on D={never below 0}, the marked words are iid, with width L>=M, radius R, and duration tau, and E L,E R<infinity. Only star-mark departures use rows. All active rows of a word ending at height L lie strictly below L-M. The renewal masses are

    b_0=1, b_n=0 (1<=n<M), b_n=xi u_(n-M) (n>=M),
    u_n=E_Q a_n, a_n=P_(0,omega)(T_n<T_-1), u_n decreases to p=P_0(D)>0.

These one-sign identities do not require coexistence: enumerate the raw first hit of H-M before -1, append the constant-weight script, and impose a D suffix. The script separates active prefix rows from suffix rows, so its raw mass is xi u_(H-M) p; division by p gives b_H. The source bridge proof uses the opposite sign only elsewhere.

The main target remains E tau<infinity without a new moment or crossing assumption. The results below do not establish it. Finite-support row laws, even with exact range one and d>=4, are still unresolved by these arguments.

## 2. A confinement lemma valid under Q

**Lemma C235.** There exist C,c>0 such that, for every sufficiently large integer N, the raw path before sigma_N=T_(N+1) wedge T_-1 remains in |underline X|_infinity<=C N^2 except on an event of probability <=C exp(-cN).

**Proof.** Fix a signed transverse coordinate functional u. The deterministic limiting ray has first coordinate >0, so choose a fixed b>0 such that Y(x)=u.x+b x_1 tends to +infinity along the walk almost surely. The minimum argument (or the finite-range sign-union source) gives p_Y=P_0(Y(X_j)>=0 for every j)>0. The ray also implies that, for a sufficiently large fixed C2,

    P_0(max_(j<=T_(N+1)) |X_j|<=C2 N) ->1.

Indeed after a finite random time |X_j|<=C' (X_j)_1; before T_(N+1) the latter is at most N, and the earlier finite prefix is eventually inside the same bound. Intersect this event with D_Y; for large N its probability is at least p_Y/2.

At a first crossing of Y>j C3 N before sigma_N, every old departure has smaller Y. Prescribe m positive e1 steps with constant mark 0, where m is a fixed integer with bm>r||Y||_1. They have weight lambda^m, independent of all rows. From their endpoint impose the translated favorable event D_Y and the preceding norm bound through relative T_(N+1). Every row used by this suffix is beyond the old Y barrier by more than r||Y||_1, hence at infinity-distance >r from the old active rows. Apply `lem:separated-weights` separately to each finite crossing prefix. The infinite event is read in the killed walk outside the forbidden old r-neighborhood; no collar rows are revealed. Its conditional raw probability is at least epsilon=lambda^m p_Y/2>0.

Up to absolute strip exit, this continuation increases Y by at most bm+||Y||_2 C2 N, plus a fixed crossing overshoot. Absolute exit occurs no later than its relative T_(N+1). Choose fixed C3 large enough that the continuation prevents crossing the next Y-threshold before exit. If the connector itself exits, the same conclusion holds. Enumeration of first-crossing prefixes therefore bounds the probability of crossing j thresholds before exit by (1-epsilon)^(j-1). Crossing a transverse threshold of order N^2 forces order N such Y-thresholds because x_1>=0 before exit and u.X<=Y(X). A finite union over the 2(d-1) signed transverse coordinates proves the assertion. This is a raw path argument; it does not assert conditional independence after observing a collar. QED.

## 3. A small, unconditional duration moment (technical)

**Proposition D235.** Under Section 1, set b=(2d+1)/alpha and A=2d+b. Then

    E_(word) tau^s <infinity for every 0<s<1/A.

This is explicitly a fractional-moment result, not a bootstrap to E tau.

**Proof.** There are O(N^(2d-1)) sites in the strip and confinement box of C235. By stationarity and Markov's inequality, except on an environment event of probability <=C N^-2, q(x+e1)>=N^-b at every such site. From a visit to x, a positive e1 step followed by never going below x_1+1 has quenched probability >=kappa q(x+e1)>=kappa N^-b. It precludes any return to x before exit. Thus the number of visits to each site before sigma_N has a geometric tail with this success parameter. If sigma_N>N^A while the path stays in the box, some site has at least N^A/(C N^(2d-1)) visits. A union bound bounds this probability by C N^(2d-1)exp(-c N), for A=2d+b. Together with C235,

    P_0(sigma_N>N^A)<=C N^-2+C exp(-cN/2).

On D, if L<=N then the first word ends at the first hit of L, so tau<=T_(N+1)=sigma_N. The word law is the D-conditioned path law. Consequently

    P_(word)(tau>N^A)
      <=P_(word)(L>N)+p^-1 P_0(sigma_N>N^A)
      <=(E L)/N+C N^-2.

Taking N=floor(t^(1/A)) and integrating s t^(s-1)P(tau>t) proves the claim. No independence among the sitewise q-values was used. QED.

## 4. Crossing-to-duration conversion with the actual marked law

**Conditional transfer T235, not the target theorem.** Under Section 1, suppose additionally that there is beta in (0,1) such that, for every D0>0, eventually

    Q(a_N<N^-beta)<=N^-D0.                         (QC)

Then the source's marked L and tau have every finite polynomial moment. In particular the original walk has deterministic velocity v with v.ell>0.

The hypothesis (QC) is the unpaid crossing estimate, not an admissible added hypothesis for a new ballisticity finding. The contribution here is the complete conversion using the shifted renewal law; I232 left this conversion open.

**Proof.** First d_N=u_N-u_(N+1) is superpolynomially small. Use C235 and require a_(N+1)(x)>=(N+1)^-beta at every site of its polynomial-sized box. The failure probability is superpolynomial by (QC), stationarity, and a union bound. On a fixed good environment, the event T_N<T_-1<T_(N+1), while staying in the box, has probability at most

    [1-(N+1)^-beta]^(N+1).

After hitting N, visit the successive descending levels N,N-1,...,0. From each such visit, the auxiliary crossing of N+1 relative levels before one downward level has probability at least (N+1)^-beta and forces the original upper exit first. Iterate the quenched Markov property at these visits, stopping if the box is left. This bounds the event in question; no annealed independence is invoked. Since beta<1 the displayed expression is stretched exponentially small. The confinement exception is exponentially small, proving sum (N+1)^k d_N<infinity for all k.

Apply the shifted-renewal lemma in Checkpoint 2. For clarity its identity is

    sum_(n>=0) P_(word)(L>n)t^n
      = [1-t+xi t^M(1-sum_(n>=0)d_n t^(n+1))]^-1.   (SR)

The denominator tends to xi p>0 and has finite derivatives of every order at t=1 from below. Nonnegative coefficients on the left allow monotone convergence of its derivatives. Thus all weighted polynomial sums of the width tail are finite. In particular its tail decays faster than every power. This explicitly retains the initial gap: replacing the denominator in (SR) by 1-sum d_n t^(n+1) would be wrong.

For duration, impose a_N(x+e1)>=N^-beta at every relevant box site. Again the exceptional environment probability is superpolynomial. A positive step from x followed by the auxiliary crossing from x+e1 precludes returning to x before the original upper exit. Its probability is at least kappa N^-beta. The geometric visit-count argument from Section 3 now shows that sigma_N>N^A has superpolynomially small probability for any fixed A>2d-1+beta. Therefore

    P_(word)(tau>N^A)<=P_(word)(L>N)+p^-1P_0(sigma_N>N^A)

is superpolynomial. This proves all finite moments of tau. The iid-word strong law gives v=E(word displacement)/E tau; its first coordinate is E L/E tau>0. Integrable radius makes the limit hold inside words; the finite first raw cut does not affect the limit. The deterministic ray from A232 gives v.ell>0. QED.

## 5. High-dimensional route: what the independent skeleton really gives

Restrict to d>=4, still with arbitrary Q as in Section 1; a finite row alphabet is unnecessary for the following technical fact. Take two independent D-conditioned paths, each with the source's iid marked words. Their common width renewals give iid pairs of lists. The common renewal masses are b_n^2; for n>=M these are at least xi^2 p^2. The elementary renewal generating-function argument in the finite-range source's `prop:common-blocks`, applied with the same sign on both tapes, proves a finite mean common width. For example if f(t) is the first-common-width generating function, sum b_n^2 t^n=1/(1-f(t)); its lower bound forces f(1)=1 and E K<=1/(xi^2 p^2).

The number of words from either tape in a common block is at most its width. Whether the i-th word is needed is determined by earlier words on that tape and all widths on the independent other tape, independently of that word's radius. Tonelli gives finite expected sum of both tapes' radii in a common block, exactly as in the source proof. Thus the full transverse difference increment S in Z^(d-1) has E|S|<infinity, and its successive copies are iid and symmetric by exchanging the paths.

**Skeleton heat bound.** The law of S has positive mass at 0 and at every +/- transverse unit vector. For the latter, prescribe one tape's first word to move laterally by the specified unit vector, then upward to record height 1, then take the final M-step marked script. Prescribe the other tape to go directly upward to height 1 and take its final script. All pre-script marks may be 0; no earlier script completes, and both words have width M+1. Their raw marked weights are strictly positive, the source word law makes their probabilities positive, and their first common width is M+1. Equal prescribed words on the two tapes supply the atom at 0. Interchanging tapes supplies the negative vector.

Let m=d-1 and phi(t)=E exp(i t.S), t in [-pi,pi]^m. Symmetry makes phi real. The specified atoms give 1-phi(t)>=c sum_j(1-cos t_j). The atom at zero precludes phi=-1 anywhere. The unit atoms preclude phi=1 except at the origin modulo 2pi. Hence near zero |phi(t)|<=1-c'|t|^2 and away from zero |phi|<=rho<1. Fourier inversion yields, for the independent difference skeleton Z_n,

    sup_(x,y) P_x(Z_n=y)<=C(n+1)^(-m/2).            (HK)

Indeed integrate |phi(t)|^n and compare the neighborhood of zero to the Gaussian integral. For m>=3, sum_n P_x(Z_n=y)<infinity for every x,y. This proves transience of the independent endpoint skeleton without a second moment.

**Why this does not close the path comparison.** (HK) concerns endpoints of common words. The shared law agrees with two independent Q-fields only for fixed prefixes whose active row sets remain at distance >r. A word can make a very large transverse excursion and return close to its starting transverse coordinate. Finite first moment of its radius does not make total trace overlap summable. The next example makes this logical limitation explicit; it is not an RWRE counterexample.

Take two independent iid decorated tapes of constant width M+2, M>=2. In each block take a bounded symmetric transverse endpoint increment eta (with support 0 and +/-e_j), and independently a positive integer radius B with P(B>=t) comparable to t^-a for 1<a<2. Build a finite nearest-neighbor decoration as follows: ascend to height 1; traverse every vertex of the transverse l1-ball of radius B and return to its center; move by eta in that layer; ascend to record height 2; take the final M-step script. Use star marks in the preliminary part and the prescribed 0,1,...,1 script at the end. This satisfies the marked-word height and active-row geometry; there are no earlier scripted candidates. Its radius is at most C(B+1), so has finite mean. Both tapes have independent words, fixed widths, and bounded nondegenerate symmetric endpoint-difference increments.

At the start of block n their transverse gap Z_(n-1) is a bounded-increment centered random walk. An elementary exponential-moment bound and Borel--Cantelli give |Z_(n-1)|_1<=C sqrt(n log n) eventually almost surely: for each coordinate, use E exp(t xi)<=exp(Ct^2), optimize t, choose C large, and sum the resulting n^-3 bounds. Independently, the events B_n>=C sqrt(n log n)+1 occur infinitely often since sum (n log n)^(-a/2)=infinity. At each such late block, the first tape's filled ball contains the other tape's initial site at relative height 1. Their traces intersect. Thus infinitely many trace contacts occur almost surely despite a transient, bounded-step endpoint-difference skeleton and integrable radii.

This decoration law is NOT asserted to equal the annealed word law W(gamma) of any uniformly elliptic Q. It disproves only the inference from the proposed *listed spatial inputs* to summable overlaps. Genuine RWRE weights could exclude this law, but a new estimate using those weights is then required. Even a non-summable contact upper bound is not a proof of failure of the actual crossing estimate. No claim about impossibility of a sharper high-dimensional argument is made.

Primary prior-art check: Rassoul-Agha--Seppalainen's 2009 `Proposition 7.10` compares shared and independent difference transitions with a power-decaying error by using high moments of the full regeneration durations; `Lemma 7.11` bounds intersection through those durations. Its `Theorem 1.1` assumes a product environment and E tau_1^p0<infinity with p0>176d. Neither that theorem nor its coupling proof supplies this missing estimate from E radius alone. Applying it here would assume more than the target. The complete pinned iid fluctuation/Gaussian/clipping/kernel/stage/stationary argument instead avoids a second moment by a substantial projected-diagonal analysis; its fresh-layer steps must still be rebuilt under Q.

## 6. Finite alphabets, collars, and the correct entropy reference

A finite row alphabet does not supply either iid structure or arbitrary splicing. Here is an exact range-one finite-support example in every d. Let eta_x be iid fair bits, put Z_x=eta_x+eta_(x+e1)-1, and set c=1/(2d),

    omega(x,+e1)=c+epsilon Z_x,
    omega(x,-e1)=c-epsilon Z_x,
    omega(x,+/-e_j)=c (j>=2),  0<epsilon<c.

The row alphabet has three elements, uniform ellipticity constant c-epsilon, and the law is stationary ergodic and 1-dependent, including infinite deterministic sets. Adjacent rows are dependent, so its range is genuinely nonzero. This is the I232 mediator example, not a new transient RWRE.

There is a hard constraint: (Z_x,Z_(x+e1))=(1,-1) is impossible. Under the all-row product of the one-site marginal, this pattern has probability 1/16. On N disjoint neighboring pairs under that product law, the event E_N of no forbidden pattern has probability (15/16)^N, whereas Q(E_N)=1. Data processing gives

    KL(Q_restricted || product_restricted)>=N log(16/15).

On the full line the no-forbidden-pattern event has Q-probability 1 and product probability 0; hence the global entropy is infinite. Injective row quantization does nothing to this example. More generally finite-alphabet quantization preserves finite dependence but cannot justify a product reference law.

Independent splicing has a second, opposite-direction problem. Take lower rows from one Q-field and upper rows from another independent Q-field across the seam between heights -1 and 0. At a specified seam pair the resulting law puts probability 1/16 on the forbidden pattern, while Q gives it probability zero. Thus the splice is not absolutely continuous with respect to Q even on this two-row window, and KL(splice || Q)=infinity. Adding a collar and revealing it does not generally restore conditional independence: I232's explicit covariance calculation is the retained counterexample to that proposal.

**A valid deterministic collar bound.** Suppose the alphabet has K elements. Let A,B,C be deterministic disjoint row sets, dist_infinity(A,B)>r and C finite. Put U=omega_A, V=omega_B, W=omega_C. Then U and V are independent and

    I(U;(V,W))=I(U;W|V)<=H(W)<=|C| log K.           (CE)

This holds even for infinite A,B, by finite partitions and monotone limits. It compares the actual joint law to the product of its appropriate marginals, not to the all-row product law. It does NOT persist after arbitrary further conditioning. The proof is the entropy chain rule, independence I(U;V)=0, and the finite alphabet bound on H(W).

For a deterministic horizontal cut and a finite upper window, C may be the r boundary layers and V the upper rows above that collar. Equation (CE) then bounds the mutual information between the past and that finite upper window. The problem is quantitative: the full collar has infinitely many transverse sites. For a truncated window of width of order N, the crude cost is order r N^(d-1) log K, rather than the O(log N) total bad-event entropy that powers the iid episode argument. No argument here amortizes that surface cost over episodes or bounds it only by a uniformly integrable local profile quantity.

In particular, the iid `profile-entropy` proof's assertion that the future field, stopped at the next episode boundary and independently extended, still has the iid reference law does not survive this seam. A correct Q extension would have to sample using the conditional law of the omitted rows given the retained rows. That law retains boundary information; replacing it by Q's unconditional upper marginal is not justified. A profile-only state may not remember the required boundary data. The deterministic collar inequality does not solve this stopped-window problem.

The *final* bias-removal step of `profile-no-growth`, by itself, is more robust: if a suitable finite entropy law relative to the actual Q-upper field, and a local outward-order remainder, were already constructed, finite-range independence would separate its fixed origin box from the far-tail neighborhoods once their distance exceeds r. The missing work is the construction of that entropy law and the quantitative kernels, not far-tail decorrelation under a valid reference.

For completeness, finite-path quantization only gives the following limited comparison. If two row realizations obey |log omega(x,e)-log omega'(x,e)|<=eta for every x,e, a fixed T-step path has likelihood ratio between exp(-eta T) and exp(eta T). Summing paths of length at most T retains this bound under the same coupled row law. It does not make the quantized rows independent, and gives no uniform error for arbitrarily long crossing trajectories. No finite-path-to-full-kernel passage with a usable entropy cost was proved.

## 7. Exact remaining failure and verdict

The new technical conclusions are (C235), (D235), the shifted-renewal transfer (T235)/(SR), and the independent skeleton bound (HK). These are not a tenth substantive finding. In particular the original assigned target remains unpaid even for d>=4, finite-support rows, and exact positive finite dependence range.

There are two precise unclosed constructions:

1. Produce a same-direction shared-Q multiwalk comparison with control of active-row r-proximity over decorated words, strong enough for the quenched tube/clipping and separated-stage estimates. Endpoint transience (HK) does not supply that control. In the complete iid source, the first adaptive failure occurs already at `fluct-short-block`: extending the passing mass from height s-1 to s leaves an endpoint law measurable below s, but under Q the row at s is not fresh. An m>r constant-mark connector fixes separation for one restart, while incurring lambda^(km) for k particles each time; no proof here propagates the relative-motion budgets and cumulative logarithmic losses through all of `gauss-diagonal`, `kernel-rapid-loss`, and `stage-prop`.
2. Construct the stationary episode array with a finite-window entropy bound relative to the ACTUAL Q law, with at most O(m) cost for m episodes after O(log N) conditioning entropy is averaged over O(log N) episodes. The precise failed iid identity is the assertion in `profile-entropy` that keeping the stopped slab and appending an independent full upper field preserves the reference field law. The finite-support seam example disproves that identity under Q; (CE) gives only a finite deterministic-window surface cost, not the required bound.

A direct proof of integrable tau would bypass both, but none was found. Fractional moments in D235 are deliberately not promoted to a first moment. No maximum or product of overlapping halfspace survival variables has been treated as independent. No exact-scope ballisticity counterexample was constructed or verified. This is a bounded research failure with technical progress, not a negative theorem about finite-range RWRE.
