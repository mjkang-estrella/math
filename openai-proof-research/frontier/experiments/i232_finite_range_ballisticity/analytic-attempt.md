# I232 early partial mathematical notes

Target selected at resumption: family 220 only. No theorem is claimed at this checkpoint. All pinned results/lower operations at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true.

Intended question: for d >= 2 (with available finite-range zero-one input only d >= 3), does a stationary ergodic uniformly elliptic nearest-neighbor random environment on Z^d, whose full rows on deterministic sets at distance > R are independent, satisfy positive directional speed whenever the annealed walk tends almost surely to +infinity in that direction?

Route A: inspect the iid mean-regeneration-time proof and try a forced, environment-independent buffer of length > R. Independence of deterministic separated sets is legitimate; independence after revealing the rows in the buffer is not automatic. A regeneration construction must specify precisely which rows are queried and whether failure excursions cross the intended cut. Mere existence of regeneration times would not give integrability.

Route B: inspect posterior/likelihood arguments and possible finite-color/block reduction. No bounded-radius iid-factor representation is supplied by the hypotheses; even if one were given, it would not by itself make the coarse walk nearest-neighbor iid RWRE. Any proposed comparison must preserve path probabilities and first moments.

Active counterexample search: one-dimensional transient zero-speed iid RWRE, layered embeddings (which violate finite-range row independence), local finite-dependent traps, and uniformly elliptic escape from a bounded-width trap. Need distinguish actual finite-dependent counterexamples from examples with long-range correlations, degeneracy, or dimension one.

Early logical constraint: the zero-one theorem concerns escape probabilities, not speed or moments. No implication from its conclusion to a finite regeneration mean is currently established here.

# Completed analytic continuation (supersedes the checkpoint's uncertainty)

## 1. Exact question and stipulated interfaces

Let d >= 2, U={+/-e_i:1<=i<=d}, and Q be a stationary ergodic Borel law on (Delta_U)^(Z^d). Assume deterministic kappa>0 and integer r>=0 such that Q-a.s. omega(x,e)>=kappa for every x,e, and F_A is independent of F_B whenever deterministic nonempty A,B (including infinite sets) have dist_infinity(A,B)>r. Dependence is on complete transition rows, not just a selected coordinate. P_x is the annealed nearest-neighbor walk. For a fixed nonzero ell, A_ell={X_n.ell -> +infinity}.

**Target, not proved:** P_0(A_ell)=1 implies X_n/n -> v deterministically, with v.ell>0. In d>=3 the stipulated finite-range zero-one theorem would permit replacing probability one by positive probability. Neither a common exceptional null set for every real direction nor uniform constants over Q,r,kappa is asserted. The proved A232 statement below is restricted to d>=3, the scope of the stipulated finite-range cut interface. No separate d=2 cut theorem is claimed. B232 has its own direct proof and does not require that interface.

The pinned iid manuscript's `thm:main` assumes the product law nu^(Z^d), d>=2 and uniform ellipticity. Its central unpaid-to-us input for extending speed is equation (5): for some beta in (0,1), every D>0 eventually Q(a_N<N^(-beta))<N^(-D), where a_N=P_(0,omega)(T_N<T_-1) after a coordinate reduction. Its `geom-speed` uses this estimate and iid renewal identities to get an integrable word duration. We accept all of that as true in its stated iid scope.

The pinned finite-range manuscript `thm:main` has exactly the row-independence contract above, d>=3, and concludes only the zero-one law. Its `lem:separated-weights`, `prop:cut-law`, `prop:mean-width`, and `prop:exact-cut-bridges` are also stipulated. In normalized height h(x)=(ell/||ell||_infinity).x, choose a coordinate step a with h(a)=1, mark weight lambda with 0<2lambda<kappa, and an integer M>dr+1. An M-step a-script with marks 0,1,...,1 has probability xi=lambda^M. Only star-mark departures use rows. Under D_h={h(X_n)>=0 for every n}, with p=P_0(D_h)>0, the marked words between script cuts are iid, their widths L have finite mean, and every word's active rows have h strictly below L-M. Full spatial-radius integrability in the finite-range source (`prop:radius-moment`) is stated under coexistence of both escape signs. The following first route removes that coexistence requirement for this intermediate estimate, by adapting the OTHER pinned manuscript's forward-template proof.

## 2. Route A: a buffered forward template

**Technical proposition A232 (d>=3).** Under the exact finite-range hypotheses above, if p=P_0(D_h)>0, then the radius R_word=max{|X_j-X_0|:j in one marked regeneration word} has finite mean under the stipulated conditioned word law. Thus this holds, in particular, when P_0(A_ell)>0. This is a technical extension of the pinned iid `geom-radius`, not a claim of a new-to-literature ballisticity theorem.

**Proof.** Use the stipulated iid marked words, put H_k=sum_(j<=k)L_j, and write R_j for their radii. If E R_1=infinity, I(s)=E min(R_1,s) is increasing, concave, unbounded and o(s). By E L in (0,infinity), choose c>0,C,C0 so that

    ck-C0 <= H_k <= Ck+C0  (all k>=0)

has probability >.95. Choose integer C1 with C1 c>C+4, then b>1/c, and eta>0 with 4 C1 eta<.1. For sufficiently large a0 (a scalar, not the coordinate step), let N be the least positive integer with I(a0 N)>=eta a0. Then N->infinity as a0->infinity, and eta a0<=I(a0 N)<2eta a0.

The first C1 N words obey both the displayed height bounds and

    sum_(j<=k) R_j <= a0 k  (1<=k<=C1 N)                 (A1)

with probability >.8. Here is the full estimate used: truncate R_j at a0 C1 N. Its mean is at most C1 I(a0 N)<2 C1 eta a0; the probability of any truncation among C1 N samples is at most 2 C1 eta. For a stationary nonnegative sequence Z, the maximal inequality

    P(max_(k<=n) k^(-1) sum_(j<=k) Z_j > a0) <= E Z_1/a0

costs a further 2 C1 eta. To prove that inequality, select disjoint witness intervals greedily among bad starting indices 1,...,m; they cover the bad starts and lie in 1,...,m+n. Their total sum exceeds a0 times the number of bad starts. Take expectations and then m->infinity. Adding the height exception gives the .8 assertion. No duration bound is used.

Fix large B>1. Choose i0 with sum_(i>=i0)P(L>i)<eta/(4B) and C(i-1)+C0+i<=(C+2)i for i>=i0. Then take a0 large enough that N>=i0 and I(B a0 i0)<eta a0/4. Tail integration and concavity give

    eta/(2B) <= Lambda := sum_(i=i0)^N P(R_i>B a0 i, L_i<=i) <=2eta.   (A2)

For clarity the lower bound before removing width exceptions is
[I(B a0(N+1))-I(B a0 i0)]/(B a0)>=3eta/(4B); the upper bound is I(B a0 N)/(B a0)<=I(a0 N)/a0. Count the indices in (A2) whose PRECEDING words also satisfy (A1) and the height bounds. Independence of the next word gives expected count >=.8 Lambda; its second moment is <=Lambda+Lambda^2, after dropping the preceding-word restrictions. Cauchy-Schwarz gives a positive count with probability >=c2/B, with c2 independent of B,a0.

On that event a site of word i satisfies |X_n|>(B-1)a0 i, while all heights so far lie in [0,(C+2)i]. For one of the 2d signed coordinate functionals u there is consequently

    Y(X_n)/(a0(1+max_(j<=n)h(X_j))) > c3 B,
    Y(x)=u.x+b a0 h(x),                                (A3)

for a fixed c3>0 and all sufficiently large B. Its union over u has raw probability >=p c2/B before leaving the strip defined by h>=0 and running h-maximum <=(C+2)N.

We prove an incompatible exponential upper bound, specifying the finite-range repair. Fix u and a first crossing sigma of Y/(a0(1+running h-maximum))>t before that exit. All earlier sites, and hence all active prefix rows, have Y<Y(X_sigma); the crossing overshoot in the ratio is at most b+1. Write s=||h||_1<=d (the norm of its coefficient vector). Choose a fixed integer m so large that

    m>C0+r s+2,
    b(m-C0)-1 > r b s+2.                               (A4)

Prescribe m steps in direction a, all with a constant-weight mark (for example mark 0). Their weight is lambda^m; their rows are NOT queried or revealed. From their endpoint prescribe a translated D_h path whose first C1 N words satisfy the .8 template. Up to its terminal cut, every site of template word k+1 has Y-increment from X_sigma at least

    m(b a0-1)+b a0(ck-C0)-a0(k+1)
    =a0[b(m-C0)-1+(bc-1)k]-m
    > r(1+b a0 s) >= r ||Y||_1                        (A5)

for sufficiently large a0, uniformly in k>=0. Hence every such site has infinity-distance >r from every earlier prefix row. The last cut has height above (C+2)N+r s for large N, by C1 c>C+4 and (A4). All later sites stay above that cut, so their height separation from every old prefix site is >r s, again giving infinity-distance >r. These are deterministic safe sets after fixing the prefix. Killing the translated suffix on entering the complement of their union shows that its entire event probability depends only on safe rows. The separated-weight lemma, applied to each fixed prefix, gives conditional raw probability at least

    epsilon0=.8 lambda^m p >0                         (A6)

for this continuation. There is no conditioning on the environment in the intervening collar, and no conditional independence assertion is needed.

This continuation exits the strip by the final template endpoint and increases the ratio by a bounded amount K independent of t,B,a0,N. Explicitly the positive part of the initial u-coordinate divided by the later denominator is <=t+b+1, the later b h-term contributes <=b, and the extra coordinate motion in template word k+1 is bounded by

    [m/a0+k+1]/[1+m+ck-C0].

This is uniformly bounded for a0>=1,k>=0; the finite connector has a bounded ratio contribution too. Choose K larger than all these fixed bounds. At thresholds 1+jK, sum (A6) over the finite first-crossing prefixes. It follows recursively that the probability of crossing the next threshold before strip exit is at most 1-epsilon0 times the previous crossing probability. Thus (A3) for this u has probability <=C' exp(-c'B). The finite union over u contradicts its lower bound p c2/B. This proves E R_word<infinity. The parameter order is: geometry constants, then B, then i0, then a0 large; m is fixed after geometry constants and r, before a0. QED.

**What this proves and does not prove.** Word endpoint increments have mean w with h(w)=E L>0. The vector strong law and R_j/j->0 give X_n/|X_n|->w/|w| on the event with a finite first cut. In particular under a.s. A_ell there is a deterministic limiting ray r_* with ell.r_*>0, and some signed coordinate is transient. Applying A232 again in that coordinate gives integrable radius for its marked words. If their duration tau has infinite mean, the truncated strong law gives the word count divided by elapsed time ->0, and the same radius estimates give X_n/n->0. If E tau<infinity, the velocity is w/E tau and has positive ell-projection. This renewal consequence is NOT a candidate finding; it makes the sole missing sign of speed explicit. It is consistent with pre-existing conditional LLNs.

## 3. Route B: posterior transport and a buffered inverse moment

**Technical proposition B232.** With the same row assumptions, in coordinate height, suppose p=P_0(T_-1=infinity)>0. Put q(x)=P_(x,omega)(never below x_1) and a_H(x)=P_(x,omega)(T_(x_1+H)<T_(x_1-1)). Then q(x)>0 Q-a.s. simultaneously for all x, a_H(x) decreases to q(x), and for some alpha>0 depending on Q,kappa,r,

    E_Q[q(0)^(-alpha)] < infinity.                    (B1)

**Proof.** Uniform ellipticity rules out staying forever in a bounded-height strip: blocks of upward steps leave it with a fixed positive probability. Hence a_H decreases to q. The event that q(j e1)>0 for infinitely many j belongs to the upper halfspace tail sigma-field. This tail is trivial: it is independent of every finite-coordinate cylinder by finite-range independence, thus independent of the full environment sigma-field and of itself. For each m, the union over j>=m has probability >=Q(q(0)>0)>0, so its decreasing limit has probability one. A finite upward path from 0 to such a j stays nonnegative and has positive quenched probability, yielding q(0)>0. Use translation and countability for all x.

Let F_H reveal all rows with 0<=x_1<H. For a_H>0, let mu_H be the normalized endpoint law at first hit H before -1. It is F_H-measurable because only departure rows below H contribute. Fix an integer m>r. The quenched Markov property and m upward steps imply

    q(0) >= kappa^m a_H integral q(x+m e1) mu_H(dx).    (B2)

All the fields q(x+m e1), x_1=H, depend only on rows at heights >=H+m. This entire halfspace is independent of F_H. If q(0)/a_H<s, the integral in (B2) is <s kappa^(-m), so more than half the mu_H mass has q(x+m e1)<2s kappa^(-m). Conditional expectation and Markov's inequality give

    Q(q(0)/a_H<s | F_H) <= 2 Q(q(0)<=2s kappa^(-m)).  (B3)

The endpoint q-values need not be independent of one another. The same statement holds at a finite F_H-stopping layer by partitioning according to its value.

Choose 0<delta<kappa such that rho=2Q(q(0)<=2delta kappa^(-m-1))<1. Let H_j=inf{H>=0:a_H<delta^j}. Since a_(H+1)>=kappa a_H and a_0=1, on H_j<infinity,

    a_(H_j)>=kappa delta^j.

The event H_(j+1)<infinity implies q(0)<delta^(j+1), hence q(0)/a_(H_j)<delta/kappa. Applying (B3) at H_j yields Q(H_(j+1)<infinity)<=rho Q(H_j<infinity). As {H_j<infinity}={q(0)<delta^j}, the lower tail is <=rho^(j-1). Choose alpha>0 with rho delta^(-alpha)<1 and sum over geometric bins. This proves (B1). QED.

This is the finite-range version of `geom-inverse`, with a real buffer inserted before the marginal-survival test. It does not silently treat upper rows at the unbuffered first-hit layer as fresh.

For each fixed number k and truncation floor e^(-B), bounded functions of q(x) at mutually widely separated x can be approximated in L1 by finite-row functions; those functions are independent once their supports have mutual distance >r. Thus the bounded-product mixing step of the pinned `kernel-inverse-moment` can also be transported, with constants depending on Q,r,k,B. This observation does not prove its subsequent adaptive rapid-loss or outward-order estimates.

## 4. Exact conditioning obstruction (an actual finite-dependent row field)

Let (eta_x)_(x in Z^d) be iid Bernoulli(1/2), let Z_x=eta_x+eta_(x+e1)-1, and choose 0<epsilon<1/(2d). Set

    omega(x,+e1)=1/(2d)+epsilon Z_x,
    omega(x,-e1)=1/(2d)-epsilon Z_x,
    omega(x,+/-ej)=1/(2d) for j>=2.

This is stationary ergodic, uniformly elliptic with kappa=1/(2d)-epsilon, and 1-dependent for complete rows including infinite deterministic sets. Indeed its hidden label sets are A union (A+e1), and these are disjoint for separated sets at infinity-distance >1. Rows at 0 and 2e1 are unconditionally independent. But conditioned on Z_e1=0, the events Z_0=-1 and Z_(2e1)=-1 each have probability 1/4 and their intersection is impossible. Thus even conditional independence of two separated row sets fails after a mediator row is revealed.

The obstruction exists under a WALK observation, not only direct revelation of an entire row. Start the walk at e1 and condition on its first step being +e1. Its environment likelihood is c+epsilon Z_e1 with c=1/(2d), so

    E[Z_0 | step]=E[Z_(2e1) | step]=epsilon/(4c),
    E[Z_0 Z_(2e1) | step]=0,
    Cov(Z_0,Z_(2e1) | step)=-epsilon^2/(16c^2)<0.

These follow by expanding independent centered fair bits: E Z_0 Z_e1=E Z_(2e1) Z_e1=1/4, while the three-factor centered moment vanishes. This is a counterexample to the tempting CONDITIONAL-INDEPENDENCE BRIDGE, not a counterexample to directional-transience-implies-speed; no directional transience is asserted for this example.

## 5. Active trap search, including an exact outside-scope trap

The primary searches are logged separately. They returned no verified stationary uniformly elliptic finite-range-dependent counterexample in d>=2. This is a bounded-search statement, not nonexistence.

A precise one-dimensional diagnostic is useful. Take iid rho_i equal to 4 with probability 1/4 and 1/4 with probability 3/4, and p_i=1/(1+rho_i). Then E log rho=-(log 4)/2<0, while E rho=19/16>1. The nearest-neighbor environment is uniformly elliptic (p_i in {1/5,4/5}). Here is a self-contained explanation of the trap mechanism, so no unread Solomon theorem is being used as evidence.

For the birth-death harmonic equation, scale increments obey s(i+1)-s(i)=rho_i[s(i)-s(i-1)]. The strong law for log rho makes the scale sum finite at +infinity and infinite at -infinity. Finite-interval hitting probabilities are affine in s; letting the boundaries tend outward shows that all positive levels are reached a.s., and that the probability of returning to a fixed level from level b tends to zero as b->infinity. Hence the path tends to +infinity a.s. The geometric decomposition into failed left excursions before the first right departure gives the extended-mean relation m_i=1/p_i+rho_i m_(i-1) for the quenched crossing time from i to i+1. Iteration from m_j>=1 yields, for every K>=0,

    m_i >= 1+2 sum_(k=0)^K product_(j=0)^k rho_(i-j).

Taking expectations and then K->infinity gives E m_i=infinity. This lower bound suffices; no subtraction of infinite expectations is used. To justify converting this to zero speed, construct each successive crossing using a fresh infinite sequence of independent uniforms. Its duration is a shift-equivariant measurable function of the iid environment and the corresponding fresh uniform sequence. The durations indexed by level are consequently stationary ergodic, so the truncated ergodic theorem gives T_b/b->infinity. Since X_t is bounded above by its running maximum, the hitting-time inverse and directional transience give X_t/t->0. This is the classical one-dimensional example, reconstructed here rather than nominated.

Its direct higher-dimensional lift fails the assigned dependence hypothesis. Give the +/-e1 transitions at x probabilities a p_(x1), a(1-p_(x1)) for 0<a<1, and all transverse transitions probability (1-a)/(2d-2). The horizontal embedded chain is the example above, so it tends to +infinity with zero speed; transverse coordinates are bounded-increment martingales and also have zero speed. But every row on a fixed hyperplane x_1=i encodes the same nondegenerate p_i. Arbitrarily distant row sigma-fields are therefore dependent. It is NOT an r-dependent counterexample for any finite r.

A fixed-width local trap cannot repair that lift. If every site of a set S has a nearest-neighbor exit path of length <=m, uniform ellipticity implies

    P_(x,omega)(T_(S^c)>jm)<=(1-kappa^m)^j,
    E_(x,omega)T_(S^c)<=m kappa^(-m),                  (T1)

uniformly in x in S and in the environment. Reapply the quenched Markov property every m steps to prove this. A tube of fixed transverse width has such a bound independently of its longitudinal length. Thus simply making a one-dimensional valley longer inside a fixed-width tube does not produce a duration exponential in its length. This does not exclude traps whose width grows, or correlated geometries defined by more complicated local constraints.

For a prescribed finite region V and a proper row event B with Q(omega(0) in B)=p_B<1, coloring Z^d by (r+1)^d residues yields

    Q(omega(x) in B for every x in V)
        <= p_B^(ceil(|V|/(r+1)^d)).                   (T2)

Choose the largest residue class in V. Its distinct sites have pairwise infinity-distance >r, and independence of collections makes those rows jointly independent. This only controls a specified all-B event. It is not a universal trap-volume bound: adaptive traps, many possible shapes, and conditional exploration laws are not covered. No inference of ballisticity from (T1)-(T2) is made.

The BZZ primary example has positive speed in BOTH opposite directions with positive quenched probabilities, and only polynomial mixing; it is neither a verified finite-dependent trap nor a zero-speed example. The stipulated finite-range zero-one law already prevents it from lying in the target class. Guerra's finite-dependent discussion retains (T), and Comets-Zeitouni retains a quantitative drift/moment condition. None closes the one-direction transience case.

## 6. Where both routes stop

A232 gives a limiting ray and B232 gives only a SMALL inverse moment. Neither gives E tau<infinity. A small inverse moment alpha>0 is compatible with a nonintegrable mean delay; replacing alpha by 1 without proof is invalid.

For route A, one must still establish sufficiently strong crossing control and propagate it through the MARKED renewal structure. In particular the iid identity with renewal masses u_n is not the marked identity: the finite-range source gives bar-u_n=0 for 1<=n<M and bar-u_H=xi u_(H-M) for H>=M. The iid nonnegative defective-convolution proof of superpolynomial width tails cannot be copied without dealing with this gap and shift.

For route B, the specific failed direct transfer is at the last sentence of the read proof of `kernel-outward-order`'s initial construction and at `profile-entropy`: a test using all rows below an adaptive layer H does NOT leave the rows at H fresh under Q. Appending m forced steps can restore separation from the old active rows for a specified path, but an unrestricted endpoint kernel still uses collar rows and can return to them. Also, splicing an independent full upper field onto a correlated lower field does not generally preserve Q at the seam. The pinned finite-range stopped-posterior comparison fixes a DIFFERENT, killed-path comparison; it assumes opposite escape signs and does not provide the same-direction many-walk Gaussian/rapid-loss/stationary-array package.

One explicit sufficient quantitative target to seek next is the analogue of pinned (5): after A232's signed-coordinate reduction, find beta in (0,1) such that for every D>0, Q(a_N<N^(-beta))<=N^(-D) for all sufficiently large N. This is an UNPAID ESTIMATE, not an added hypothesis advertised as a theorem. In addition, a rigorous marked-renewal conversion from that estimate to E tau<infinity must be supplied. An alternate terminal route is a direct proof of E tau<infinity for the existing marked words; we do not count that restatement as progress.

The more structural missing construction is a buffered version of the iid same-direction multiwalk kernels that simultaneously (i) keeps the tested endpoint laws measurable below their active cutoff, (ii) pays at most controlled logarithmic mass over the stages needed for outward order, (iii) proves vanishing projected-diagonal occupation rather than assuming contact harmless, and (iv) gives a valid finite-window reference-field entropy bound across each collar. We have proved no such construction. Fixed per-stage forcing costs alone are not a proof of these four requirements.

## 7. Contribution verdict

**Target unresolved in I232.** No finite-range ballisticity theorem and no counterexample in its exact scope. A232 and B232 have explicit analytic proofs relative to stipulated source interfaces; they are technical transport lemmas, not a tenth substantive finding. T1, T2, the mediator example, and the one-dimensional/layered diagnostic clarify why proposed shortcuts fail. No direct CLT, LLN, velocity-hemisphere corollary, or additional hypothesis restating the desired moment estimate is nominated. Parent-owned independent proof and contribution gates have not been run here.
