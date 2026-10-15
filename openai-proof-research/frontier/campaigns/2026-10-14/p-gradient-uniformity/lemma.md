# R1 resolved: compact-p interior gradient regularity

2026-10-14. Independent support audit for I345, **not a new finding or an acceptance**. The source facts and the parameter-uniform deductions are distinguished below. This note closes only R1/U1 in the Opus proof review; it does not re-review I345 or its other dependencies.

## Lemma to insert in the proof

For every integer n≥2 and every finite P≥3, there are numbers

`theta=theta(n,P)>0` and `C=C(n,P)<∞`

such that, whenever `3≤p≤P` and `u∈W^{1,p}_loc(B_1)` is a bounded weak solution of

`div(|Du|^(p−2) Du)=0` in `B_1⊂R^n`,

its continuous representative satisfies

`||Du||_(L∞(B_(1/2))) + [Du]_(C^(0,theta)(B_(1/2))) ≤ C osc_(B_1)u`.       (R1)

There is no positive lower bound on |Du|, and no sign or noncritical-point hypothesis. The exponent can be decreased to lie in `(0,1/3]` if desired. Both constants are common over the entire closed p interval.

**Primary source:** Karen Uhlenbeck, *Regularity for a class of non-linear elliptic systems*, Acta Mathematica **138** (1977), 219–240, DOI `10.1007/BF02392316`: scalar specialization on p. 222, quantitative Theorem (5.4) on p. 238, and the proofs in Sections 1–5. [Original primary PDF](https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/6219-11511_2006_Article_BF02392316.pdf). The proof below verifies uniformity of its choices; it does not infer it merely from a fixed-p estimate.

## 1. Notation and common structural constants

Uhlenbeck's growth exponent is denoted s here, to distinguish it from the present p:

`rho(Q)=Q^s`, `s=(p−2)/2∈[1/2,S]`, `S=(P−2)/2`, `Q=|omega|²`, `omega=Du`.

Take her structural constant C=0. The de Rham gradient/curl complex has her identity (1.2), and `d omega=0`, `div(rho(Q)omega)=0` are her system (1.1). For now let the dimension m≥3. Fix

`a=min{1/2,1/(m−2)}`.                                      (7)

This is positive, at most every s under consideration, and strictly below the Sobolev upper restriction `2/(m−2)` used in Section 4. In particular the Sobolev exponent `2(1+a)` is one fixed admissible exponent.

The exact left side of (1.3) is `(1+2s)Q^s`. For x,y≥0,

`|s x^s−s y^s| ≤ S max{1,S} (x+y)^(s−a)|x−y|^a`.            (8)

To check (8), divide by `(x+y)^s`; on [0,1], t↦t^s is s-Hölder with constant one for 0<s≤1, while for s≥1 its Lipschitz constant is at most S. Since a≤s and a≤1, either estimate implies the asserted a-Hölder estimate. The zero/zero case is immediate. Thus her (1.3), (1.3)' and (1.4) all hold with the single choice

`K*=2+(1+2S)+S max{1,S}`.                                  (9)

This also bounds `|Q rho'(Q)|/Q^s=s`, including its continuous extension at Q=0. No derivative of rho at Q=0 is required by the theorem: rho is continuous there and differentiable for Q>0.

## 2. Uniformity before the perturbation step

**Read source facts.** Section 1 derives a nonnegative subsolution H with

`H'(Q)=rho(Q)/2+Q rho'(Q)`;                                 (1.7)

Theorem (1.10) gives a symmetric divergence-form operator with ellipticity bounds controlled by K*. Section 2's Moser statements and its weak-subsolution justification have constants controlled by those ellipticity bounds and the fixed Sobolev/mean-value exponents. Section 3 states that its constants depend on K; Lemmas (3.1) and (3.3), and Theorem (3.2), supply weighted differentiability, weighted Caccioppoli, and a local supremum estimate.

**Uniform deduction for this family.** Here choose

`H_s(Q)=(s+1/2)/(s+1) Q^(s+1)=(p−1)/p |Du|^p`.

Its prefactor lies between 2/3 and 1. The coefficient bounds in (1.10) are common by (9). Fix any one mean-value exponent strictly between 1 and `m/(m−2)` when applying (2.1), and one Sobolev exponent; neither is varied with p. In the proof of (3.2),

`|D sqrt(H_s(Q))| ≤ (S+1) Q^(s/2)|D omega|`.

Combining this with (3.1) and the fixed Sobolev/Moser constants proves a common version of (3.2): for balls `B_(4r)⊂D`,

`sup_(B_r) H_s(Q) ≤ C_2(m,P) r^(−m) ∫_(B_(4r)) Q^(s+1)`.   (10)

This is an operation-level check of that proof: the only additional s factor in passing from the weighted omega derivative to `D sqrt(H)` is bounded by S+1; the prefactor of H and its reciprocal are bounded by 1 and 3/2. Section 3's difference-quotient bounds use the common (1.3)' constants. In the scalar specialization, the potential for omega is u itself, so there is no varying-Lebesgue-exponent Hodge-potential estimate to leave implicit. The weak differentiability/subsolution justification in Sections 2–3 allows Q=0.

## 3. A common perturbation threshold in Section 4

This is the substantive uniformity check. Uhlenbeck's (4.1) fixes a positive relative reference size eta and concludes a 1/2-Hölder estimate from small L² excess. Fix `eta=1/2` once. Its lower reference size during iteration will be 1/4.

By homogeneity, normalize `sup Q=M=1`; M=0 is trivial. During the perturbation iteration all constant approximations can be projected to `|omega_i|≤1`, exactly as in the proof of (4.9). We maintain `|omega_i|²≥1/4`.

### Common constants in the linear approximation

For the normalized linearization in (4.2), the scalar gradient coefficient matrix at a nonzero reference w is

`I+2s (w/|w|)⊗(w/|w|)`.

Its eigenvalues are 1 and 1+2s, hence lie in `[1,P−1]`. The energy comparison and all constant-coefficient interior estimates in (4.2) therefore have common constants depending only on m,P.

The nonlinear comparison in (4.3) can also be bounded uniformly, without leaving the source's “combinatorial constant c(s)” unchecked. For precision use the ordinary flux Taylor remainder

`G_s(v,w)=[A_s(v)−A_s(w)−DA_s(w)(v−w)]/rho(|w|²)`.

The weak linearized comparison tested against its zero-boundary difference gives exactly the energy bound of (4.3) with this remainder. Put

`A_s(v)=|v|^(2s)v`, `F_s(v)=|v|^s v`.

On the unit ball, the derivative of A_s is uniformly Lipschitz for `s∈[1/2,S]`. Indeed, away from zero its second derivative has norm at most

`C_m q(q+3)|v|^(q−1)`, `q=2s∈[1,2S]`,

so it is bounded uniformly; integration along segments, split at zero if necessary, gives the same bound across zero. Thus the first-order Taylor remainder is at most `C(m,P)|v−w|²`. Dividing by `rho(|w|²)≥4^(−S)` is harmless. In particular, for the fixed a in (7), the normalized remainder G in (4.3) obeys

`|G(v,w)| ≤ C(m,P)|v−w|^(1+a)` whenever `|w|²≥1/4`.          (11)

There is a common inverse comparison for F_s on this set. If `R=max{|v|,|w|}`, integrating its positive derivative along the quarter of the joining segment nearest a maximal endpoint gives

`(F_s(v)−F_s(w))·(v−w) ≥ 2^(−S−2) R^s |v−w|²`.

Since R≥|w|≥1/2,

`|v−w| ≤ 2^(2S+2)|F_s(v)−F_s(w)|`.                        (12)

This explicitly controls the power-map comparison underlying the source's (4.6), uniformly in s. It covers v=0.

Let `E=∫|omega−w|²` on the fixed outer ball. The weighted estimate (4.8) has a common scalar constant directly: the differentiated coefficient `DA_s(omega)` has eigenvalues between `Q^s` and `(P−1)Q^s`; testing each differentiated equation against a cutoff squared times `omega_j−w_j` and applying Young gives a weighted-energy constant at most a fixed cutoff factor times `4(P−1)²`. Uhlenbeck's difference-quotient argument supplies the weak justification, including zeros of omega. Thus (4.8), on nested fixed balls, and the elementary bounds

`||DF_s(v)||≤(S+1)|v|^s`,

`|F_s(v)−F_s(w)|≤(S+1)|v−w|` for |v|,|w|≤1,

give

`||F_s(omega)−F_s(w)||_(W^(1,2)(inner ball))² ≤ C(m,P) E`.

Apply the fixed Sobolev embedding into `L^(2(1+a))`, then (11)–(12), then the energy comparison (4.3). The L² error of the linearized comparison field is at most

`C(m,P) E^(1+a)`.                                         (13)

This is precisely the small power gain required in (4.4); no compactness assertion about an unspecified function c(s) was used. Fixed half-ball rescalings only alter the common dimensional constants.

Combining (13) with the linear interior gradient estimate gives the one-step excess inequality of (4.9)–(4.11), with a single `C_3=C_3(m,P)≥1`:

`E_(i+1) ≤ C_3[t²+t^(−m) E_i^a] E_i`,

`|omega_(i+1)−omega_i| ≤ C_3 sqrt(E_i)`.                    (14)

The normalization and ball rescalings here are those of (4.11): `E_i` is the L² excess on the rescaled unit ball. Enlarging C_3 absorbs the fixed half-ball changes in the proof of (4.9). This is a slightly less optimized scalar form of the printed estimates, with eta already fixed and its lower size 1/4 absorbed into C_3.

### Explicit common choices

Choose

`t=min{1/8,1/(4C_3)}`,

`epsilon=min{1, 1/(256C_3²), [t^(m+1)/(4C_3)]^(1/a)}`.       (15)

Whenever `E_0≤epsilon`, (14) gives `E_(i+1)≤(t/2)E_i≤t E_i`. Moreover,

`Σ_i |omega_(i+1)−omega_i| ≤ C_3 sqrt(epsilon)/(1−sqrt(t))`

`≤2C_3 sqrt(epsilon)≤1/8`.

Since each projected reference has norm at most one, its squared norm differs from the initial reference's squared norm by at most twice this drift, hence at most 1/4. Starting with `|omega_0|²≥1/2` therefore preserves `|omega_i|²≥1/4` at every step, which closes the induction used in (11)–(14).

Uhlenbeck's (4.12)–(4.15) now give the small-excess theorem (4.1) with one threshold `epsilon_*=epsilon_*(m,P)>0` and one constant `K_4=K_4(m,P)`: the resulting exponent is the fixed 1/2. The change from (15)'s unit-ball convention to (4.1)'s B_2/B_1 convention uses only fixed radius/volume factors; decrease epsilon_* by those factors. All geometric series have common ratio at most sqrt(t). This proves actual common choices, rather than assuming local boundedness of fixed-s constants.

## 4. A common decay factor in Section 5, including critical points

**Read source facts.** Proposition (5.1) is an alternative at each radius: either `M(r)+C` decreases by a factor `1−lambda`, or a reference vector satisfies the excess and size hypotheses needed for (4.1). Its proof uses (3.3), the fixed linear weak Harnack bound (2.3), Poincare for `F_s(omega)`, factors `(s+1)²`, and powers of 2. It does not assume a positive lower bound for the original gradient.

**Uniform deduction.** The constants in these operations are common by Sections 1–3 above. Factors `(s+1)²` and `2^(2s+2)` are at most `(S+1)²` and `2^(2S+2)`. The maps involved in selecting the reference vector are radial homeomorphisms with exponents s+1∈[3/2,S+1]; their denominators and the reciprocal exponents are uniformly controlled. Thus choose a common `C_5=C_5(m,P)≥1` in all parts of (5.1).

On scanned p. 238 the two choices required in the proof of (5.4) are exactly

`1−C_5 sqrt(lambda) ≥ 2^(−(s+1)/2)`,

`lambda C_5 2^(s+1) ≤ epsilon_*`.                          (16)

One common sufficient choice is

`lambda_*=min{1/4, 1/(16C_5²), epsilon_* /(2 C_5 2^(S+1))}`. (17)

For the first inequality, the left side is at least 3/4, whereas the right side is at most `2^(−3/4)<3/4` for s≥1/2. The second follows directly. In particular the reference has size at least one half of the current maximum whenever the perturbation alternative is taken.

Choose

`theta=−log(1−lambda_*)/(2 log 4)>0`,

so that `sqrt(1−lambda_*)=4^(−theta)`, exactly (5.5). Since lambda_*≤1/4, theta<1/2. This is one positive exponent for the entire p interval.

The remaining proof of (5.4), on pp. 238–239, has two cases. Repeated decrease of M yields the geometric modulus `r^theta`; the first scale where the perturbation alternative occurs yields a 1/2-Hölder modulus, which is stronger than theta. If no such scale occurs, M tends to zero, so the modulus holds at a zero gradient as well. Its constants use only the common K_4, lambda_*, theta and fixed radius factors. Translating the argument to arbitrary centers as in (5.4) therefore proves a common estimate

`[omega]_(C^(0,theta)(B_(r/2))) ≤ K_0(m,P) r^(−theta) sqrt(M)`

whenever `sup_(B_r)|omega|²≤M`.                             (18)

This is the needed uniform reading of (5.4). The critical-gradient branch is the decrease alternative, not an application of a uniformly elliptic linearization at zero.

## 5. Oscillation normalization and completion of (R1)

The already reviewed Kotschwar–Ni bound in I345 §2.1 could supply the gradient maximum for (18). It is not needed here. The following gives a self-contained route using Uhlenbeck's (3.2).

Normalize the essential oscillation to one and subtract the essential infimum, so `0≤u≤1`. For a cutoff eta supported in B_1, equal to one on B_(7/8), with `|D eta|≤16`, testing the weak equation by `eta^p u` and using Holder gives

`∫ eta^p |Du|^p ≤ p (∫eta^p |Du|^p)^((p−1)/p)`

`                         · (∫|u|^p |D eta|^p)^(1/p)`.

This test is justified by Sobolev approximation; if the left side is zero there is nothing to divide. Otherwise,

`∫_(B_(7/8)) |Du|^p ≤ (16P)^P |B_1|=:E_*(m,P)`.            (19)

Apply (10) in balls centered in B_(3/4), with r=1/32, so the outer radius 4r=1/8 is contained in B_(7/8). Since H_s≥(2/3)|Du|^p,

`sup_(B_(3/4)) |Du|^p ≤ (3/2) C_2 32^m E_*=:A_*`.

Consequently

`||Du||_(L∞(B_(3/4))) ≤ max{1,A_*}^(1/3)=:L_*(m,P)`.        (20)

For every center x in B_(1/2), apply (18) on B(x,1/4)⊂B_(3/4). This gives the common local theta-Hölder bound for pairs separated by at most 1/8. For more distant pairs use `|Du(x)−Du(y)|≤2L_*≤2·8^theta L_*|x−y|^theta`. Thus the gradient norm plus its full B_(1/2) seminorm is bounded by one C(m,P). Restoring the oscillation proves (R1) in dimensions at least three.

For n=2, extend u constantly in one new coordinate. Fubini applied to compactly supported test functions shows that `u_tilde(x_1,x_2,x_3)=u(x_1,x_2)` is an actual weak p-harmonic function on `B_1^2×R`, hence on B_1^3, with the same oscillation bound. Apply the three-dimensional statement and restrict back to x_3=0. This is a **constant** extension, not the linear lift u+b used elsewhere in I345. The norm of the extended gradient equals the original one. This proves (R1) for every n≥2.

## 6. What this repairs

The lemma supplies one theta and C for every bounded-p subsequence in I345's bad-scale argument, including its finite-effective-viscosity branch and original critical gradients. In the notation of I345 §4, it yields the uniform Euclidean Taylor estimate `C r^(1+theta)` and therefore `lambda_i≤C s_i^theta`. This contradicts the selected lower bound once gamma_i<theta. No new assumption is imposed on the actual p-harmonic solution.

R1 is **resolved at author-audit level**, with an explicit primary proof trace. The historical reading gap U1 is closed for this support audit: all of Uhlenbeck Sections 1–5 were read, and the OCR-ambiguous thresholds were checked against rendered pages. This does not retroactively change what the Opus reviewer read, and is not an independent full-theorem PASS or a contribution decision. No claim is made to have formalized (R1) in Lean.
