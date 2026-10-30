# S238 — independent correctness review, round 1

Correctness recommendation: **PASS**, relative to the expressly stipulated truth of the pinned operative source proofs. This is a recommendation to the parent, who alone adopts it. It covers the entire unchanged FROZEN.md and the submitted AUTHOR-PROOF.md, including their auxiliary mathematical assertions. No essential repair, additional hypothesis, narrowed conclusion, replacement pair, or unresolved mathematical verification is required. No contribution verdict, acceptance, or campaign count is assigned.

The reviewed statement is the 4,342-byte FROZEN.md with SHA256 `1e4dbb6345bf6f0c61bb589b394e6454f382f329f87eddbd3a91b1e18ce2f212`. The reviewed proof is the 26,676-byte AUTHOR-PROOF.md with SHA256 `c2faa9dfe4e993cd299503b7b5d365653e866742dc6df6560fe864d30727d654`. PREFREEZE.md and COMPARISON.md retain their historical chronology; neither an unfinished prefreeze sentence nor a later reading record replaces the final submitted argument.

The reasoning below is independent. No contribution review, parent assessment, peer result, other-round body, or registry/status information was read or used. Artifact authentication and mathematical assessment are separate. The exact author selection was authenticated before reliance, and all 83 admitted files and 14 recorded directories were baselined. The outside report and verification record give the final unchanged-original check. Reading/access limitations, including actual boundary-display exposures, are recorded separately in READING-LIMITS.md; no complete primary-literature or original-history clearance is claimed.

## 1. Exact source interfaces and the unchanged pair

I use O for the October 5 paper and S for the September 23 paper at immutable pin `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. These abbreviations refer to the admitted authenticated copies under `packet/private/canonical/preprints/Nonuniqueness-with-local-conservation-for-the-hard-sphere-Boltzmann-equation-October-5-2026/` and `packet/private/canonical/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/` of the author packet. Section-file references below are relative to each paper's `build/`. I independently read both drivers, preambles, all 22 section files, all three figure-code files, and both bibliographies. All 35 source blobs were independently checked against the complete pinned tree's Git blob identities; that authentication is not substituted for reading.

The exact O interface is stronger than either its headline alone or the older continuation theorem. O `paper/01-introduction.tex:75–177`, `def:admissible`, specifies:

* The spatial torus is initially R³/Z³ with volume one; velocities range over all R³. The sphere carries ordinary area, and the kernel and collision are exactly `a=(v-v*)·ω`, `v'=v-aω`, `v*'=v*+aω`, with Q± as in FROZEN.md. M is the same normalized Gaussian `(2π)^(-3/2) exp(-|v|²/2)`.
* F is nonnegative and weakly continuous in L¹ against every bounded measurable test, with F(0)=F0. For every finite T, `sup_{0≤t≤T} ∫ F(1+|v|²+|log F|)<∞`.
* With G=F/M, both Q±/(1+G) are in spacetime L¹ on every finite interval. For every C¹ β with β(0)=0 and `|β'(z)|≤Cβ/(1+z)`, the initial-trace distributional identity is `∫[Mβ(G)Dφ+β'(G)Qφ]+∫Mβ(F0/M)φ(0)=0`, for smooth periodic φ compactly supported in time and velocity.
* Total momentum is conserved. At every time, the global energy inequality and `H_M(F(t))+∫_0^t D(F)≤H_M(F0)` hold. D has the ordinary-area factor 1/4 and the nonnegative extended integrand Φ; this is the exact dissipation used in the submitted proof.
* The third velocity moment is spacetime integrable on each finite interval. For ψ=1,v1,v2,v3,|v|²/2 and every smooth compactly time-supported periodic φ, `∫Fψ(∂tφ+v·∇xφ)+∫F0ψφ(0)=0`. These are exact local mass, momentum, and kinetic-energy identities, with initial traces.

O `thm:main` supplies one nonnegative F0 with bounded initial velocity support and finite mass, energy, and absolute entropy, and two global solutions in this class differing on a positive spacetime-velocity measure set. It also states global strong L¹ continuity and all polynomial spacetime moments of Q++Q−. The stronger weighted continuity used by S238 is not inferred from that headline: O `paper/08-compactness.tex`, `prop:global-limits`, `comp:moment-envelope`, `comp:path-formula`, especially lines309–335,373–399,440–454, establishes every-time weak L¹ convergence along the selected subsequence, the unrenormalized equation with its initial trace, the strong transport integral formula, and strong continuity with every polynomial velocity weight. Its tail estimates and diagonal extraction over integer horizons and integer weights yield all finite horizons and all real k≥0 by domination. The source identifies the nonlinear Q± separately using uniform integrability and compactness, not an unjustified product of weak limits.

The datum is the one in O Section4 (`con:datum`), a truncated bath plus the infinite cold family. Both the dormant and each fixed-horizon cap approximation converge to precisely this datum; the vanishing cap seed does not change F0. Its velocity support is bounded initially, including the cold jets. No subsequent support restriction is inferred. The finite systems retire each cold color at `L_s=s^(-1/2)` by transferring it to the bath without changing the total. O Sections6–7 supply global control for these finite evolutions. Section8 then supplies global limits for both families, not merely a local solution followed by an arbitrary weak continuation.

The selection in O Section12 is also essential. One dormant global limit is fixed first. If cap limits agreed with it on arbitrarily small cap horizons, the source chooses finite approximants diagonally against rescaled compact tests. The dormant normalized density vanishes off the axis; the cap-hit dilation has a nonzero limit; Sections10–11 force its dilated horizon U to be finite. Thus the ratio of the two scales tends to `1/U>0`. Positivity transfers dormant vanishing through this nondegenerate dilation and contradicts the nonzero cap limit. Consequently a sufficiently small cap horizon supplies a cap global limit with positive spacetime-velocity separation from the fixed dormant limit. There is one common datum, and the difference survives the actual final limits and global construction. S238 selects this already furnished pair, without a new sequence, restart, concatenation, or selection condition.

For comparison, S `sections/02-framework.tex`, `def:admissible`, and `06-admissibility.tex` give the older global renormalized class: weak continuity, finite entropy/moments, separately renormalized gains/losses, local mass and total momentum, and energy/entropy-dissipation inequalities. Strong L¹ continuity and integrable gains/losses hold on its common early interval. Its later continuation uses the older renormalized existence interface, which does not by itself provide O's global local momentum/energy identities. I read S's full construction and separation, but do not use its weaker continuation to justify O's stronger conclusions. Nor do I audit the stipulated source proofs.

Finally, O `paper/02-framework.tex:4–12` rotates space and velocity together so the irrational jet direction becomes e3, and rotates the lattice to Λ. The quotient R³/Λ still has volume one. Rotating both coordinates back is an isometry from this quotient to the original standard torus; treating the rotated function as Z³-periodic without this map would be wrong. Simultaneous rotation preserves |a|, sphere area, velocity Lebesgue measure, M, radial weights, transport, and Φ. Scalar entropy transforms by composition, vector flux by the orthogonal matrix, and divergence covariantly. No normalization or torus-volume factor is lost. The proof's rotation paragraph is sufficient.

## 2. Simultaneous envelopes, compression, and fixed parameters

The needed source bounds hold simultaneously for both finite families and all their active and retired colors. They are not independently chosen estimates requiring incompatible parameters.

O Section4 fixes `s_j=s0 exp(-jη)`, `d_s=d0 s^10`, `L_s=s^(-1/2)`; q lies strictly between 1 and 2. The positive mesh η, K, α, γ, s0, d0, bath parameters, and the chosen cap horizon are fixed in the source's actual parameter order. Constants below may depend on that fixed construction, on the finite review horizon τ, and on the moment order. In particular factors depending on 1/(αγ), 1/(1-exp(-η)), d0, or 1/(2-q) are allowed. No uniformity as those construction parameters degenerate is claimed.

O `cold:geometry`, `cold:upper`, `cold:barrier`, `cold:core-amplitude`, `cold:nonmain` in `paper/05-cold.tex` give the exact required inputs. Different active enlarged tubes, including signs and periodic lifts, are disjoint. The source's A_s(t) in Section8 is the union of the scale-s representatives in one spatial cell; it is empty after retirement and satisfies `|A_s(t)|≤Cτ s²` for 0≤t≤τ. The axial length is O(1+t), already included in Cτ. Periodic unfolding counts the full union, not just one copy. Disjointness leaves at most one main color at a point, and the complete nonmain sum, including periodic copies, has a Gaussian bound. There is no additional unnoticed spatial, sign, or periodic multiplicity in S238's sums.

Each active color has the deterministic bound `c_i≤U_i=f_i+ε_s m_i`, where `ε_s=C_*L_s d_s/s=C_*d0 s^(17/2)` is bounded by the source choices. While t≤L_s, the barrier has velocity coefficient at most `C s^(-1)d_s^(-3)`, axial center |U|≤1+α<2, and Gaussian velocity factor at least as decaying as `exp(-|v-Ue3|²/d_s²)`. Its time multiplier is at most e; its spatial damping is at most one. The free core satisfies f_i≤m_i.

The actual compressed core measure matters. Write `S=sech²(γ(z_c-tp3)/s)` in the source's notation. The source formula is

`f_i(t,x,p) dp = [K S/(s+tαγS)] J(w) dw`

with masks between zero and one, `p̄=d_s w̄`, and `p3=a_s^σ(z_c-tp3)+d_s w3`. Here J is fixed, bounded, smooth, and supported in the unit ball. Differentiating the last equation, using `(a_s^σ)'=αγS/s`, gives

`dp3/dw3 = d_s/[1+t(a_s^σ)']`,

and the full velocity Jacobian is `d_s³/[1+t(a_s^σ)']`. Monotonicity yields `|p3-U|≤d_s|w3|`, with bounded U. The measure coefficient is at most `K max(1,(αγ)^(-1))/(t+s)`; hence its mass is O((t+s)^(-1)). These estimates hold also at t=0.

An adversarial concern is that a Gaussian bound on the w-measure does not imply a Gaussian density bound in p after compression. The proof does not make that inference. Its height estimate uses the separate source bound f_i≤m_i. Indeed the actual Jacobian also explains it directly: division by `d_s³ s/(s+tαγS)` gives density `K S/(s d_s³) J(w(p))`, with the masks. Thus the cancellation gives the required s^(-1)d_s^(-3) height, while the pushforward coefficient gives the different, time-decaying mass bound. This is an expansion of an explicit source formula already cited in the proof, not an essential new density argument supplied to repair it.

The remainder mass is

`ε_s ∫m_i dv ≤ C (L_s d_s/s)(1/s) = C d0 s^(15/2)`.

Its Gaussian width is comparable to d_s and its center is bounded and axial. While active, `(t+s)s^(15/2)≤(s^(-1/2)+s)s^(15/2)` is uniformly bounded; hence its mass is also ≤C/(t+s). Both exponents, 17/2 for ε_s and 15/2 for its mass, are correct.

The early bath/cap and global continuation bounds in O Sections6–7 put the non-cold part, including every transferred retired color, below CτH, with

`H(v)=exp(-|v|²)<v>^(-100)(1+|v̄|^(-q))`.

Retirement does not discard a component or create a total-density jump. At the instant of transfer one may use the pretransfer active bound or the posttransfer bath bound supplied by the source. The source's global estimates, rather than an unproved sum of separate retired-color norms, are what control H. The source already makes d_s smaller than 1/4 (indeed smaller geometric thresholds occur); the completion-of-squares threshold in S238 is not an additional parameter restriction.

## 3. Equations (2.2)–(2.4), every-time transfer, and null sets

The Gaussian calculation is exact. For d≤1/4 and |U|≤2,

`-|v-Ue3|²/d²+4|v|² = -(d^(-2)-4)|v-Ue3/(1-4d²)|²+4U²/(1-4d²)`.

The last term is uniformly bounded. Since `s^(-1)d_s^(-3)=d0^(-3)s^(-31)`, the barrier bound and bounded ε_s imply `(2.2) U_i≤C s^(-31) exp(-4|v|²)`. There is neither a missing compression factor nor a change of width exponent. The nonmain sum is Gaussian and the bath is bounded by H. Off all A_s, the logarithm is bounded by a constant plus qℓ; on A_s it gains at most `31|log s|` plus a constant. The elementary inequality `log(1+|v̄|^(-q))≤log2+qℓ(v)` with `ℓ=log⁺(1/|v̄|)` then proves `(2.3) log⁺F≤Cτ c+qℓ`.

For `(2.4)`, the transverse relation is exactly `p̄=d_s w̄`; no axial Jacobian estimate is being mistaken for a transverse one. Thus

`ℓ(p)≤|log d_s|+log⁺(1/|w̄|)`, and `<p>^k≤C_k<w>^k`.

The latter uses bounded U and the monotonicity estimate above. A fixed Gaussian dominates J. Its logarithmic transverse integral is finite because `∫_0^1 r|log r|dr<∞`. The core therefore contributes at most `C_k(1+|log d_s|)/(t+s)≤C_k e_s/(t+s)`, where `e_s=1+|log s|`. Applying the ordinary centered Gaussian change of variables to the remainder gives `C_k e_s s^(15/2)`, again ≤C_k e_s/(t+s) during activity. H contributes a finite constant for every real k: near the axis the only extra integral is `∫_0^1 r^(1-q)|log r|dr<∞`, and the Gaussian controls every polynomial order at infinity. The complete nonmain sum has the same property. This establishes all moment orders in `(2.4) J_k≤Cτ,k b` for the approximants.

Passing this information to the limit requires the precise every-time source convergence. The correct deterministic majorant at a fixed t is

`E(t,x,v)=CτH(v)+Σ_i 1_{O_i(t)}(x) U_i(t,x,v)`.

The sum includes the actual main cores and remainders. Its integral is bounded by `Cτ[1+Σ_s s²/(t+s)]≤Cτ[1+Σ_s s]`, with the harmless remainder already included. Thus E(t) is integrable at every t, including zero and retirement times. This is not the globally nonintegrable loose height majorant `Σ_s 1_{A_s}s^(-31)e^(-4|v|²)`. The proof explicitly makes this distinction.

For each fixed time, the source's same selected subsequence converges weakly in L¹. Testing `F_N(t)≤E(t)` by arbitrary nonnegative bounded phase tests passes this order inequality to F(t). This gives the pointwise bound needed for (2.3). For R_k and J_k, truncate the nonnegative velocity test, multiply by an arbitrary nonnegative bounded spatial test, pass weak convergence, and then apply monotone convergence. The integral order inequality for every spatial test yields the stated a.e.-in-x moment bound. Constants and the right-hand spatial envelope are independent of N.

These arguments are for each t, not just for a.e. t. The phase-space null set on which a pointwise inequality fails may depend on t; that is harmless for the L¹-valued continuity conclusion. The moment integrands and envelopes are jointly measurable, and Tonelli handles their spacetime versions. The velocity axis has Lebesgue measure zero, so values assigned to ℓ there do not affect phase integrals. Later collision changes of variables are justified for nonnegative measurable truncations, which also avoids assuming a collision fiber cannot meet the axis. No alteration of F at exceptional times is made.

## 4. Disjointness algebra and logarithmic summation

With the definitions in (2.1), off the tubes a=b=c=1. At a point in A_s, set h=1/(t+s) and e=e_s. Then `a=1+h`, `b=1+eh`, `c=1+e`, so

`ca-b=e+h≥0`.

Also `(1+h)²≤2(1+h²)` and 1+e≤2e. Consequently

`∫_0^τ∫ ca² ≤ Cτ[1+Σ_s e_s s²(τ+∫_0^τ(t+s)^(-2)dt)]`

and `∫_0^τ(t+s)^(-2)dt=1/s-1/(s+τ)≤1/s`. This proves (2.5)–(2.6), with the finite contribution of τ absorbed into Cτ. Integrating up to τ even when L_s<τ only enlarges the estimate, so retirement causes no missing interval. Disjointness is what prevents cross-scale quadratic products.

Since all s_j<1, `e_{s_{J+n}}=e_{s_J}+nη` and `s_{J+n}=s_Jρ^n`, ρ=exp(-η). Therefore

`Σ_{j≥J}s_je_{s_j}=s_J[e_{s_J}/(1-ρ)+ηρ/(1-ρ)²]`,

exactly (2.7). The s² terms are bounded by the s terms. For the first j with s_j<ε, use s_j≤ε and monotonicity of `s(1-log s)` on (0,1) to get `C ε(1+|log ε|)`. The constant can depend on the fixed η; it is not mesh-uniform. These computations include the entire union A_s in one cell, whose source volume bound has already included signs and periodic copies. The same sum controls the later small-tube entropy cost uniformly in t. No spatial factor or missing horizon dependence is suppressed.

## 5. Outgoing-sphere logarithms and gain bounds

Here I rederive the estimate without relying on a differently normalized primary representation. For σ uniform on S², each coordinate σ1 is uniform on [-1,1]. For any h∈R² and 0<ε≤1,

`P(|h+σ̄|<ε)≤P(|h1+σ1|<ε)≤ε`.

The containing interval has length at most 2ε, and the marginal density is 1/2. This is independent of h, including tangency. Layer cake gives

`E log⁺(1/|h+σ̄|)≤∫_0^∞ e^(-u)du=1`.

For any center c0 and radius r>0, set h=c̄0/r and use `log⁺(1/(rz))≤log⁺(1/r)+log⁺(1/z)`. The result is precisely (3.1). Its r-dependence is explicit; the proof does not falsely assert a radius-independent average at r→0. The probability bound also proves the axis preimage is area-null for r>0.

For g=p−ξ≠0 rotate g/|g| to e3, write u=e3·ω, and put `σ=e3−2uω`. Then the output is `(p+ξ)/2+(|g|/2)σ`. On each open hemisphere, σ3=1−2u² and the azimuth is either unchanged or shifted by π. Hence `dσ=4|u|dω` on each sheet. The two hemispheres give two preimages outside null boundaries. Multiplying by |g||u| gives `( |g|/2 )dσ` after their contributions are added. Thus the exact coefficient in (3.2) is correct, and φ=1 gives total rate 2π|g|, with ordinary sphere area 4π. No normalized probability measure has been substituted into Q.

The map on (v,v*) for fixed ω is an orthogonal involution in center/relative coordinates: the center is fixed and the relative vector is reflected. Its absolute six-dimensional Jacobian is one, and it preserves |a|. For nonnegative measurable tests, first use bounded truncations and then monotone convergence. This extends both the gain involution and the outgoing-sphere identity to the unbounded ℓ without prior integrability assumptions. If g=0, the kernel is zero; every bounded truncation has zero contribution, so its limit is zero even when the output lies on the axis. There is no undefined operative 0·∞ at zero speed.

Tonelli and these identities give, at almost every (t,x),

`∫Q⁺ℓ dv ≤2π∫F(p)F(ξ)|p−ξ|[1+log⁺(2/|p−ξ|)]dpdξ`.

Since `z log⁺(2/z)≤2/e` and `|p−ξ|≤|p|+|ξ|`, this is ≤C(R0R1+R0²)≤CR0R1. This proves (3.3), including the near-zero-speed regime. The same nonnegative change of variables with test one yields `∫Q⁺=∫Q⁻≤CR0R1`, (3.4). All integrability conclusions are derived after Tonelli; none is assumed to authorize the changes of variables.

## 6. Positive logarithms and negative loss logarithms

The frequency is exactly `ν_F(v)=2π∫|v-p|F(p)dp≤C<v>R1`. With (2.3)–(2.4),

`∫Q⁻log⁺F ≤C R1(cR1+J1)≤C[a(ca)+ab]≤Cca²`.

This needs moments of order one, and b≤ca is used in the last step. For the gain,

`∫Q⁺log⁺F ≤C c∫Q⁺+q∫Q⁺ℓ≤C cR0R1≤Cca²`,

since c≥1. The positive-log estimates are therefore integrable by Section4 of this review. Source polynomial integrability alone would not prove them.

For z≥0,w≥1, `z log⁻z≤wz+C exp(-w/2)`. If z≥exp(-w), then log⁻z≤w; if 0<z<exp(-w), put z=exp(-u), u>w, and bound `u exp(-u)≤C exp(-w/2)` using the boundedness of u exp(-u/2). At z=0 both sides are meaningful with the stipulated zero convention and the inequality holds. Taking w=<v>² and multiplying by the frequency estimate gives

`∫Q⁻log⁻F ≤C R1[∫<v>³F+∫<v>exp(-<v>²/2)]≤C R1(R3+1)≤C(a²+a)`.

Thus the moment orders R1 and R3, and all factors of a,b,c in (4.2)–(4.5), are correct. The Gaussian residual is integrable over velocity; spatial volume is finite; a²+a is integrable because c≥1 and (2.5) holds. This proves absolute loss-log integrability independently of any entropy equality.

## 7. Vacuum transfer and negative gain logarithms

Let μ be the nonnegative collision measure `|a|dt dx dv dv* dω`, A=F'F*', B=FF*. The exact source entropy inequality gives `∫Φ(A,B)dμ<∞`. Also `∫(A+B)dμ<∞` by (3.4) and ∫a²<∞. These are statements about the already chosen limit.

The loss-log estimate and exchange v↔v* give `∫B(|log F|+|log F*|)dμ<∞`. Apply the measure-preserving collision involution to obtain `∫A(|log F'|+|log F*'|)dμ<∞`; hence `∫A|log A|dμ<∞`. On A=0 these weighted expressions are defined as zero, just as B-weighted expressions are on B=0. This convention does not assume anything about Q⁺ on the phase-space vacuum.

For A,B>0, the three-ratio proof of (4.8) is valid. If A/B≥2 then A−B≥A/2, and if A/B≤1/2 then B−A≥A. In either outer regime Φ controls the corresponding `A|log(A/B)|` (with coefficient at most 2). In the middle regime the latter is ≤A log2≤(A+B)log2. Thus

`A|log(A/B)|≤2Φ(A,B)+(log2)(A+B)`.

Combining it with `A|log A|` controls `A|log B|` on the positive quadrant. This controls the logarithm of the product, not yet the two individual negative logarithms.

For zero products, the extended Φ is infinite if exactly one of A,B is positive and is zero if both vanish. Finiteness of its nonnegative integral makes the mismatch set collision-measure-null. Therefore `A=B=0` μ-a.e. on {AB=0}. In particular `∫1_{F(v)=0}A dμ=0`. Tonelli implies `Q⁺=0` a.e. on the spacetime phase zero set of F. The loss is `Fν_F` with finite ν_F at a.e. (t,x,v), because R1 is finite a.e., so Q⁻ vanishes there too. This proves the frozen zero-set assertion before any logarithmic chain rule or entropy equality is used. A different representative on a phase null set does not change this result: lifts of such sets remain null under Tonelli and the collision involution.

To extract an individual negative logarithm, the submitted proof uses, correctly,

`log⁻F(v)≤|log B|+log⁺F(v*)` on A,B>0.

For log F(v)<0 this is the identity `−log F(v)=−log B+log F(v*)` followed by inequalities; for log F(v)≥0 it is trivial. This is the step that handles potentially large opposite logarithms cancelling in log B. Its last term, after multiplication by A, is integrable by the positive gain-log estimate with v and v* exchanged. Thus `∫Q⁺log⁻F<∞` follows. The A=B=0 set contributes zero, and the mismatch set is already null. Equations (4.9)–(4.11) therefore use only proved zero conventions and contain no circular use of equality.

The subsequent passage from log F to log(F/M) is justified by `|log M|≤C<v>²` and the source polynomial collision bound of order two. It yields (4.12). At this stage all signed collision expressions needed later are absolutely integrable; Fubini may be applied to obtain a common a.e.-(t,x) set where the velocity and collision computations are legitimate. Source polynomial integrability is used here for the Gaussian logarithm, not substituted for the separately proved log F bound.

## 8. Uniform weighted entropy integrability and every-time continuity

For every z≥0, `0≤η_M(z,v)≤z log⁺z+C<v>²z+M`. The function z log⁺z is increasing. Equations (1.1),(2.3),(2.4) give (5.2), using R_k,J_k,R_{k+2}. On a small active tube A_s this is bounded by `Cτ,k e_s[1+(t+s)^(-1)]`. Integrating its spatial volume and using t+s≥s yields the uniform small-scale cost

`sup_{0≤t≤τ} ∫_{U_ε(t)×R³}<v>^kη_M(F(t))≤Cτ,k Σ_{s<ε} e_s(s²+s)≤Cτ,k ε(1+|log ε|)`.

This includes t=0 and all retirement times because the deterministic estimates were passed at every time. Retirement can remove a tube from U_ε but its material is then controlled by the bath estimate. No discontinuity of total F is introduced.

Outside U_ε(t), only finitely many scales can be main. Their heights, the complete nonmain bound, and the hot bound give the time- and space-independent velocity majorant `G_ε=Cτ,ε(H+e^(-4|v|²))`. Its constant need not remain bounded as ε↓0. The entropy is dominated there by

`D_ε,k=<v>^k[G_εlog⁺G_ε+C<v>²G_ε+M]`.

Near the transverse axis the worst local factor is `r^(-q)(1+|log r|)`, integrable in two transverse dimensions because q<2. Axially and at large velocity the Gaussian controls every real polynomial weight. Finite spatial volume makes this an L¹ function of phase space.

The moving-set issue is resolved correctly. Given a phase set E, split it by U_ε(t) at the same time t. First choose ε so the entire small-tube integral is small for every t. On its complement, absolute continuity of the integral of the fixed D_ε,k makes the integral small whenever |E| is small. This proves uniform integrability without choosing a fixed union of all moving tubes. For velocity tails make the same first choice and then choose R so `∫_{|v|>R}D_ε,k` is small. This proves tightness on the unbounded velocity space. Uniform integrability alone on an infinite-measure domain would not have sufficed.

For t_n→t, the existing strong L¹ continuity of F gives convergence in measure on each bounded velocity cylinder. Since M is positive and bounded away from zero there, the continuous map `(z,v)↦η_M(z,v)` preserves this convergence in measure (equivalently use the subsequence a.e. criterion). Multiplication by <v>^k is bounded on the cylinder. Vitali gives weighted L¹ convergence there, and the uniform tails give it on the whole phase space. Every real k≥0 is covered directly or by a larger integer weight. No exceptional-time redefinition is involved: the bound and the source strong representative are available at each prescribed t. In particular the limit at zero is η_M(F0), not an unspecified entropy trace.

Finally `||s(t_n)−s(t)||_{L¹_x}≤||η_M(F(t_n))−η_M(F(t))||_{L¹_{x,v}}`, and the analogous inequality for J uses |v|≤<v>. This proves the asserted L¹_x continuity of both s and the vector J. There is no claimed quantitative modulus uniform in the construction parameters.

## 9. Characteristic L¹ formula and the regularized chain rule

The source gives the unrenormalized distributional equation and Q∈L¹ in spacetime, in addition to strong L¹ continuity and its initial trace. On R³/Λ set `f#(t,x,v)=F(t,x+tv,v)` and `q#=Q(t,x+tv,v)`. Periodic translations preserve spatial measure. The transport group is strongly continuous on phase L¹, including unbounded velocity space, by approximation with smooth compact-velocity functions and its isometry property. Thus f# is L¹-continuous. Pulling back smooth periodic compact-velocity tests transforms the transport equation to `∂t f#=q#`. Subtract `F0+∫_0^tq#` in L¹. The difference has zero distributional time derivative, hence is constant, and the strong initial trace makes that constant zero. This gives (6.1) for every t, agreeing with `comp:path-formula`.

Joint measurability and the isometric change of variables give q#∈L¹. Fubini produces, for a.e. (x,v), an absolutely continuous scalar representative `F0(x,v)+∫_0^tq#(u,x,v)du`. It agrees with f# as an L¹ function at each t. It is nonnegative on the entire time interval: it is nonnegative for a.e. time on a.e. characteristic, and scalar continuity removes possible negative values at individual times. This construction does not change the original L¹-valued solution at any time.

For fixed δ∈(0,1], `η_δ(z,v)=M[(z/M+δ)log(z/M+δ)−(z/M+δ)+1]` is C¹ in z≥0 with derivative log(z/M+δ). On each scalar absolutely continuous curve and compact time interval, its argument is bounded and M(v)>0 is fixed. Its derivative is therefore bounded on that curve's range. The ordinary scalar chain rule yields (6.3); no global L∞ bound is required.

The uniform estimate `|log(G+δ)|≤|log G|+log2` for G>0 follows by splitting G≥1, G+δ≤1, and G<1<G+δ. On G=0 the already proved Q⁺=Q⁻=0 makes the product with log δ vanish a.e. Equation (4.12) is consequently a δ-independent collision dominator even at vacuum. The proof is not attempting to insert the unbounded logarithm into the source's bounded-derivative renormalization class.

The scalar function y log y−y+1 is nonnegative. Also `(z+δ)log⁺(z+δ)≤C[1+z+z log⁺z]`. After multiplication by M and using `M G log⁺G≤F(log⁺F+|log M|)`, this gives (6.5). Its zeroth and first velocity moments are spacetime integrable by the bounds already proved; they are integrable at t=0 as well. In particular η_δ(0,v)=M(δlogδ−δ+1) has the correct limit M, matching the frozen definition η_M(0,v)=M. The initial convergence is therefore dominated even on vacuum.

These are explicit checks of the operations already present in Section6, not a replacement argument added to remedy a missing regularity hypothesis.

## 10. Removing δ and velocity cutoffs

Integrate the scalar characteristic identity against a smooth periodic test compactly supported in time and velocity, change variables back, and integrate by parts in time. The initial term is η_δ(F0)φ(0). The dominator (6.5) handles the density and transport terms, including the |v| factor, and (4.12),(6.4) handle the collision term. Dominated convergence as δ↓0 gives exactly

`∫η_M(F)Dφ+∫Q log(F/M)φ+∫η_M(F0)φ(0)=0`.

This is the kinetic logarithmic identity with the stipulated zero convention now justified. It is not inferred from the preexisting renormalized identity alone.

For φ(t,x)χ_R(v), transport differentiates t and x only. There is no derivative of χ_R in this equation and no artificial boundary term in velocity. The time-derivative term is dominated by the zeroth entropy moment, the spatial derivative by the first entropy moment, the collision term by (4.12), and the initial term by the initial relative entropy. Letting R→∞ proves (6.7). The limiting equation retains its initial trace and its flux; there is no missing velocity or entropy defect. Smooth cutoffs suffice and no monotonicity of χ_R is required for dominated convergence.

## 11. Absolute symmetrization, factor 1/4, and all endpoints

Equation (4.11) implies absolute collision integrability of `(A+B)|log F(v)|` on spacetime. Velocity exchange gives the same statement for log F(v*); the collision involution gives it for the primed logs. Thus for a.e. (t,x), all terms below are absolutely integrable. On the positive quadrant write

`I=∫Q log F dv=(1/2)∫(A−B)(log F+log F*)|a|=(1/2)∫(A−B)log B |a|`.

Under the involution this is `−(1/2)∫(A−B)log A |a|`. Averaging yields

`I=−(1/4)∫(A−B)log(A/B)|a|=−d_F(t,x)`.

The first half comes from exchange of the two particles, and the second half from averaging pre- and postcollisional expressions. Sphere area remains ordinary area throughout; no extra 2π factor belongs in d. The zero-zero set contributes zero, and the single-zero mismatch set is μ-null by Section7. Consequently this is exactly the frozen extended Φ integral, not a new convention for dissipation. All changes of variables and Fubini are now absolute, rather than formal subtractions of infinite expressions.

The function log M is a constant minus |v|²/2. Its integrals against Q± are absolutely integrable by the source weight-two collision bound. The same symmetrization with this polynomial test has zero collision bracket, by conservation of pair energy and particle number. Hence `∫Q log M=0` and `∫Q log(F/M)=−d_F`. This cancellation is local in (t,x); no appeal to global conservation alone is being used.

The source entropy inequality already gives `d_F∈L¹([0,τ]×T³)` and nonnegativity. Substitution into the cutoff-free identity gives exactly

`∫_0^∞∫[s ∂tφ+J·∇xφ−d_F φ]+∫s(0,x)φ(0,x)=0`,

or `∂t s+div_x J=−d_F`. The sign and initial boundary term agree with FROZEN.md. s and J have the proved continuous L¹_x representatives.

Taking φ constant in space shows the continuous function `h(t)=H_M(F(t))` has distributional derivative `−D(F(t))∈L¹(0,τ)`. Hence h agrees a.e. with an absolutely continuous function. Two continuous functions agreeing a.e. agree everywhere; the initial term fixes its value to H_M(F0) at zero. Thus, for every `0≤a≤b≤τ`,

`H_M(F(b))+∫_a^b D(F(t))dt=H_M(F(a))`.

This uses the same original F(t) at all endpoints, including zero and retirement instants. The value assigned to D on individual null times is immaterial to its integral. Since τ was arbitrary, all finite endpoints in the frozen global assertion are covered.

## 12. Objections, alternatives, and closure of the complete scope

The concrete concerns investigated and resolved were these:

| Potential correctness objection | Resolution in the submitted argument and admitted source |
|---|---|
| Only the weaker September or headline interface is available. | O Section8 explicitly supplies the stronger every-time weighted mild/compactness interface for both global families; O Section12 supplies the final separated pair. |
| Rotation changes the standard torus or angular normalization. | Space, velocity, lattice, and angular variables rotate together; the covolume-one quotient is mapped back isometrically. |
| Axial compression invalidates a Gaussian density estimate. | The proof uses f_i≤m_i for the height and the actual pushforward measure for mass/log moments; the exact Jacobian confirms their distinct roles. |
| Large-scale-time or periodic copies add an uncontrolled multiplicity. | Source disjointness and the already-unfolded A_s volume/nonmain estimates include both signs and all copies; Cτ is horizon-dependent. |
| The sum of s^(-31) height bounds diverges and cannot pass weak limits. | The transfer uses the actual mass-integrable core/remainder envelope E(t), then derives the loose logarithmic height bound. |
| Bounds hold only a.e. in time, or retirement changes F. | The source convergence is every-time, the transfer is at each t, retirement changes colors only, and the source strong representative is retained. |
| A sphere tangent to the axis has an uncontrolled logarithm. | A single uniform sphere coordinate gives probability ≤ε; layer cake is uniform in the center and the hard-sphere rate handles small radius. |
| A hidden angular factor or gain change-of-variables assumption is used. | The two hemisphere sheets have Jacobian 4|u|, giving |g|/2 and total rate 2π|g|; nonnegative truncations justify unbounded tests. |
| Polynomial collision bounds are silently treated as log bounds. | Positive logs use ca² summability and the sphere estimate; negative loss uses R1,R3; only log M uses polynomial integrability afterward. |
| Vacuum or cancellation inside log B leaves negative gain uncontrolled. | Finite extended Φ first proves mismatch-nullity and vacuum vanishing; the exchanged positive-gain term controls cancellation of individual logs. |
| Moving tubes do not give uniform entropy integrability. | Their entire entropy costs are uniformly small; outside them a fixed velocity majorant supplies absolute continuity and tails. |
| The logarithmic chain rule presumes a global supremum or positivity. | Scalar absolutely continuous paths have bounded ranges separately; δ-regularization and the proved collision/log dominator handle vacuum. |
| Cutoffs or symmetrization lose an initial/flux defect or an endpoint. | All four terms have explicit dominators, no v-derivative of the cutoff occurs, symmetrization is absolute, and continuous entropy fixes every endpoint. |

The explanatory calculations in this review expand explicit equations, cited source formulas, and ordinary measure-theoretic steps already entailed by the submitted text. They are clarifications, not essential additions. In particular the Jacobian calculation was explicitly present in the source input and the proof already invoked the separate barrier for height; the same distinction applies to sphere truncations, the phase-vacuum inference by Tonelli, and equality of the continuous and absolutely continuous entropy representatives. I found no essential unfinished mathematical work in the frozen statement or submitted proof.

I checked compatible classical alternatives at their actual hypotheses, solely for correctness context. DL1991 Sections1–2 obtains the entropy inequality by truncation, weak compactness/identification of pair products, and convex lower semicontinuity. That operation alone does not give equality or convergence of dissipations. LM2010 Section4.1 explicitly retains conservation defects and does not assert entropy equality. Neither substitutes for the present logarithmic argument. The BGL H-theorem and AppendixA chain-rule proof use a lower positive global Maxwellian and an upper global Maxwellian to control log F. S238 does not possess or assume those pointwise bounds; it verifies the needed absolute integrability directly and then uses the same scalar chain-rule operation. Golse's Propositions3.1/3.3 show the classical collision symmetrization under continuous positive rapidly decaying density and polynomial log control; the present proof verifies absolute integrability instead of assuming those regularity hypotheses. GPV AppendixC's hard-sphere specialization uses a different angular normalization; the independent outgoing-sphere calculation here avoids importing its coefficient. None of these comparisons supplies an additional unverified hypothesis or a hidden replacement proof.

The result concerns precisely the unchanged October dormant/cap pair. Their common compact-initial-velocity datum, nonnegativity, source renormalized equations, strong traces, exact local conservation, polynomial collision bounds, source entropy admissibility, and positive-measure separation are all retained. The new conclusions are weighted entropy continuity for every real k≥0, absolute spacetime logarithmic gain/loss integrability with proved vacuum vanishing, continuous entropy density and flux, the exact local entropy equation with integrable frozen dissipation, and global equality at every pair of finite endpoints. No lower bound, persistent compact support, uniqueness, all-solutions statement, additional branch, parameter-uniform assertion, or convergence of approximate dissipations is used or established.

The exact admitted Lean endpoint and declaration were inspected. The nonuniqueness declaration ends in `sorry`, and its documented scope is the earlier interface with the stronger local-conservation refinement expressly outside it. It supplies no proved formal support for S238. The present recommendation is a mathematical correctness review relative to stipulated source truth, not a formal certification or a contribution assessment.
