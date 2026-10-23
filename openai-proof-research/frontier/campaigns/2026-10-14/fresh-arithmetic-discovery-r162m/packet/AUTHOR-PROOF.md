# Author proof for the frozen r162m theorem

This is a discovery author-proof nominee, not a correctness or contribution review. The exact immutable statement is FROZEN-THEOREM.md. All norms on Σ use induced area measure μ=σ, and all output norms use Lebesgue measure on R³. Functions are complex valued. Write m=μ(Σ)>0 and

T f(x)=∫Σ e^{2πi x·ξ} f(ξ)dμ(ξ),   U_a f(ξ)=e^{-2πi a·ξ}f(ξ).

Thus T(U_a f)(x)=Tf(x−a). The sign in the frozen conclusion corresponds to U_{−a}.

## 1. The paid estimate and its exact use

The fully read integrated Source077 graph theorem supplies L³ input and L^q output for every q>3. Its surface transfer retains this estimate before the final finite-measure embedding. More explicitly, on each of finitely many measurable chart pieces, write ξ=v+L(ζ,φ(ζ)) with L invertible and dμ=J(ζ)dζ. Extend g(ζ)=f(ξ(ζ))J(ζ) by zero off the piece. Then

‖g‖₃³ ≤ (sup J)² ∫piece |f|³dμ,
T f(x)=e^{2πi x·v} Eφ g(Lᵀx),
‖Eφ g(Lᵀ·)‖q=|det L|^(−1/q)‖Eφ g‖q.

The actual window partition and graph continuations in that source apply to these rough zero-extended functions. Summing the finite chart estimates gives

(A)  ‖Tf‖q ≤ A_q ‖f‖₃,  every q>3.

Each A_q is finite for this fixed surface. No uniform family dependence is asserted. Smooth boundary does not impose a trace condition on f. The two source manuscripts' capacity, weighted maximal, sparse-ball and propagation operations are all paid input; none is claimed as a new deduction here. Exact source labels and private reading limits are in private/SOURCE-INTERFACE.md and the reading records.

Fix p∈(3,∞). Since ‖f‖₃≤m^(1/3−1/p)‖f‖p, (A) with q=p gives C=‖T‖p→p<∞. Moreover T1(0)=m, T1 is continuous, and T1∈Lp, so C>0.

Choose once and for all q₀=(3+p)/2, so 3<q₀<p. Interpolation of (A) at q₀ with ‖Tf‖∞≤‖f‖₁ gives

(B)  T:L²(μ)→L^s(R³),   s=4q₀/3,

because 1/2=(1−3/4)/1+(3/4)/3 and 1/s=(3/4)/q₀. This is ordinary linear complex interpolation of the same integral operator; on the finite measure space all these definitions agree. Also T:L²→L∞ with norm at most √m. Choose q₁>max(p,s), for example q₁=p+s+1. Interpolating the two L² estimates gives T:L²→L^q₁.

The new work will use (A) below p and (B) above p simultaneously. It will not assume that remainders have Lp norms uniformly bounded in the number of profiles.

## 2. Elementary facts used in the proof

### 2.1 Decay and dislocation

For any h∈L¹(μ), Th is uniformly continuous: compactness of Σ and dominated convergence give this directly, or one can use

|Th(x+y)−Th(x)|≤2π supΣ|ξ| ‖h‖₁ |y|.

If h is bounded, h∈L³ and (A) implies Th∈L^{q₀}. A uniformly continuous function in a finite L^r(R³), r<∞, tends to zero as |x|→∞. Indeed, otherwise uniform continuity produces balls of a single positive radius on which its modulus is bounded below, with infinitely many disjoint balls, contradicting integrability. For arbitrary h∈L¹ approximate h in L¹ by bounded functions; ‖T(h−h_M)‖∞≤‖h−h_M‖₁ proves

(C)  Th(x)→0 as |x|→∞, for every h∈L¹(μ).

Consequently if |a_n|→∞, U_{a_n}h converges weakly to zero in L^r(μ) for every 1<r<∞ and h∈L^r: every dual pairing is the Fourier transform of the L¹ density h times its dual test. Similarly, U_b depends strongly continuously on b in any finite L^r. These assertions use the fixed surface only. No multiple-phase independence or equidistribution is needed.

Weak L² convergence h_n⇀h implies Th_n(x)→Th(x) at every x, since the exponential kernel belongs to L²(μ). The same is true for weak Lp convergence.

### 2.2 Output norm splitting

We use the following elementary Brezis–Lieb identity. If v_n→v pointwise almost everywhere and sup_n‖v_n‖r<∞, 1<r<∞, then

(D)  ‖v_n‖r^r−‖v_n−v‖r^r→‖v‖r^r.

For completeness, Fatou gives v∈Lr. For each ε>0, the scalar mean-value inequality and Young's inequality give

||a+b|^r−|a|^r|≤ε|a|^r+K_{r,ε}|b|^r.

Set a=v_n−v and b=v. The positive part of

||v_n|^r−|v_n−v|^r−|v|^r|−ε|v_n−v|^r

is bounded by (K_{r,ε}+1)|v|^r and tends to zero pointwise. Dominated convergence, then ε→0, proves (D). We will apply it only at the finite exponents q₀,p,q₁.

### 2.3 Nonzero analytic outputs overlap

For h∈L¹(μ), compact support of the measure hμ makes Th real analytic on all of R³: its exponential power series converges absolutely and uniformly on compact subsets even for complex spatial arguments. If Th vanishes on a nonempty real open set, its Taylor coefficients at a point of that set vanish, and the entire power series implies Th vanishes everywhere. If Th is identically zero, differentiating at zero shows ∫ξ^α h(ξ)dμ=0 for every multi-index α. Polynomials are uniformly dense in continuous functions on the compact set Σ by Stone–Weierstrass; hence the finite complex measure hμ is zero. Therefore h=0 μ-almost everywhere.

Thus a nonzero h has a continuous nonzero output whose zero set has empty interior. If h and k are both nonzero, the open nonzero set of Th contains a point at which Tk is nonzero. Their nonzero sets consequently overlap on an open ball. This conclusion needs no sign or regularity of h,k.

## 3. Profiles with a small output remainder

Let (f_n) be any sequence with ‖f_n‖p=1. We first construct a profile description, with no extremality assumption. It is bounded in L² and L³. Pass to a subsequence on which ‖f_n‖₂² tends to A²≤m^(1−2/p), and on which each of ‖Tf_n‖r^r, r∈{q₀,p,q₁}, has a limit. Such subsequences exist because (A) and finite measure bound these quantities.

We claim there are either finitely many or countably many nonzero φ_j∈Lp and sequences a_n^j∈R³ such that, putting

r_n^J=f_n−Σ_{j=1}^J U_{a_n^j}φ_j,

the following hold for every fixed finite J on a single final subsequence:

(E1) |a_n^j−a_n^k|→∞ for j≠k;
(E2) U_{−a_n^j}f_n⇀φ_j in Lp;
(E3) ‖r_n^J‖₂²→A²−Σ_{j≤J}‖φ_j‖₂²≥0;
(E4) for each r∈{q₀,p,q₁},
     lim_n‖Tr_n^J‖r^r=lim_n‖Tf_n‖r^r−Σ_{j≤J}‖Tφ_j‖r^r;
(E5) lim_{J→∞} limsup_n‖Tr_n^J‖q₁=0.

For a finite list, J→∞ in (E5) means use its final remainder. An empty list is allowed at this stage.

Here is the complete extraction argument. Start with r_n^0=f_n. At stage J assume the already extracted residual satisfies U_{−a_n^j}r_n^J⇀0 in L² for all j≤J, and that its L² norm has the limit in (E3). This property is vacuous at J=0. Let η_J=limsup_n‖Tr_n^J‖q₁ on the current subsequence. If η_J=0 stop. Otherwise pass to a subsequence attaining this limsup, and eventually satisfying ‖Tr_n^J‖q₁≥η_J/2 and ‖r_n^J‖₂≤B, where B=2m^(1/2−1/p)+1 can be fixed for all stages by (E3).

By (B),

‖Tr_n^J‖q₁^{q₁}≤‖Tr_n^J‖∞^{q₁−s}(A_s^{(2)}B)^s,

where A_s^{(2)} is the finite L²→L^s norm from (B). There is therefore a point a_n^{J+1} with

|Tr_n^J(a_n^{J+1})| ≥ c η_J^{q₁/(q₁−s)},

with c>0 depending on the fixed exponents, m and A_s^{(2)}, and not on J. The factor c includes a factor 1/2 for choosing an approximate supremum. The sequence U_{−a_n^{J+1}}r_n^J is L² bounded. Extract its weak limit φ_{J+1}; evaluation at zero is an L² dual pairing, so

(F) ‖φ_{J+1}‖₂≥c m^(−1/2) η_J^{q₁/(q₁−s)}>0.

The complex values at zero converge along this weak subsequence; the lower bound survives. No positivity of them was required.

For each old j, after a further subsequence the new parameter either diverges from a_n^j or has a bounded difference converging to a vector. The latter alternative is impossible: strong continuity of fixed modulations and U_{−a_n^j}r_n^J⇀0 would force the new weak limit to be zero. Hence (E1) holds. Subtract the profile to define r_n^{J+1}. Weak convergence gives the exact Hilbert energy decrement

‖r_n^{J+1}‖₂²=‖r_n^J‖₂²−‖φ_{J+1}‖₂²+o(1).

At the new parameter the new residual has weak limit zero. At every old parameter this follows from the previous zero limit and (C) applied to the newly subtracted profile. This proves the induction invariant and (E3).

It remains important to justify Lp membership without a uniform Lp residual estimate. The original sequence U_{−a_n^{J+1}}f_n is bounded in Lp, hence has a weak Lp subsequence by reflexivity. Since Lp embeds continuously into L², this is also weak L² convergence. All previously subtracted modulated profiles tend weakly to zero in L² by (C) and (E1). Thus the weak Lp limit of the original sequence is precisely φ_{J+1}. In particular φ_{J+1}∈Lp with ‖φ_{J+1}‖p≤1, proving (E2). This inductive step uses only already established Lp membership of earlier profiles.

For each fixed J, r_n^J is bounded in Lp by 1+Σ_{j≤J}‖φ_j‖p, which is finite, even though it may grow with J. It follows from (A) that Tr_n^J is bounded in each of L^{q₀}, Lp and L^{q₁}. In the new frame its output converges pointwise to Tφ_{J+1}, by weak L² convergence and the kernel test. Apply (D) in that frame and use translation invariance of output norms to obtain

‖Tr_n^J‖r^r=‖Tφ_{J+1}‖r^r+‖Tr_n^{J+1}‖r^r+o(1)

for r=q₀,p,q₁. Induction proves (E4) and the existence of the residual output norm limits.

For infinitely many profiles, (E3) yields Σ_j‖φ_j‖₂²≤A². The uniform bound (F) forces the successive η_J to tend to zero: their positive power 2q₁/(q₁−s) has a summable bound. Each extraction was made on nested subsequences. Choose a final diagonal subsequence so that the first k norm identities and the first k tests from fixed countable dense subsets of L² and L^{p'} hold to accuracy 1/k, and the first k parameter separations exceed k, at its kth term. The relevant norm limits already exist on each retained subsequence. This standard diagonal choice preserves every fixed finite-stage identity, weak limit and separation. The final limsup of each residual q₁ norm is no larger than its value on the corresponding stage subsequence. Therefore η_J→0 gives (E5). If the procedure stops, the same assertions hold with its last residual. This establishes the claim on one sequence of indices, not distinct incompatible subsequences for different identities.

Crucially, (E4) at q₀ gives the uniform bound

(G) limsup_n‖Tr_n^J‖q₀ ≤ lim_n‖Tf_n‖q₀ ≤ A_{q₀}m^(1/3−1/p), for every J.

Let θ∈(0,1) satisfy 1/p=θ/q₀+(1−θ)/q₁. Output interpolation and (E5),(G) show

(H) lim_{J→∞} limsup_n‖Tr_n^J‖p=0.

This is the replacement for the unavailable positive exponent q−p in diagonal truncation arguments. There has been no assumption of pointwise input convergence, bounded input amplitude, uniform Lp residual control, or independence of phase labels.

## 4. Local square mass of all the profiles

Pass to a further subsequence on which |f_n|²⇀ρ in L^{p/2}(μ). This is possible since p/2>1 and

‖|f_n|²‖_{p/2}=‖f_n‖p²=1.

The weak limit ρ is nonnegative and ‖ρ‖_{p/2}≤1. All earlier assertions persist under this subsequence.

Fix a bounded nonnegative measurable w on Σ and a finite J. Expanding a weighted square gives

0≤∫w|f_n−Σ_{j≤J}U_{a_n^j}φ_j|²dμ.

The first term tends to ∫wρdμ, since w∈L^{p/(p−2)} on this finite measure space. For a diagonal cross term, (E2) gives

∫w f_n overline{U_{a_n^j}φ_j}dμ
 =∫(U_{−a_n^j}f_n) w overline{φ_j}dμ
 →∫w|φ_j|²dμ.

The dual test wφ_j belongs to L^{p'} because p>2, φ_j∈Lp, w is bounded and μ is finite. For j≠k, wφ_j overline{φ_k}∈L¹ and (C),(E1) give

∫w U_{a_n^j}φ_j overline{U_{a_n^k}φ_k}dμ→0.

Taking the limit in the expansion yields

∫w Σ_{j≤J}|φ_j|²dμ≤∫wρdμ.

Taking w to be indicators proves Σ_{j≤J}|φ_j|²≤ρ almost everywhere. There are only countably many J, so these inequalities hold off a single null set. Monotone convergence then gives

(I) S:=Σ_j|φ_j|²≤ρ almost everywhere,
    ∫ S^{p/2}dμ≤∫ρ^{p/2}dμ≤1.

This local estimate is stronger than retaining only Σ_j‖φ_j‖p^p≤1. In particular it records overlap of input supports. It does not prescribe a joint distribution for three or more modulation phases. Every oscillatory term used in its proof is a pairwise Fourier transform of one fixed L¹ density.

## 5. Extremality at the diagonal

Now assume the original sequence is extremizing: ‖Tf_n‖p→C. By (E4) at p and (H),

(J) C^p=Σ_j‖Tφ_j‖p^p.

At least one profile is nonzero, since C>0. Since p/2>1, pointwise superadditivity and (I) imply

C^p=Σ_j‖Tφ_j‖p^p
   ≤C^p Σ_j‖φ_j‖p^p
   =C^p∫Σ_j|φ_j|^p dμ
   ≤C^p∫(Σ_j|φ_j|²)^{p/2}dμ
   ≤C^p.

Every inequality is an equality. Each individual nonnegative deficit C^p‖φ_j‖p^p−‖Tφ_j‖p^p is zero, so each nonzero φ_j is an extremizer after normalization. Also

Σ_j|φ_j|^p=(Σ_j|φ_j|²)^{p/2} almost everywhere.

For any two positive numbers a,b and t>1, (a+b)^t>a^t+b^t. Applied to any two squared moduli in this countable sum, equality implies

(K) |φ_j||φ_k|=0 almost everywhere whenever j≠k.

Thus any distinct nonzero profiles are exact extremizers with disjoint input supports. The scalar diagonal mass estimate by itself would allow this alternative; (I) identifies it exactly.

We next exclude it. Suppose φ and ψ are two such nonzero profiles. Disjoint supports give, for both signs,

‖φ±ψ‖p^p=‖φ‖p^p+‖ψ‖p^p.

The two operator norm inequalities and extremality imply

(L) 1/2(‖Tφ+Tψ‖p^p+‖Tφ−Tψ‖p^p)
    ≤C^p(‖φ‖p^p+‖ψ‖p^p)
    =‖Tφ‖p^p+‖Tψ‖p^p.

For any complex numbers u,v, the parallelogram identity and convexity of t↦t^{p/2} give

(|u+v|^p+|u−v|^p)/2
 ≥ ((|u+v|²+|u−v|²)/2)^{p/2}
 = (|u|²+|v|²)^{p/2}
 ≥ |u|^p+|v|^p.

The final inequality is strict whenever u and v are both nonzero. By §2.3, Tφ and Tψ are simultaneously nonzero on an open ball. The integrable nonnegative difference in the last display is strictly positive there. Its integral is therefore strictly positive, contradicting (L). This rules out two nonzero profiles.

There is exactly one profile, say φ_1. From (J) and the equality chain, ‖φ_1‖p=1 and ‖Tφ_1‖p=C. Assertion (E2) gives U_{−a_n^1}f_n⇀φ_1 in Lp. The norms of both sides equal one. Uniform convexity now yields strong convergence. One can see this directly from Clarkson's inequality, valid for complex Lp when p≥2:

‖(h+k)/2‖p^p+‖(h−k)/2‖p^p≤(‖h‖p^p+‖k‖p^p)/2.

Its scalar form follows from the parallelogram identity, a^{p/2}+b^{p/2}≤(a+b)^{p/2}, and convexity applied to |h|²+|k|². The midpoint of U_{−a_n^1}f_n and φ_1 has weak limit φ_1, so its norm has liminf at least one and is at most one. Clarkson consequently forces the difference norm to zero. Recalling the definition of U, this is precisely

‖e^{2πi a_n^1·ξ} f_n−φ_1‖p→0

on the extracted subsequence. This proves the full sequential assertion in the frozen theorem, with no restriction on the initial normalized extremizing sequence.

## 6. Attainment and qualitative stability

By the definition of C there exists a sequence with unit input norm and output norms tending to C. The proved sequential statement gives a normalized extremizer, so M_{Σ,p} is nonempty.

Modulation preserves both norms. Therefore U_a M_{Σ,p}=M_{Σ,p}, and distance to this set is modulation invariant. If the frozen qualitative stability assertion failed for some ε>0, there would be unit-norm f_n with ‖Tf_n‖p≥(1−1/n)C but distance at least ε from M_{Σ,p}. The sequential statement provides a subsequence and modulations converging strongly to a normalized extremizer φ. Then g_n=U_{a_n}φ belongs to M_{Σ,p} and ‖f_n−g_n‖p→0, a contradiction. Thus a positive δ(Σ,p,ε) exists. No rate or effective value has been claimed.

## 7. Scope and remaining review

Every surface and every strict exponent in the frozen statement is treated. Boundary affects only the already-paid rough chart transfer. The profiles retain the same original surface and the same p-norm normalization. No spatial truncation replaces the global norm. No amplitude cutoff or smooth approximation of an extremizing sequence is assumed. Neither curvature degeneration nor p=3 is treated. All uses of interpolation and finite chart changes are paid classical steps, not separately proposed findings.

The proposed additional operation is the compatible output remainder argument plus local square-mass equality and analytic exclusion of disjoint extremizers, closing the diagonal where the strictly off-diagonal scalar mass proof does not apply. Primary comparison and transitive reading limitations are explicit in private/PRIMARY-UNDERSTANDING.md. This author proof assigns no independent correctness gate, no substantial-contribution gate, no acceptance, no priority, and no count. The parent alone may request the two separate reviews.
