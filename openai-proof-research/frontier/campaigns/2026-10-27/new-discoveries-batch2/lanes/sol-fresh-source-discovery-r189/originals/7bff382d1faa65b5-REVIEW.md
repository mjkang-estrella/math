# Independent full-scope contribution review — ROUND1

**Verdict: TECHNICAL, conditional on correctness of the entire unchanged frozen theorem.** This is solely the substantial-contribution assessment. It assigns no correctness verdict, acceptance, or count. It is not a replacement theorem or a request to repair the author proof. The bound statement and proof remain immutable.

The conclusion rests on a compatible derivation covering every frozen conclusion, given below. It does not rest on the failure of a familiar off-diagonal argument, on an abstract concentration-compactness slogan, or on the claim that a published theorem already states the frozen result. The actual primary proofs already contain the two-output-exponent remainder operation. Finite surface measure makes that operation directly available to the present rough Lp sequence. The remaining diagonal equality analysis is obtained by a weighted Hilbert square expansion and the elementary strict complex plus/minus inequality, together with injectivity and analyticity of a compactly supported Fourier transform. These operations compose without a new compatibility hypothesis.

Actual primary versions, proof labels, exact read extents, source operations, and history comparisons are in `private/COMPARISON.md` and the private reading records. The original mathematical derivation here is deliberately separated from the protected source bodies and their named metadata.

## 1. Paid interface and the precise scope to which it applies

Write μ for the induced area measure, m=μ(Σ), and

T f(x)=∫Σ exp(2πi x·ξ)f(ξ)dμ(ξ),    U_a f(ξ)=exp(−2πi a·ξ)f(ξ).

Thus T U_a f(x)=Tf(x−a). Compactness and nonemptiness of the smooth two-surface imply 0<m<∞. Every finite p>3 is considered separately. Constants can depend on that p and the entire fixed surface.

The stronger paid graph estimate is L3→Lq for **each** q>3, before the surface proof's final finite-measure embedding. Its applicability does not require smooth input. On a measurable chart piece ξ=v+L(ζ,φ(ζ)) with induced density J, let g(ζ)=f(ξ(ζ))J(ζ) on the piece and zero elsewhere. Then

‖g‖3³ ≤ (sup J)²∫piece |f|³dμ,

T(f 1piece)(x)=exp(2πi x·v) Eφg(Lᵀx),

‖Eφg(Lᵀ·)‖q=|det L|^(−1/q)‖Eφg‖q.

The paid window partition and phase continuation allow these measurable zero extensions. The finitely many chart terms therefore give

(1)  ‖Tf‖q ≤ A_q‖f‖3,    every q>3.

This includes boundary charts, and a finite atlas covers disconnected chart descriptions as well. No boundary trace of f or ambient extension of f is required. No uniform curvature/derivative family bound is extracted. The source's stronger packet, weighted, capacity, and propagation operations are all paid; the deduction uses their integrated consequence (1), without re-auditing their truth.

Finite measure now gives ‖f‖3≤m^(1/3−1/p)‖f‖p. Consequently 0≤C≤A_p m^(1/3−1/p)<∞. Since T1(0)=m and T1 is continuous, its Lp norm is positive; (1) makes that norm finite. Hence C>0. These are the frozen sharp norm's finiteness and positivity with the specified induced measure and complex normalization.

## 2. A compatible classical profile construction

The Hilbert extremizer theorem alone cannot be applied: the given extremality is in Lp, not L2. Instead Hilbert space is used only to extract profiles; sharp normalization is recovered later in Lp.

Fix q0=(p+3)/2, so 3<q0<p. Interpolating the same integral operator between L1→L∞ and (1) at q0 gives

(2)  T:L2(μ)→Ls(R³),    s=4q0/3,

because the interpolation weight on L3 is 3/4. Also T:L2→L∞ with norm at most √m. Choose a finite q1>max(p,s); interpolation gives T:L2→Lq1. These choices work on both sides of p=6 and for p arbitrarily close to 3. No Stein–Tomas output exponent or restriction on p to an even integer is needed.

For every h∈L1(μ), Th is uniformly continuous, since Σ is compact and

|Th(x+y)−Th(x)| ≤ 2π supΣ|ξ| ‖h‖1 |y|.

For bounded h, (1) puts Th in Lq0. Uniform continuity plus finite integrability implies Th(x)→0 at infinity: otherwise infinitely many disjoint fixed-radius balls have a fixed positive integral. Approximation by bounded functions in L1, using ‖T(h−hM)‖∞≤‖h−hM‖1, gives decay for all h∈L1. Thus U_an h⇀0 in any finite reflexive Lr when |a_n|→∞, by testing against its dual. Bounded parameter sequences have strongly convergent modulation subsequences, by dominated convergence. These are the precise dislocation hypotheses, including complex pairings.

Start with an arbitrary unit Lp sequence f_n. It is L2 bounded by m^(1/2−1/p). Select subsequences giving limits of its squared L2 norm and its output norms at q0,p,q1. Set r_n^0=f_n. Suppose finitely many profiles have been extracted, with residual r_n^J and old-frame weak L2 limits zero. The Hilbert energy identity bounds lim ‖r_n^J‖2 by the same initial bound, uniformly in J. If η_J=limsup ‖Tr_n^J‖q1 is positive, (2) gives

‖Tr_n^J‖q1^q1 ≤ ‖Tr_n^J‖∞^(q1−s) (K B)^s

on a tail with a common L2 bound B. Choose a_n so that |Tr_n^J(a_n)|≥c η_J^(q1/(q1−s)). Weak compactness in L2 supplies a limit φ of U_−a_n r_n^J. Pairing with 1 shows

(3)  ‖φ‖2≥c m^(−1/2)η_J^(q1/(q1−s))>0.

The complex values converge along this subsequence; positivity of the values is not assumed. If the new parameter differed boundedly from an old one, strong continuity of modulations and the old-frame zero weak limit would force φ=0. Hence parameters separate pairwise. Subtract U_a_n φ. The Hilbert squared norm decreases by ‖φ‖2²+o(1), and all old and new residual frames have weak limit zero.

This weak L2 profile belongs to Lp for a reason independent of residual Lp bounds in J: the **original** modulated sequence U_−a_n f_n has unit Lp norm and therefore a weak Lp subsequence. Its L2 weak limit is the same φ, because all previously subtracted profiles dislocate weakly. This induction proves φ_j∈Lp, ‖φ_j‖p≤1, and U_−a_n^j f_n⇀φ_j in Lp. For each fixed J, r_n^J has a finite Lp bound 1+∑j≤J‖φ_j‖p. It need not have a uniform bound in J.

Weak L2 convergence implies pointwise convergence of the extension, since its kernel at each fixed x lies in L2(μ). Apply the Brezis–Lieb identity at q0,p,q1 in each new translated output frame. Its hypotheses hold: pointwise convergence just proved and finite, fixed-J output bounds from (1). For each fixed J and each of these r,

(4)  lim ‖Tr_n^J‖r^r = lim ‖Tf_n‖r^r −∑j≤J ‖Tφ_j‖r^r.

For clarity, the identity uses no a.e. convergence of the INPUT. It follows from the scalar estimate

||a+b|^r−|a|^r|≤ε|a|^r+Kε|b|^r

and dominated convergence for the excess over ε|a|^r, followed by ε↓0. It is valid for complex numbers and every finite r>1.

The decrements ∑‖φ_j‖2² are summable. Inequality (3), with constants independent of J, forces η_J→0. A nested-subsequence diagonal selection preserving all finite-stage norm identities, pairwise parameter separations, and weak tests from countable dense subsets gives a single subsequence with (4) and

(5)  limJ limsup_n ‖Tr_n^J‖q1=0.

If extraction stops, the same statement means its last remainder. Choose the kth diagonal term far enough out for the first k identities and tests to have error ≤1/k and the first k separations to exceed k. The asymptotic norm bound for each fixed remainder is then preserved. Separability of the finite Lr spaces involved supplies the countable test sets.

At q0, (4) gives

(6)  supJ limsup_n ‖Tr_n^J‖q0 ≤ A_q0 m^(1/3−1/p).

Interpolation on OUTPUT, with 1/p=θ/q0+(1−θ)/q1, combines (5) and (6) to give

(7)  limJ limsup_n ‖Tr_n^J‖p=0.

This is the operative second-exponent argument already found in actual primary proofs. The original primary uses bounded truncations to enter Hilbert space. Here finite μ and p>3 supply L2 boundedness immediately, while (1) supplies the lower output exponent for the untruncated sequence. The primary's later amplitude-truncation removal and its use of q−max(p,p') are unnecessary. Consequently failure of that later argument at q=p is not an unpaid obstacle here.

## 3. Local square mass and diagonal equality

The scalar estimate ∑‖φ_j‖p^p≤1 alone would not force one profile at q=p. Its localized Hilbert predecessor supplies exactly the missing equality information by an elementary square expansion.

Pass to a subsequence such that |f_n|²⇀ρ in L^(p/2)(μ). Reflexivity applies since p/2>1; positivity and lower semicontinuity give ρ≥0 and ‖ρ‖p/2≤1. Fix a finite J and an arbitrary bounded measurable w≥0. Expand

0≤∫w |f_n−∑j≤J U_a_n^j φ_j|²dμ.

The original square tends to ∫wρ. The linear term for profile j tends to ∫w|φ_j|², since wφ_j∈L^{p'} on the finite measure space and U_−a_n^j f_n⇀φ_j in Lp. The off-diagonal profile products tend to zero: wφ_j overline{φ_k}∈L1, so the decay already proved applies at a_n^j−a_n^k. Therefore

∫w∑j≤J|φ_j|²dμ≤∫wρdμ.

Taking indicator weights and then the countable monotone limit yields

(8)  S=∑j|φ_j|²≤ρ a.e.,    ∫S^{p/2}dμ≤1.

This is localization of Hilbert Bessel's inequality by the bounded multiplier √w, which commutes with all modulations. The derivation establishes all its hypotheses on this same sequence. It neither asserts joint equidistribution of phases nor substitutes an L2 normalization for the Lp normalization. The nonlinear step is simply weak compactness of squared moduli in the reflexive space L^(p/2).

Now impose extremality of the original sequence. Equations (4) and (7) give

C^p=∑j‖Tφ_j‖p^p.

Since p/2>1, (8) gives the complete chain

C^p=∑j‖Tφ_j‖p^p ≤ C^p∑j‖φ_j‖p^p
 =C^p∫∑j|φ_j|^p ≤ C^p∫S^{p/2} ≤ C^p.

All deficits are nonnegative, so every inequality is an equality. Every nonzero profile is an exact extremizer after normalization. Strict superadditivity of t↦t^(p/2) on two positive arguments implies |φ_j||φ_k|=0 a.e. for j≠k. This last conclusion retains the equality information discarded by the primary scalar ℓp estimate. It costs no new decoupling theorem: it is the equality case of the explicitly localized square inequality.

## 4. Why two disjoint profiles are impossible

Compact frequency support implies that Th is entire for every h∈L1(μ): its exponential series converges absolutely and locally uniformly even at complex spatial arguments. If it vanishes on a real open set, its Taylor coefficients there vanish and it vanishes identically. If Th is identically zero, all moments of the finite complex measure hμ vanish. Polynomials restricted to the compact subset Σ separate points and contain constants, so Stone–Weierstrass and uniqueness of finite measures give hμ=0. Thus h=0 a.e. No connectedness of Σ, sign of h, or smoothness of h is needed.

For two nonzero profiles φ,ψ, their continuous analytic outputs u=Tφ,v=Tψ therefore have intersecting open nonzero sets. Indeed the nonzero set of u contains an open ball, on which v cannot vanish identically. After shrinking around a common nonzero point, both are nonzero on a ball.

If φ and ψ are disjointly supported exact extremizers, linearity and the operator norm bound give

(‖u+v‖p^p+‖u−v‖p^p)/2
 ≤ C^p(‖φ‖p^p+‖ψ‖p^p)=‖u‖p^p+‖v‖p^p.

For complex scalars u,v and p>2, parallelogram and convexity give

(|u+v|^p+|u−v|^p)/2 ≥ (|u|²+|v|²)^{p/2} ≥ |u|^p+|v|^p,

with the last inequality strict whenever both moduli are positive. The nonnegative integrable difference is strictly positive on the ball just obtained. Integration contradicts the preceding norm inequality. The actual primary proof of the complex plus/minus inequality supplies precisely this scalar operation; no quadratic-surface translation symmetry from that paper's larger theorem is used.

There is accordingly exactly one nonzero profile. It has Lp norm one and output norm C. This rules out splitting at the diagonal without q>p. The compatible operation is weighted Bessel equality plus strict complex convexity and analytic injectivity; a reference to general concentration compactness alone would not establish it.

## 5. Every sequence, attainment, and the whole extremizer set

For that single profile φ, U_−a_n f_n⇀φ in Lp, with ‖f_n‖p=‖φ‖p=1. Uniform convexity makes this convergence strong. Explicitly, Clarkson's inequality for complex Lp, p≥2, is

‖(h+k)/2‖p^p+‖(h−k)/2‖p^p ≤ (‖h‖p^p+‖k‖p^p)/2.

The midpoint norms tend to one by weak lower semicontinuity and the triangle inequality, so the difference tends to zero. This gives exactly the frozen **plus** sign: U_−a_n f_n=exp(2πi a_n·ξ)f_n. The diagonal indices can be chosen strictly increasing throughout. Nothing in the construction selected a special extremizing sequence; it began with an arbitrary one.

Choose an extremizing sequence from the definition of the finite positive supremum to obtain attainment. Let M be the entire normalized extremizer set. It is invariant under U_a because input moduli and translated output norms are unchanged. If the asserted stability failed for ε>0, choose unit f_n with ‖Tf_n‖p≥(1−1/n)C and dist(f_n,M)≥ε. The sequential conclusion gives U_−a_n f_n→φ∈M. But U_a_n φ∈M and

‖f_n−U_a_n φ‖p=‖U_−a_n f_n−φ‖p→0,

a contradiction. This yields the stated positive δ(Σ,p,ε) relative to **all** normalized extremizers, with no classification or rate.

## 6. Assessment at every frozen conclusion

| Frozen requirement | Integrated payment/derivation |
|---|---|
| Every compact embedded definite-curvature smooth surface, smooth boundary allowed | Paid full graph estimate and rough measurable chart/Jacobian transfer in §1; the subsequent proof uses only finite compactly supported μ and that estimate. |
| Every finite 3<p<∞ | q0 between 3 and p, s=4q0/3, finite q1>max(s,p); all convexity inequalities require only p>2. |
| Complex rough normalized inputs | Original unit Lp weak compactness, fixed-J output splitting, weighted L1 product decay, and complex scalar inequalities in §§2–4; no positive-data or smooth-data reduction. |
| Positive finite sharp constant | §1 with (1), finite-measure embedding, and T1(0)=m. |
| Every extremizing sequence and strong Lp subsequence modulo the specified modulations | §§2–5; sharp Lp normalization comes from (8) and equality, not Hilbert extremality. |
| Attainment | Definition of supremum followed by the sequential conclusion. |
| Qualitative stability relative to entire M | Modulation invariance and the contradiction in §5. |
| Fixed-surface constants only, no hidden scope replacement | Every constant in extraction and interpolation belongs to this one μ,p. No endpoint, family uniformity, quantitative rate, or local/global extremizer classification is used. |

The unpaid nonroutine remainder for this **contribution comparison**, after the displayed compatible classical composition, is empty. This does not certify the author's correctness gate: that remains separate and must be decided independently. No theorem from a restricted sphere or paraboloid setting was silently used as the whole-scope result. No worldwide novelty, exhaustive literature clearance, or impossibility assertion is made.

## 7. Reading limits and immutable inputs

All 29 canonical blobs were freshly acquired at the prescribed pin and authenticated against the complete nontruncated 13,223-entry tree. Both actual wrappers, both READMEs, all operative section bodies, the included figure sources, and the bibliography metadata were read. The two compiled PDFs were authenticated as binaries, not rendered or counted as additional proof reading. Actual primary proofs were read at the extents recorded privately, including full FVV and Buschenhenke text, the full scale-one profile section and off-scaling argument in Flock–Stovall, Stovall's full space-time/main-proof sections, and the local-extremizer argument in Ciccone–Sousa. Abstract-profile material was inspected with its actual weak/Delta and Opial hypotheses; unneeded transitive parts were not counted as read or used as black boxes. The five specifically authorized original-history spans were independently read through their stated endings. There was no broad history rerun and no peer gate inspection.

The exact essential comparison is closed by §§1–5; the private record explicitly distinguishes the uninvoked transitive reading limits from essential hypotheses. No author's reading ledger is substituted for these reads. Initial clipped outputs were recovered as specified privately before this final assessment.

Pre/post checks cover all 21 authorized author inputs. In particular the 1,645-byte frozen statement and 17,147-byte proof retain their bound SHA256 values and 0644 modes. Artifact verification authenticates bytes only and does not assign a mathematical gate.
