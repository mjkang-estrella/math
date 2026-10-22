# Arithmetic r154: concrete continuation reduction

Research notes, not a frozen theorem or an author-proof nominee. All operations in the two SOURCE055 manuscripts at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true. The calculations below investigate an additional operation: for every smooth complex quintic X, join the actual source Gepner stability condition to the ordinary large-volume component by a path of numerical stability conditions on the full numerical group. This is not connectedness of the entire stability manifold, a mirror-period assertion, or an extension to other hypersurfaces. No theorem was frozen. Original deductions are separated from paid operations below.

## 1. What the two source constructions actually supply

Write G for the authenticated quintic manuscript, and L for the authenticated prescribed-large-volume manuscript; exact paths, hashes and complete reading extents are in private/READING.md and private/source-bindings.json.

G uses coordinates (r,c,d,e)=(rk,H²ch1/5,Hch2/5,ch3/5), with H³=5. Its full numerical real space is four-dimensional, and its numerical lattice is discrete. Put λ=exp(2πi/5), t0=(1/2)cot(π/5), u=(5−√5)/10. Its point-normalized charge is

 ZG/5 = (λ−1)r/5 + (t0²−5/6+i t0/2)c + (−1/2+i t0)d − e.

Its functor is Φ=T_O ∘ (−⊗O(1)), in that order. G's numerical section calculates the integral-lattice action, whose real matrix is

 M = ((−4,−20/3,−5,−5),(1,1,0,0),(1/2,1,1,0),(1/6,1/2,1,1)).

The characteristic polynomial is the fifth cyclotomic polynomial. The separate periodicity input proves Φ⁵≅[2] at the functor/kernel level, not merely on numerical classes. The charge is an eigenform and the final slicing obeys ΦP(φ)=P(φ+2/5).

The construction begins with rational first tilts B_± at slopes ±1/2 and second cuts N_b^η=d−bc+ur+η1c+η0r. A discrete nonnegative p_b=c−br and noetherianity construct the second torsion pairs directly. Independent-parameter slope comparison, Serre duality and the twist triangle prove ΦU_η⊂U_θ throughout a fixed two-dimensional square. The tensor step uses the shear α1=η1, α0=η0−η1 once; iterations do not repeatedly shear the allowed square. The coarse fifth-periodic grid is refined to V_{k+1}⊂V_k, with V_{k+5}=V_k[1] and V_{k+2}=ΦV_k. Blocks S_k=V_k∩V_{k+1}^⊥ lie in sectors [k/5,(k+1)/5]. Independent variations in r and c, together with the other two charge coordinates, give full numerical support. Finite lattice counts in sectors give block HN filtrations; common boundary phases are merged to form the actual slicing. G does not license replacing that final slicing without examining its boundary conventions.

L proves exact ordinary and square-root-Todd charges for K_X trivial at every sufficiently large volume, with a common threshold on an open set of real twists and ample directions. It embeds in products of projective spaces, uses scaled full numerical norms, and perturbs ambient charges by a bound C1η+C2/t in the scaled operator norm. The fixed support quadratic form remains negative on all kernels in this small deformation. A finite negative-line resolution and line-tensor phase bounds supply restriction. GRR with the specified Todd corrections gives the exact desired charge, and injectivity of numerical pushforward supplies full support. The ordinary charge is identified with its double-tilt heart by the surface section argument; the Todd construction must not simply be assigned that same heart. Stable points are proved in L.

Separately, L's fixed-apex estimate, restriction/cohomology argument and wall integration give the strong tilt inequality above a threshold for every smooth projective complex threefold along the stipulated fixed polarization/twist setup. The wall argument uses a decreasing discriminant and integrates D' = −aS/3, with S=Δ/d. These are paid proofs, not conjectural inputs. They do not assert an effective general numerical threshold, or control the negative parameter reached below. The small-volume counterexamples in L concern specific other threefolds and do not refute this quintic continuation.

## 2. Strongest operative primary comparisons

Toda 1305.0345v3 §§3.1–3.6 supplies the proposed Gepner charge/heart and explains the original irrational-slope HN issue. G supplies its actual new existence proof; the older conjectural status is not an objection to G.

Li 1810.03434v2 Theorem 1.3 and the full §3 proof give the standard quintic region α>0 and α²+(β−floor β−1/2)²>1/4, with the appropriate real-charge coefficient bound. At β=−1/2 this is α²>1/4. The proof uses Brill–Noether stability, evaluation cones, a minimal-discriminant reduction and integer-β wall endpoints. Its domain restriction cannot be erased when α² becomes nonpositive.

Xu 2511.21288v2 supplies the stronger slope-sheaf envelope. The actual Clifford and restriction proofs in §§3–4 were read. In particular, on [6/13,1/2] the envelope is g(x)=x/2−3/10; reflection extends this same affine expression to [1/2,7/13]. These exact pieces, stronger than G's intentionally coarser envelope, are used below. They bound slope-semistable sheaves, not arbitrary two-term complexes.

Bayer 1606.02169v3 was read completely. Its support-form deformation theorem is a covering statement over a connected domain on which a fixed support quadratic form is negative definite on every kernel. A path in the vector space of charges alone does not meet its hypotheses. Repeated local charts with possibly collapsing radii do not prove that a finite path has a lift to its endpoint.

Bayer–Macrì–Stellari 1410.1585v2 §8 was read through its proofs. The standard twisted-cubic region and its quadratic forms are conditional on the applicable tilt inequality. Its common-first-tilt uniqueness lemma requires both hearts to be tilts of the same first heart; equality of charges alone is insufficient. Li verifies the requisite region on the quintic, not the negative-α² corridor.

The actual restriction and uniqueness proofs were also read in Cheng–Feyzbakhsh 2607.04788v1 §3, Li et al. 2607.28411v1 §§3.24–3.28 and 6.2, and Giovenzana–Robotis–Rota–Zuliani 2608.16013v1 §§3–4. These give strong ambient, large-volume and full-support operations. Li et al.'s distinguished-component comparison already handles changes of embedding and Todd-type corrections at large volume using scaled O(a^−2) perturbations and a strict Bayer-property uniqueness argument. It is paid, not a new nominee here. The required strict Bayer property has not been established for an arbitrary interpolation to the Gepner slicing.

Late, before these notes were drafted, Li 2601.22994v1 was read in full, including the actual double-Schubert/Soergel filtration, finite descent, isogeny scaling, and restriction-resolution proof. Thus the ambient construction is not being reduced to a title or abstract. Its local deformation plus large isogeny operation is effective as an existence construction at large volume; it does not transport a quintic Gepner slicing backwards along a finite-volume corridor. Earlier foundational papers cited inside these primaries were not all recursively read; the proof interfaces actually used and this limit are recorded privately.

## 3. Exact common charge coordinates

Fix B=−H/2. In twisted coordinates write

 y=c+r/2,  z=d+c/2+r/8,  w=e+d/2+c/8+r/48.

Their inverse is c=y−r/2, d=z−y/2+r/8, e=w−z/2+y/8−r/48. Set

 sG=1/4−2u=−3/4+√5/5,       AG=t0²−17/24=−11/24+√5/10.

Direct substitution gives

 ZG/5 = −w+AG y + i t0(z−sG r/2).                         (1)

The real rank term cancels because u+t0²=3/4. In particular

 sG≈−0.3027864045, AG≈−0.2347265356, AG−sG/2=−1/12.       (2)

For comparison use Z_{s,A}=−w+Ay+i(z−sr/2). Passing from (1) to this charge is the orientation-preserving linear change that divides the imaginary coordinate by t0. It transports the slicing by the standard lifted GL⁺(2,R) action; it is not an assertion that the phase 2/5 covariance is unchanged under a nonconformal linear change. The original source condition and the transported one lie in the same component.

The ordinary physical-volume charge, divided by 5 and with imaginary coordinate divided by t>0, is Z_{s,A} with

 s=t²/3, A=t²/2=3s/2.                                    (3)

For a quintic c2(X)=10H², so √td(X)=1+5H²/12. The Todd charge has

 s=t²/3−5/6, A=t²/2−5/12.                               (4)

More generally multiplying ch by 1+κH² gives s=t²/3−2κ and A=t²/2−κ; hence A−s/2=t²/3>0. Equation (2) rules out representing this normalized Gepner charge by a positive-volume charge in this particular one-parameter degree-four correction family. This is a precise obstruction to a routine ordinary/Todd substitution in the fixed B and normalization. It is not an obstruction to a path of stability conditions or to a more general charge normalization.

Take the explicit straight segment

 A(s)=AG+(3/2−AG)(s−sG)/(1−sG),       sG≤s≤1.             (5)

All these charges are surjective real maps: y and w supply the real direction, and z supplies the imaginary direction. At s=1 it meets the ordinary ray. For s>1/4 its real coefficient obeys A(s)>s/6: the difference is affine with positive slope and its value at 1/4 is 403/687−13√5/229>0. Thus the part s>1/4 belongs to Li's region, and the ordinary ray from s=1 to arbitrarily large volume lies in the same known standard family. This pays the entire positive end, including connection to L's ordinary large-volume stability conditions by the common-heart identification. This first comparison alone leaves sG≤s≤1/4. The stronger fixed-form reduction in §6 below pays every remaining positive s without assuming its heart is A_s; the genuine unresolved crossing is at s=0 and on the negative side. Equation (5) alone is still not a construction of a slicing.

## 4. Bounded hearts throughout and beyond the missing interval

Let B0=⟨C_{≤−1/2}[1],C_{>−1/2}⟩ be the rational first-tilt heart. It is noetherian by G, Lemma first-tilt-noetherian. Its function y=c+r/2 takes values in (1/2)Z_{≥0}. For real s put N_s=z−sr/2 and define a nonzero object of B0 to be high if y=0 or N_s>0, low if y>0 and N_s≤0. Let T_s consist of objects all of whose nonzero quotients are high, and F_s of those all of whose nonzero subobjects are low.

For every s>−7/20 these are a torsion pair. Here is the full applicability check, rather than an invocation of HN at an irrational parameter. If y(E)=0 in B0, its degree-minus-one sheaf is slope-semistable of slope −1/2 and its degree-zero sheaf has dimension at most one. Xu gives d/r≤−1/20 at slope −1/2. Consequently

 N_s(F)/r ≤ −1/20−1/4+1/8−s/2
           = −7/40−s/2 <0                              (6)

for a positive-rank boundary sheaf F. After shifting this is positive. The dimension-at-most-one sheaf contributes N_s=d≥0, and equality is possible only in dimension zero. Thus N_s≥0 on y=0, with equality precisely for zero-dimensional sheaves.

High objects are extension-closed. In an object having a high subobject choose one with smallest y. If y=0, all its quotients have y=0. Otherwise a low quotient would leave a high kernel with strictly smaller y, a contradiction. Hence the selected subobject belongs to T_s. Quotient and extension closure of T_s, and noetherianity of B0, give a maximal T_s subobject. Its quotient has no high subobject by the same minimal-y argument and belongs to F_s. A nonzero image of a map from T_s to F_s would be both high and low. This proves the torsion pair.

It follows that A_s=⟨F_s[1],T_s⟩ is a bounded heart, and N_s≥0 on it. If N_s(E)=0, its T_s part is zero-dimensional and its shifted F_s part, if nonzero, has negative y. Therefore a nonzero E in A_s cannot have zero numerical class: y forces the F_s part to vanish and e then forces the zero-dimensional part to vanish. This argument applies to every real s>−7/20, including s=0 and sG, without assuming a Bridgeland condition or full tilt-slope HN. It is a direct extension of G's paid torsion-pair mechanism using Xu's stronger endpoint bound; it is not proposed as the substantial result.

At s=sG this is G's unperturbed double-tilt heart. Existence of A_s alone does not give a stability condition: a charge with nonnegative imaginary part can still take a nonzero object to the positive real axis or zero, and HN and support remain separate obligations.

## 5. A uniform near-zero rank bound, with the sheaf-to-complex interface closed

For finite tilt slope use ν_s(E)=N_s(E)/y(E), with the convention +∞ for y=0. The following argument applies to an object known to be ν_s-semistable in B0 with finite slope; it does not assume the existence of HN filtrations for all objects.

On the whole strip μ∈[−7/13,−6/13], Xu's bound, including its reflected piece, gives

 d/r ≤ −μ/2−3/10,
 N_s/r ≤ −7/40−s/2 =: −m(s).                            (7)

For s≥sG, m(s)≥mG=(√5−2)/10>0. Fix

 δ=13(√5−2)/10 = 13mG.

Suppose |ν_s(E)|<δ. Put F=H^−1(E), T=H^0(E).

If the top slope factor F1 of F had slope in [−7/13,−1/2], its saturation gives an actual monomorphism F1[1]→F[1]→E in B0. When μ=−1/2 its y is zero and it destabilizes by the +∞ convention. Otherwise

 0<y(F1[1])/r(F1)=−μ(F1)−1/2≤1/26,
 ν_s(F1[1])≥26m(s)≥26mG>δ.

This contradicts semistability. Therefore all slopes of F are strictly less than −7/13, and y(F[1])>r(F)/26 if F≠0.

If T has positive rank, remove its ordinary torsion and take its bottom slope quotient T1. Because all the intervening torsion-free slopes exceed −1/2, this is an actual quotient T→T1 in B0, hence a quotient of E. If its slope lay in (−1/2,−6/13], then

 0<y(T1)/r(T1)=μ(T1)+1/2≤1/26,
 ν_s(T1)≤−26m(s)≤−26mG<−δ,

contradicting the quotient inequality for semistability. Thus all positive-rank slopes of T exceed −6/13. Divisorial torsion contributes nonnegative y, and lower-dimensional torsion contributes zero. Consequently y(T)>r(T)/26 if T has positive rank.

Add the two estimates. They give the uniform bound

 |r(E)| ≤ r(F)+r(T) ≤26y(E)                             (8)

for all the indicated finite-slope semistables, on every s≥sG. The non-strict inequality includes rank-zero and torsion cases. This closes the otherwise unjustified passage from a slope-sheaf bound to the rank of a two-term tilt object. At ν_s=0 it applies in particular to nonzero F∈F_s with N_s(F)=0: the definition of F_s supplies the subobject inequality and excludes y=0 subobjects, hence precisely the finite-slope semistability needed above.

For s in a compact interval I⊂[sG,∞), (8) also gives

 |z(E)|≤(δ+13 max_I|s|) y(E),
 |c(E)|≤14y(E),
 |d(E)|≤(δ+13 max_I|s|+15/4)y(E).                        (9)

For a fixed s and a bound y≤Y, there are only finitely many possible triples (r,y,z) of these near-zero semistables: all three coordinates are bounded and lie in a fixed rational lattice. Hence their ν_s values form a finite set under this bound. The third Chern coordinate w is not bounded by (8)–(9), and arbitrary objects have not thereby acquired HN filtrations. This is a precise partial support reduction, not a full support claim.

## 6. What happens to the standard support form at the crossing

BMS's usual form in the β-twisted coordinates is

 Q_K=K(y²−2rz)+4z²−6yw.

On ker Z_{s,A}, parametrized by (r,y,z,w)=(r,y,sr/2,Ay), it becomes

 Q_K|ker = s(s−K)r²+(K−6A)y².                           (10)

For s>0 the familiar choice is s<K<6A. At s=0 the r² coefficient vanishes for every K. At s=sG<0, any K>0 gives s(s−K)>0. Thus the positive-parameter proof cannot simply carry its Q_K through this segment.

The degenerating vector at s=0 is not only a formal irrational direction. In K_num⊗Q it is exp(−H/2); the integral combination

 35[O]−35[O(1)]+21[O(2)]−5[O(3)]

has untwisted coordinates (16,−8,2,−1/3) and twisted coordinates (16,0,0,0). Its charge vanishes at s=0 for every A. This does not contradict the existence of stability at s=0: the support condition forbids such a kernel class from being semistable, not from being a class or the class of an arbitrary object. The rank bound above in fact excludes it from the finite-slope near-zero semistables. Likewise the formal twisted cubic (1,x,x²/2,x³/6) meets the kernel at x=0,s=0. On the negative-s side its imaginary part (x²−s)/2 is positive for every real x. Crossing the boundary of the standard twisted-cubic domain is a limitation of that proof domain, not a general nonexistence theorem.

One can explicitly prepare a different kernel-negative quadratic form if a third-character gap were proved. Suppose, on some proposed heart branch, that for the zero-slope tilt semistables one could prove

 w≤(A−ε)y, with ε>0.                                    (11)

Together with (8), this makes the form

 Q=3ε(y²−r²/676)+6y((A−ε)y−w)+L(z−sr/2)²                (12)

nonnegative on those zero-slope classes, for any L≥0. On the entire two-dimensional kernel its restriction is exactly

 −3ε y²−(3ε/676)r²,

which is negative definite even at s=0. Thus there is no remaining elementary linear-algebra obstruction to replacing (10). What is missing is (11) on an appropriate branch and control of (12), or another support form, on *all actual Bridgeland-semistable objects*. An inequality only on the zero-slope cut is not that control. Transferring a corrected quadratic inequality through all HN/wall steps is part of the unpaid operation. Formula (12) is a concrete reduction, not a conditional nominee and not an assertion that (11) is true at every endpoint in the unmodified heart.

### 6.1 The fixed-form theorem pays the entire open positive segment

A final strongest-payment comparison improves the initial endpoint of the unresolved interval. Choose the rational anchor α*=3/5, β*=−1/2, so s*=9/25>1/4, and put K=1/2. Li's Theorem 1.2 supplies BMS Conjecture 4.1 at this pair. BMS Lemma 8.8, whose hypothesis is this fixed rational pair rather than a global conjecture, gives the support form Q_{1/2} for the known stability condition at Z_{s*,A(s*)}. Its applicability is exact: s*<1/2<6A(s*).

For all 0<s≤s*, equation (10) has strictly negative coefficients:

 s(s−1/2)<0,  1/2−6A(s)<0.

Indeed A(s)≥A(0)=(232−52√5)/687>1/12. Bayer's fixed-Q deformation theorem now lifts the charge path on every closed segment [ε,s*], ε>0, starting from that known stability condition. The lifts agree on overlaps by uniqueness, so they give one continuous lift on (0,s*], in the large-volume component. This is a legitimate use of a fixed support form on a connected kernel-negative domain, not a succession of unspecified shrinking local charts. Together with the Li region it pays all s∈(0,1] in (5).

It does **not** identify the lifted heart with A_s when s≤1/4, or give a limit at s=0. The coefficient s(s−1/2) tends to zero; Q_{1/2} is no longer negative definite on the limiting kernel. The new rank bound in §5 controls tilt-semistables of B0, not all semistables of this lift with its as-yet-unidentified heart. It cannot simply be used to replace the lift's support form. This is the sharper compatibility interface: extend this actual positive-side lift through s=0 to the actual source Gepner endpoint, using a nondegenerating support argument and any necessary explicit heart/boundary tilts. The fixed-form extension is paid primary composition, not an additional nominee.

## 7. The Gepner endpoint has an explicit boundary-tilt description

There is more information here than the mere existence of an unspecified Gepner heart. Let A=A_sG=H_0 in G's grid. Its block filtration has factors in S_4,S_3,…,S_0, hence all its HN phases for the source slicing lie in [0,1]. The source finite block refinements and their merged equal-phase factors remain objects of A; their triangles are short exact sequences there. The phase cut at zero therefore supplies a torsion pair in A:

 T=A∩P((0,1]),     F=A∩P(0).

Its HRS tilt ⟨F[1],T⟩ is exactly P((0,1]). To see both inclusions rather than guess an endpoint convention, every phase generator in (0,1) comes from S_0,…,S_4 and is in T. Phase-one generators come from S_4 and S_5; the latter are shifts of the phase-zero generators in S_0 and therefore belong to F[1]. Conversely T and F[1] have precisely the required phases. Extension closure proves equality. The existence of this torsion pair follows directly from the finite HN filtration inside A, not from an assumption of a stability function on A.

This pays the categorical identification of the actual source endpoint as a specific boundary tilt of the calculable A_sG. It does not show that F=0, so P((0,1]) must not simply be equated with A_sG. Nor does it propagate this boundary torsion pair along (5): away from sG the source eigencharge/periodic sector proof no longer supplies the required slicing. At sG the positive imaginary-coordinate rescaling in (1) preserves the real-axis conventions, so the same boundary-tilt description applies after that GL⁺ action.

## 8. Exact unpaid operation after the strongest reduction

The two ends are real stability conditions, and the actual lift on every s>0 is joined to the full ordinary/Todd large-volume region by the fixed-form argument in §6.1 and paid primary/source operations. The bounded hearts A_s exist across the whole segment. The cohomology argument gives uniform rank and lower-character control near zero slope, a usable replacement for the lost positive-s discriminant estimate. The actual Gepner heart is identified by a source-controlled boundary tilt. These are the integrated payments.

The unresolved operation is to construct compatible slicings through s=0 and over the negative interval [sG,0], starting with that actual boundary-tilted Gepner endpoint, with HN/local finiteness and full support that does not collapse, and to identify it with the actual positive-side lift on an overlap s>0. On the unmodified A_s branch, real-axis positivity is equivalent to

 w(F)<A(s)y(F) for every nonzero F∈F_s with N_s(F)=0.      (13)

Indeed the zero-imaginary T_s objects are zero-dimensional and have negative real charge; a shifted F has real charge w−Ay. Equality would give a zero central charge. Formula (13) is not proved here. A branch with extra boundary tilts can bypass its failure, but then those torsion pairs, their phase assignment, and HN/support compatibility must actually be constructed. The source endpoint gives one such boundary tilt, not the whole interval.

L's strong tilt theorem only controls a large *positive* physical volume. Li's primary theorem directly pays s>1/4, and its rational anchor plus BMS/Bayer pays a lift for every s>0 as above. Xu controls r,c,d and yields (8), but contains no bound on the required w for these two-term objects. Bayer supplies a lift only after the kernel/support hypothesis is established. G supplies full support via a finite-periodic eigencharge grid at its endpoint, not along arbitrary Z_{s,A}. The large-volume Todd perturbation is small in a scaled norm; equations (2)–(4) show why it cannot be mistaken for the missing Gepner operation.

No compatible third-character/phase-cut argument closing this interval was obtained. The continuation direction therefore remains PREFREEZE/no nominee. The heart and rank reductions, the explicit kernel calculation, and the boundary-tilt identification are retained to avoid replacing sustained work by the name of a hard gap. None is offered as a restricted replacement for an immutable old full target. No exhaustion, worldwide-priority claim, correctness/contribution grade, or count is assigned.
