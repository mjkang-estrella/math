# Arithmetic152 — absolute Chow versus support nilpotence

Research calculations, PREFREEZE / no nominee. No theorem is frozen or graded. All Source053 operations at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true. The purpose of the calculations is to carry the chosen operation to its actual remaining interface, not to offer the consequences below as substitute nominees.

## 1. Fixed source interfaces

The formal algebra S_{g,n} has vertexwise decoration cutoff 3g_v−3+n_v, and q[Γ,γ]=ξ_{Γ*}γ is UNNORMALIZED. Graph-sum coefficients, including 1/|Aut Γ| and 2^{-h¹(Γ)}, are separate. P_{g,n} is the complete original outer-graph relation span, already an ideal closed under gluing and forgetting pullbacks and pushforwards. Pixton2012 §§1–3 give precisely this system; PPZ corrected v3 §3.5 supplies the marking-index/partition/outer-gluing generation mechanism. No finite screen is substituted for P.

The source class is Y=Alt_color ∏_J( Dbar_ab Dbar_ac − β_J^st/2 ), with one triple for each increasing triple of g=10^60 colors, D*=C(g,3), n=3D*, degree 2D*. Its Chow image is zero. Its detector lives over R=Λ_Q(θ_ijk), with V=R⊗(Q1⊕W⊕Qe), W odd symplectic of dimension 2g. On a Lagrangian basis a_i, the cubic has coefficient θ_ijk; its correction takes values in the opposite Lagrangian, making its self-contractions zero. The handle is (2−2g)e. Rational tails are compressed by Frobenius coproducts; all other graphs are discarded. The test commutes with the specified forgetting operations, including the per-vertex cutoff checks, and kills the complete P. Its value on Y has the nonzero coefficient ±(C(g−1,2)!)^g ∏θ_ijk. This is a test on FORMAL graphs, not a Chow-valued map.

The geometric algebra B_S is different. For a smooth projective connected genus-b curve C→S with section and a rational relative degree-one divisor e_C, set a_C=π_*(e_C²), e'_C=e_C−π*a_C/2, and η=Δ−e'_1−e'_2. The pure correspondence object H_C has categorical dimension −2b. The source relative pairing relation supplies a tensor functor from the odd symplectic representation category. Its faithful coefficient algebra is

    B_S = ⊕_λ Hom_Chow(1,F_S(X_λ)) ⊗ X_λ^∨.

All actual Chow correspondences are included, not merely pairing diagrams or cohomology. The projected small diagonal is an alternating cubic φ:W_b³→(B_S)_odd. O'Sullivan Lemma2.3.1 explains the coefficient extension and its functoriality. The source gives its explicit split construction and finite same-map polarization. It does not identify B_S with R.

For a finite collection w_α spanning an isotropic subspace of W_b and an arbitrary scalar matrix γ, write

    T_γ = Σ_(α1,α2,α3,β1,β2,β3)
              γ_α1β1 γ_α2β2 γ_α3β3
              φ(w_α1,w_α2,w_α3) φ(w_β1,w_β2,w_β3).

Let c=b−1, χ=c², K²=8χ, t=25χ−1, ν=t−1, D=3K, and N=t−1+24χ. The source proves T_γ^t=0 modulo support of base codimension c when b≥5 and dim S<χ−1. Its proof is in rational Chow throughout. Finite interpolation allows all needed tests to share a finite union of exceptional supports.

The original-exponent question investigated here is whether T_γ^t=0 in FULL B_S for every such family, divisor, isotropic set and matrix, with arbitrary finite base dimension. It is a prospective question, not an asserted theorem. The original exponent is part of it: increasing that exponent does not answer it.

## 2. The determinant-fixed calculation with the base dimension retained

Put d=dim S. The determinant-fixed rank-two Quot target is K⊕O, with torus weights (0,1), determinant D=3K, and ν=t−1. The source constructs the derived tangent as the fiber of

    RHom(I',Q) → Rπ_* I_o[1].

The obstruction trace is surjective because K·D>2K². Its fixed components are pairs of rank-one arrows with total determinant D. For a high divisor with K·D_high>K², forgetting the high arrow gives a bivariant virtual pullback from the low rank-one Quot. These are compatible obstruction theories, not just equal K-classes. Manolache Theorems4.1,4.4,4.8 and Corollary4.9 give the needed proper-push, restriction, and compatible-triple operations. The source explicitly supplies their hypotheses for these schemes.

The relative virtual rank of the full Quot is v=2t+χ−3>2t. With m=3t marked surface outputs and one ch₂(Q) at each output, total codimension before localization is 2m−v. The ordinary codimension-4t coefficient would require equivariant degree 2t−v<0, so the corresponding localized fixed sum is zero. This argument is relative to S and does not use an upper bound for d.

Let P=D_low and y=KP/(8χ). There are two distinct exclusions.

(a) If 0<y<1, the low divisor virtual relative dimension is P(P−K)/2. The intersection p=KP is a positive multiple of 2c and satisfies 2c≤p≤8c²−2c. Hodge index gives

    P(P−K)/2 ≤ (p²/(8c²)−p)/2 ≤ −c+1/4.

The virtual dimension is an integer, so it is ≤−c. Each cycle representing the absolute virtual class has dimension ≤d−c; the closure of its base image has the same upper bound. Thus the low class has base support of codimension ≥c. Smooth point-Hilbert pullback, the low Euler cap, the high bivariant pullback, every operational insertion and the proper marked output push preserve that base support. This exclusion is valid for every d.

(b) On the Picard open H²(P)=0, the source factors the divisor virtual class by compatible virtual pullback from the based derived Picard class. Its absolute virtual dimension is

    d + 1 − χ.

For d<χ−1 the source kills that class outright. For arbitrary d, choose its finite cycle representative instead. The closure in S of the image of each supporting cycle has dimension ≤d+1−χ. Therefore the class is supported over base codimension ≥χ−1. This reasoning does not require the open Picard space itself to be proper: closure of a constructible image does not increase its dimension. Every subsequent compatible operation preserves this base support. Since χ−1=c²−1≥c for b≥5, these contributions still disappear in the same codimension-c support quotient.

Here support is the image of ACTUAL cycle representatives, not a bound inferred only from virtual relative dimension after arbitrary further pullback. Bivariant compatibility is precisely why increasing a cycle's dimension in the high pullback does not increase the locus of S over which it lies. The argument is repeated on a new test base when necessary; it does not assert that an arbitrary pullback preserves the codimension of an old exceptional set.

For y>1, H²(P)=0. At y=1 the only exceptional effective line is K; at y=0 the divisor is empty. Modulo codimension-c support, the four divisor pairs are consequently (0,3K),(3K,0),(K,2K),(2K,K), as in the source. Their point lengths are ν+3K²,ν,ν,ν−K². The last three are <t and vanish by the source short-length argument. Only (0,3K) remains.

The source nested-Hilbert calculation retains every output on that branch. Its pure isotropic block costs are 2 for one output, 4 for two outputs, and 2(k−1) for k≥3. At total codimension 4t on 3t outputs only bare triple blocks survive. Positive horizontal degree has no budget. The fixed procedure is compatible with the relative EGL recursion actually read in Kong §2.1, and goes beyond the latter's integrated-to-base statement by retaining all outputs. The source itself supplies that stronger operation.

The coefficient is unchanged:

    a = 1/(6^t t!) [q^(24χ−1)]
        (1+w)^(24χ)(1+2q)^t(1+4q)^((3−27χ)/2),
    w(1+w)=q, w(0)=0.

Its residue at v=1 after v=1+2w is minus a positive multiple of

    [v^(27χ−5)] (1+v²)^(25χ−1)(1−v)^(−24χ).

All relevant prefactors are nonzero rational numbers. Thus a≠0, exactly as in the stipulated source. MOP's actual symmetric-power/residue proof supplies an antecedent, not a replacement of this marked calculation by numerical universality.

This pays the compatible extension

    T_γ^t ∈ F^c B_S                         (2.1)

for EVERY d, where F^c is the base-support filtration defined below. It removes the base-dimension hypothesis but retains the support allowance. It is a direct source/virtual-pullback consequence, not a substantial nominee.

## 3. Natural support filtration and why an extra argument is needed to iterate

For a Chow correspondence on C^k, F^p means vanishing off some closed Z⊂S with codim_S Z≥p. For B_S, apply that condition to the finitely many Hom_Chow coefficients in an element's irreducible-representation expansion. A finite union combines their supports. This agrees with the source support quotient; rational projectors and intertwiners commute with restriction.

DO NOT assume F^p·F^q⊂F^(p+q) just from the definition. Two supported classes can be supported on the same locus, and arbitrary pullback can destroy a codimension estimate. The iteration below uses the universal validity of (2.1) on NEW smooth test bases, rather than a false formal multiplicativity assertion about support.

If f:T→S is a morphism between smooth quasi-projective bases, pulling the family and e_C gives its own corrected projector: refined base change for smooth proper curve powers identifies f*π_*(e_C²) with π_T*(e_T²). Pullback is thus a tensor functor on the relative Chow correspondences, preserving the chosen pairing diagrams. Using the same rational irreducible representatives and intertwiners gives a homomorphism B_S→B_T sending φ_S and T_γ,S to φ_T and T_γ,T. Rational coefficients w,γ and the abstract W_b remain fixed. This follows directly from the source coefficient construction, and is consistent with O'Sullivan2.3.1(ii). It is not a comparison with the formal detector.

Fix x∈F^p B_S. Expand it into finitely many actual correspondence cycles supported over integral Z⊂S of dimension ≤d−p. Choose a proper resolution T→Z of the entire Z, with T smooth quasi-projective and dim T=dim Z. The pulled curve is still smooth projective and retains its section. There is no need to add a curve to the base to obtain a section.

The proper surjection C_T^k→C_Z^k allows rational lifts of every cycle: choose a closed point in its generic fiber, close it up, and divide by the finite generic degree. After applying the rational representation projectors, these lifts still represent x upon proper pushforward. Correspondence composition and coefficient multiplication obey the projection formula, since the projectors and tensor operations are relative pull/intersection/push operations.

On T, (2.1) expresses T_γ,T^t as supported on a subset of codimension ≥c. Its multiplication with any of the lifted cycles is therefore supported there. Projection formula returns T_γ,S^t x as a sum of cycles whose base images have dimension at most

    dim T−c ≤ d−p−c.

There is no heavy-boundary remainder: C/S remains smooth over all of Z, and the resolution was taken over the whole closed Z. Thus, for this PARTICULAR natural element,

    T_γ^t · F^p B_S ⊂ F^(p+c) B_S.          (3.1)

The assertion holds for arbitrary coefficient multipliers, not only the fundamental class and not only fiberwise numerical tests. All lifts, decompositions, and supports used for a fixed element are finite. It also holds after characteristic-zero scalar extension, by exact scalar extension and finite coefficient calculations.

Starting with 1∈F^0, repeated use of (3.1) gives

    T_γ^(r t) ∈ F^(r c) B_S.

Since F^(d+1)=0, an absolute consequence is

    T_γ^[ t (floor(d/(b−1))+1) ] = 0 in full B_S.       (3.2)

This is an explicit absolute identity for each finite-dimensional base. It does not yield the original exponent t when d≥b−1. It is another paid consequence of source support advancement and ordinary localization/resolution, not a replacement nominee.

There is also a separate elementary cap. If the isotropic input span has dimension s≤b, the restrictions of φ involve at most M=C(s,3) odd coefficients. T_γ is quadratic in these coefficients, so

    T_γ^[ floor(M/2)+1 ] = 0.                         (3.3)

Combining the two valid bounds gives the minimum of their exponents. For s≤b and 5≤b≤301, 2t>C(b,3), so (3.3) already answers the original-exponent question. At b=301 the two integers are C(301,3)=4,499,950 and 2t=4,499,998; at b=302 they are 4,545,100 and 4,530,048, respectively. For the full interval, write c=b−1: six times the difference 2t−C(b,3) equals c²(300−c)+c−12, which is positive for every integer 4≤c≤300. The first range is explained as an automatic portion of the full question, not offered as a restricted theorem nominee. For b≥302, s large and d≥b−1, neither elementary coefficient count nor (3.2) closes the original exponent.

## 4. A concrete retained low-divisor interface

To obtain the original exponent in full B_S, the codimension-c contributions discarded in §2 must be controlled without replacing equality in Chow by equality modulo base support. Before quotienting, the marked localization identity can be organized, with the source common factorial/sign normalization, as

    a T_γ^t + E_low + E_Pic = 0.                     (4.1)

Here E_low collects supported representatives from 0<KP<K², and E_Pic the representatives obtained from the H²(P)=0 Picard-open calculations. These representatives and their separation need not be canonical; their sum equals −aT_γ^t and has codimension-c base support. The precise unpaid condition is E_low+E_Pic=0 in full B_S. It is sufficient to kill each part separately, but that stronger separate vanishing is not asserted necessary. The nonzero scalar cannot remove the error terms.

The source's surviving-branch saturation does not automatically compute (4.1). On a general fixed branch, the line-only part of the marked insertion is

    (L_i+w_i)(D_i+x_i) − (D_i+x_i)^2/2.              (4.2)

For D_i equal to 0,K,2K,3K, its surviving pure test needs positive degree on BOTH curve axes. This is what gives the one-output ordinary codimension cost ≥2. If D_i=P varies through general surface Picard data, the term w_i P has ordinary codimension ONE, because w_i is the equivariant weight. P may have a pure mixed W_b⊗W_b component. That component is not generally killed by isotropy of the same vector set in the two axes. The source fixed-point analysis and the marked output convention are both essential here: equivariant degree is not ordinary codimension.

An explicit linear-algebra calculation isolates the issue. Let W contain two orthogonal symplectic planes with bases x_+,y_+ and x_−,y_−, each paired to 1. Let A act as +1 on the first and −1 on the second. Put

    u=x_+ + x_−,       v=y_+ − y_−.

Then ω(u,v)=1−1=0, so span(u,v) is isotropic, but

    ω(u,Av)=1+1=2.                                  (4.3)

Thus the divisor correspondence represented by A has a nonzero test against two isotropic vectors. The ordinary pairing alone would have given zero. Take γ with the corresponding single off-diagonal entry to retain this term; symmetry of γ is not required by the source theorem.

This situation has an algebraic divisor model, not merely an arbitrary matrix. For b≥5, let E be an elliptic curve, choose a degree-(b−1) line L, and take a smooth double cover C→E defined by a section of L² with 2b−2 distinct zeros. Riemann–Hurwitz gives genus b. Its involution σ has nonzero + and − symplectic eigenspaces on H¹(C,Q); the + space is pulled from E, and its orthogonal complement is the − space. Rational symplectic pairs in those spaces give (4.3). On X=C×C the effective graph P=Γ_σ has

    KP=4(b−1),       P²=2−2b,
    y=1/[2(b−1)]∈(0,1),
    P(P−K)/2=−3(b−1).

Its pure mixed divisor component acts by σ (or its transpose; σ=σ⁻¹), so the displayed pairing is a genuine nonzero realization of that divisor component. Consequently there is no universal rule saying that every low-divisor mixed insertion vanishes on isotropic input.

This example DOES NOT show E_low≠0 or T_γ^t≠0. Over a point the negative virtual dimension kills the low-divisor virtual class. In a family there may be further Euler cancellations, determinant restrictions, or cancellation among branches. Equation (4.3) only identifies the invalid step in extending the bare-triple cost argument to arbitrary P. A complete solution would need the actual marked virtual push with these varying line correspondences, including their Picard and base dependence, or an alternative exact cancellation.

One tempting stronger simplification also needs care. On a smooth Picard torsor with a chosen global relative divisor class, the obstruction bundle is pulled from R²π_*O_{C×C}=(R¹π_*O_C)⊗²; its top Chern class is pulled from the genus-b moduli stack and lies above that stack's dimension. On such smooth components this can annihilate the Picard virtual class. It does not establish that ALL relevant Picard components are smooth over S: additional endomorphism/divisor classes can occur on special loci, and their deformation obstruction is part of the derived Picard theory. No global Euler-bundle replacement is made for those components, and this observation is not used to improve (3.2).

## 5. Strongest-primary comparison and the compactification interface

The original PZ construction verifies actual CohFT gluing by confining correction inputs to an isotropic subspace. Its TopFT vanishes in genus≥2, and its minimal-class deformation checks boundary restrictions directly. It does not make our formal detector a Chow realization or impose all actual cubic relations. Janda's comparison concerns relations obtained from singularities of convergent semisimple reconstruction. The actual proof uses holomorphic R-matrices/shifts and a local analytic comparison; it does not compute the full Chow kernel. Neither primary construction removes (4.1).

EGL's recursion and Kong's relative version lower Hilbert length while preserving the specified line/tangent/diagonal inputs. They are compatible with the source marked procedure. Their numerical or base-pushed universality cannot declare the marked tensor E_low+E_Pic zero. Kong's stronger one/two marked CURVE-output proof separates connected incidence components, with a diagonal-supported correction determined by a left-inverse pushforward. Its next contact equation keeps that correction. There is no analogous read theorem identifying the varying-Picard SURFACE residual in (4.1) with the bare-triple scalar.

OP Quot Lemma34 computes the canonical-curve Euler localization and moving normal cancellation; §5.2 explicitly assumes a simply connected surface for its divisor-times-Hilbert description. C×C is irregular. The stipulated source already supplies the determinant-fixed comparison for arbitrary irregularity, and (2.1) uses that construction. Dropping its trace/compatibility data and using the simpler K-class formula would not improve the argument.

Petersen's wonderful compactification presentation concerns the rational-tails space over a smooth core and a known Chow algebra of curve powers. Source053 already goes further: its bridge term −β/2 cancels the exceptional contribution 1−(1/2)·2=0, and chosen pure lifts differ from raw cubics by pair-times-singleton terms and residual base-divisor operations. Those base-divisor errors vanish on opens of EVERY smooth test family, not just geometric fibers. Source support advancement permits arbitrary cycle multipliers and costs at most 3g−2 steps on the heavy base.

The source's expensive large-vertex step uses c=b−1 support improvement (losing one only when a section is added), while ordinary steps use noise and repeated-color tests. The exterior-ideal argument converts the surface relation to arbitrary-color products at threshold C(m,3)−C(e,3)/2+t, with e even near m/2. Our (2.1) preserves exactly those interfaces and their denominators. Thus it can be substituted in the same support argument when a larger smooth test base occurs. This is compatible reuse of a paid construction. It does not eliminate the compactification's residuals, shorten the color budget by a new mechanism, preserve nonmembership after changing genus/markings, or prove that any pushed/forgotten/symmetrized relation is outside P.

The full original-exponent question remains at (4.1). We have an integrated dimension-free support relation, a justified iteration against arbitrary coefficient multipliers, an explicit absolute larger exponent, and a concrete mixed-divisor obstruction to a tempting further reduction. We do not have an exact cancellation at the original exponent. Nothing is frozen; no author-proof nominee, weaker substitute, grade, acceptance/count, exhaustion, global impossibility, or new-to-literature claim is made.
