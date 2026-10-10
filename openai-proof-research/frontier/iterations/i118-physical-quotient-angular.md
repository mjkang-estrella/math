# I118 — Original I115 audit and physical quotient angular continuation

**Disposition: original scoped I115 proofs PASS without repairs; P112 and A* remain unresolved; no substantial nomination.** The original G112 boundary-component invertibility failure and R112 equal-zero-lambda normalization failure remain failures. Two constructions below produce an explicit uniformly controlled trace quotient, an exact projected commutator residual, an explicit divergence right inverse, and a sharp norm criterion for recovering unscaled divergence from a displacement density. They do not control the actual continued density on the shrinking core. Eight accepted substantial findings remain eight.

All theorems **and lower operations** at `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are accepted. No upstream truth audit, contradiction argument, or ex-falso inference is used. The target is still: on every bounded connected smooth Euclidean three-domain, equality of the static energy forms for every pair of vector displacements supported in the same arbitrary nonempty relatively open proper patch determines both real smooth Lamé coefficients, assuming only `mu>0` and `3lambda+2mu>0`. No accessible or inaccessible interior collar, geometric restriction, coefficient subclass, additional measurement, or enlarged gauge is imposed. Local small balls and finite background bounds below are tools available for each fixed admissible smooth pair, not additional hypotheses on P112.

No children, shared edits, staging, commits, or publication were performed. I116/I117 working outputs are not bound. The launched full brief, its supplied original I115 report and finalized parent response, the separate on-disk originals, and all inherited I112 materials are frozen or directly bound. The original-audit checkpoint was written before the new constructions were promoted to deductions.

## 1. Independent original-proof verdicts

The verdicts concern the **original text**, including its express conditional scopes. A conditional theorem may pass without its antecedent being constructed from P112. The evidence replay is separate from this mathematical audit.

**A115: PASS without repairs, for exact data.** Double localization inside the measured patch identifies the full symbol of the physical traction map. Tan–Liu's complete recursion recovers both boundary values and each next normal derivative, using the invertible two-by-two coefficient matrix with determinant `mu(lambda+3mu)^2`; tangential differentiation supplies mixed derivatives. Here `lambda+mu>mu/3`, so the denominators stay nonzero. Localization changes no homogeneous symbol at points where the cutoff is one. The boundary charts are the same known Euclidean charts; there is no hidden boundary diffeomorphism.

The bump graph `s=-b(z)` is a smooth boundary, including its flat edges. The open cap itself may narrow there; it need not have an independently smooth closed boundary for the variational argument. Extend the first pair through a neighborhood of the compact attachment. Flatness of the difference makes its zero extension smooth for the second pair. Positivity persists in a sufficiently thin neighborhood; the admissible cone is convex. Korn and Poincaré on the enlarged bounded connected domain give coercivity. C112 applies because the attachment is compactly contained in the measured patch and the original-boundary traces belong to the supported trace space. Differentiating the common displacement in the open cap gives common actual divergence. This is a constructed exact-data cap, not interior collar agreement or noisy all-jet reconstruction.

**(4.1)–(4.5): PASS without repairs at their stated conditional scope.** On four trace-free symmetric Hessians, the three displacement contractions form the map `C`. Tensor Frobenius pairing gives

\[
 (C^*t)^q_{ab}=\tfrac12(\delta_{aq}t_b+\delta_{bq}t_a)-\tfrac13\delta_{ab}t_q,
 \qquad CC^*=\tfrac53I.
\]

Consequently the kernel has dimension `20-3=17`, and its annihilator is exactly the indicated three-dimensional image. The scalar Hessian column is unrestricted within its five-dimensional trace-free space. The original variable-coefficient J112/L112 compatibility establishes realizability, so this is an actual physical test space.

For the comparison `U2=(I+Z)U1+D^a partial_a U1+R`, expanding `Lcal2` and differentiating `Lcal1 U1=0` cancels third derivatives. The remaining second derivative coefficient is exactly original (4.3), with the right-side products `-D^b A1^a` in the stated order. The displayed `Y` and `V` retain the derivatives of the first operator and all zeroth-order terms. Inverting the finite test matrix **before differentiating** eliminates `Y,V` identically. Bounds for that inversion depend on the selected source family and its jets, as the original text says; it supplies no angular norm bound.

The replacement `D^a_{alpha q} -= f_alpha delta_aq`, `Z_{alpha4} += f_alpha` adds the identically zero function `f_alpha(d-div u)`. Its differentiated identities are valid on realizable prolongations. The trace normalization removes one scalar function per output row. These are four scalar gauge functions across four rows, not four freedoms in a single row. This finite differential gauge is distinct from the infinite-dimensional boundary annihilator.

**F115 principal certificate: PASS without repairs.** I reconstructed the degree-four integer matrix column by column from polynomial differentiation, without importing either I115 matrix constructor. Its dimensions are 195 by 165. On the original specified 165 rows the determinant is 166021 modulo 1000003; trial division verifies primality. Thus this is an injective map over the rationals, reals and complexes. The original exact ranks at degrees one through five remain `18,51,100,165,234`. The degree-three kernel of dimension eight prevents replacement by the source's two-prolongation closure.

**F115 scalar-column coupling, variable coefficients and closure: PASS without repairs.** At highest order the displacement-column block is the certified map and the scalar-input-column block is the conformal-Killing map. Its degree-three kernel is zero by the source's complete differentiation proof, hence so is its degree-four kernel. The direct sum is injective. Matrix multiplication in (4.3) may mix output rows and the scalar/displacement input columns, but it is zeroth order in `D`. After three differentiations it uses at most three derivatives of every column, including the scalar column. It therefore belongs to the right-hand side of the same **coupled** left-inverse equation; there is no assumption of a decoupled scalar equation at lower order.

Differentiate the algebraic trace normalization as well. The unknown highest tensor consists of fourth derivatives of `D` and third derivatives of the auxiliary `t`. The constant left inverse determines them from `D` through order three and `E` through order three. Smooth lower coefficients only alter the latter expressions. A small principal-map perturbation retains the positive least singular value, precisely the limited perturbation claim in I115; arbitrary changes of physical coordinates are not asserted. Along a compact path the order-three jet is a finite linear ODE with bounded coefficients. A zero germ and zero forcing imply zero by Gronwall. With `E` through order eight bounded by `Cr(y)^(3/2)` on a monotone-radius path, the initial ODE and five further differentiations give `D` through order nine with the same bound. The analytic input remains conditional.

**H115 embedding and rigidity: PASS without repairs, conditional on open image comparison.** Joint finite-point jets separate the response four-planes. The scalar response derivative in any nonzero spatial direction cannot lie in the value span: `grad d` is free with `(u,d)` fixed. A finite collection of source tests witnesses the local immersion. Open equality of images then gives a smooth local inverse chart and the explicitly stated invertible comparison matrix. Tangency or coincident Taylor jets of two image submanifolds does not give that open equality.

The physical divergence of `u2=A u1(Phi)+b d1(Phi)` first forces `b=0`, using free `grad d1`, then `JA=sI`, and the value terms give `c_q=partial_i A_iq`. Principal Hessian kernel inclusion is legitimate for the full displacement equation and yields `p2(J^t eta)A=T p1(eta)`. Taking determinants and using positivity for real covectors forces `JJ^t=rho^2 I`. The displayed conformal equations close for `(Phi,J,log rho,grad log rho)` and propagate the identity from the cap. Once `Phi=Id`, constant-displacement formal two-jets force `L2(s e_q)=0`; UCP removes `s-1`. This argument retains the exceptional coefficient ratios and does not divide by `lambda-mu`. R112 then gives proportionality, and **positive mu** equality in the cap fixes its scale. It does not use the failed equal-zero-lambda shortcut. No compactness of a general `GL(4,R)` comparison group is imported from the source's unitary group.

**Fixed-radius product continuation and physical transfer: PASS without repairs at the stated coverage scope.** The normalized augmentation is scalar-principal on each tensor factor; the physical Green matrix is augmented by actual differentiation of its two factors, not declared to be an inverse for arbitrary four-component sources. The accepted cross-series and compact-cylinder operations need separate equations, bounded data at fixed separation and their stated strict geometry. They do not require full-system source surjectivity. They apply to this augmented product solution.

For the divergence defect `Q=div_x K_{1:3,*}-K_{4,*}`, the first augmented equation and compatibility identity imply `(Delta_x+grad log m1 dot grad_x)Q=0`; the second-variable system commutes with that defect operation. The sum is scalar-principal elliptic on the product. UCP on each attached extension component propagates the zero defect. Repeat in the other factor. This handles overlaps without a connected-slice assumption.

The top block therefore obeys both physical equations. The positive-`P=-L` Green identity has the sign in (4.10). Moving its flux to a fixed slightly larger surface in the continued collar justifies differentiation in the second variable; actual traction and symmetry give the correct row transpose. This transfers every local physical solution and reproduces the paired sources by UCP. It supplies a smooth density at each positive radius. **It supplies no bound uniform as that radius tends to zero.** The original text made this distinction, so no repair is needed. Physical dilation must use `(u_epsilon,d_epsilon)=(u(epsilon z),epsilon d(epsilon z))`; its normalized top coupling tends to a bounded nonzero Lamé coupling, not necessarily to zero. The accepted product operations require bounded lower coefficients, so this does not invalidate their use.

**Graph and annihilator: PASS without repairs.** Eliminating `partial_nu u_nu` from traction and divergence gives exactly

\[
 \mathcal T_Bg=\ell^{-1}\{\nu\cdot\Lambda_Bg+
 2\mu(\operatorname{div}_\Sigma g_T+H g_\nu)\},\qquad \ell=\lambda+2\mu.
\]

Its graph is the whole physical trace space because the physical Dirichlet problem is uniquely solvable for every displacement trace. Transposition on the normalized pulled-back surface measure gives exactly `(-T_B^t a,a)`. In Sobolev language the graph belongs to `H^s` displacement and `H^(s-1)` divergence; smooth statements in the original text need no new assumption. Treating this as a bounded graph on unweighted `L2` would be an incorrect new application, not a claim made there.

**Boundary signs, cutoff and whole-domain budgets: PASS without repairs.** For zero-boundary scalar `v`, the real cross term between `-Delta-tau^2|alpha|^2` and `2tau alpha dot grad` is `-2tau integral (alpha dot nu)|partial_nu v|^2`. Reversing the weight reverses this boundary sign. A zero displacement trace leaves `d=partial_nu u_nu=nu dot traction/ell`, so the augmented scalar boundary term cannot be dropped. The stress product rule gives (5.3); its weak divergence term gives the stated `t^-1 H1` bound, while the strong estimate retains `t^-2 u`. Physical cutoff adds `(0,grad chi dot u)` exactly. The conjugated commutator retains `h/t`, `1/t`, `h/t^2` and `h/t` with the original signs irrelevant only after absolute values.

Splitting the bilinear identity leaves both the approximant collar integral **and the target collar integral** in (6.1). On the collar, Green's identity gives (6.2) with the inner normal directed toward the recovery set. Its outer integrated flux is the supported measured pairing; zero inaccessible displacement does not remove the inner flux. Flatness gives arbitrary **fixed-order** decay only in a smaller accessible collar. B112 bounds individual energies, not the sign of a cross-medium collar product. The `O(tau^(2-N))` divergence error must be multiplied by every loss. The original scoped obstruction and its decision to park naive expanding Runge pass; neither is a P112 counterexample.

**Preserved I112 failures.** A compact manifold may have a closed component carrying constants in the Dirichlet Laplacian kernel. G112's standalone invertibility sentence therefore fails; its connected, nonempty-boundary application passes. For R112, `(lambda,mu)=(0,1)` and `(0,2)` have proportional operators and identical solution jets but equal lambda everywhere with scale two. Its last normalization sentence fails literally; its proportionality theorem passes. Those pairs have different DN maps. Neither failure refutes P112 or an accepted source.

**Full-scope technical contribution check.** A115 is the actual elastic local-symbol recursion plus the source's flat cap/variational replacement. The residual is exact tensor duality on J112's actual physical jets. F115 changes the finite principal matrix and prolongation order, then uses the source's full left-inverse/path-ODE operation. H115 uses source jet separation, an explicit Lamé determinant, conformal finite type and physical UCP; its antecedent is additional. Fixed-radius transfer uses the complete accepted cross-series, strict-sphere and overlap constructions plus physical defect UCP and Green's identity. The graph, signs and budgets are the displayed physical differential identities at their full variable-coefficient scopes. These reductions account for each whole positive claim, not only constant-coefficient examples or theorem-title matches. None pays the new quotient coercivity step; none is nominated as substantial.

## 2. Source operations and what was actually read

Let **E** be the pinned full-boundary elasticity paper, **M** the pinned October 5 metric/connection one-patch paper, and **C** its September 24 scalar companion. The complete M introduction, boundary/source/contact section, product section, sphere section, angular section, matrix section and globalization section were read through their endings. This includes the cross completeness check, separated initialization and overlap paths; the sphere Hessian cancellation and cutoff geometry; all degree-weight calculations, scalar squared-norm commutators and matrix comparison; interpolation, prolongation and the one-fixed-dilation argument; and the use of compact unitary fibers at a frontier. C's entire bootstrap was read. M reproduces the relevant scalar product/sphere/angular operations; I do not relabel a title screen as a read of every other C section.

E's main contract, full boundary-reduction section and complete augmentation proof were read directly. Its further full operations and I112/I115 proof passages remain immutable inherited readings, not new full semantic reads by I118. No arbitrary augmented DN data are inferred from E. Tan–Liu v1's statements and complete symbol recursion/recovery through the analytic proof ending were read. Its current primary metadata still lists v1; analyticity is not used. The newly observed primary source *Hardy spaces for the Lamé equation*, arXiv:2510.10798v1, gives constant-coefficient ball Poisson formulas and vector spherical decompositions. Its contract, complete Poisson section and appendix were read; the later decomposition proof was not used. It supplies no cross-medium shrinking continuation theorem. The elementary polynomial formulas below are derived independently and agree with that classical Poisson construction. Current upstream main was observed equal to the pinned revision.

The inherited 13,223-entry tree, 749 manuscripts and 10,373 original positions are reused by reference, including 776 inherited PDF texts. All inherited lexical occurrences and a new exact physical/quotient query are replayed with membership, multiplicities and spans. This is full-domain **lexical** coverage, not semantic reading of all manuscripts. No earlier evidence verifier is invoked recursively and no corpus is copied. Reading ranges and conventions are in `read-manifest.json`; bounded current literature checking is not a worldwide-priority claim.

## 3. Physical scaling and the exact quotient

Work first on Euclidean balls `B(y,r)` compactly inside a fixed coefficient chart, with normalized unit-sphere measure. All constants may depend on a fixed finite collection of smooth coefficient bounds and positive ellipticity/energy lower bounds. For each requested finite Sobolev/parameter order, fix the corresponding finite Dirichlet and symbol estimates first; then choose `r0>0`. There is no coefficient-smallness assumption: shrinking a ball makes its rescaled coefficients close to their values at its center.

Set

\[
 m=\mu(y),\quad \kappa=\lambda(y)+\mu(y)>m/3,
 \quad B_r=r\mathcal T_{B(y,r)}.
 \tag{3.1}
\]

After pulling back by `x=y+r z`, `B_r g` is the boundary value of `div_z v`, where `v(z)=u(y+r z)`. The rescaled Dirichlet operators are a smooth uniformly invertible family down to `r=0`, whose limit is `m Delta+ kappa grad div`. Thus `B_r` is a smooth order-one boundary family down to zero, uniformly `H^s -> H^(s-1)`, with `B_r-B_0=O(r)` in every fixed symbol/parameter seminorm. This follows by the decaying-root boundary construction and differentiation of the true Dirichlet inverse; the latter bounds the smoothing remainder as well. The frozen explicit root in §4 verifies the physical root rather than assuming the scalar one.

For the source's actual conformal-reference geodesic spheres, use `x=exp_y^gamma(r z)`. Since `gamma` is a fixed smooth conformal multiple of the Euclidean metric here, its frozen map is `x=y+c(y)r O(y)z`. A smooth frame removes `O`; the physical length is `s=c(y)r`. The residual change of the unit-ball operator, Jacobian and trace is `O(r)` with smooth parameter dependence. Every construction below carries over with `s` replacing `r` and bounded positive `c`; differentiation retains its bounded derivatives. This does not change the sphere family or its required strict-concavity geometry. In the following formulas Euclidean notation displays the local model; on M's family these pullbacks and densities are included.

Use a fixed positive order-one sphere operator `Lambda=(1-Delta_S)^(1/2)` and put

\[
 F_r=\Lambda^{-1}B_r,\quad G_r g=(g,F_rg),\quad
 \Pi_r=G_r(I+F_r^*F_r)^{-1}G_r^*.
 \tag{3.2}
\]

The balanced physical trace is `(g,Lambda^-1 r d)=G_r g`. The order-zero operator `F_r` is bounded on each fixed `H^s`. Since `I+F_r^*F_r >= I`, its inverse exists on `L2`; its positive principal symbol and elliptic regularity give bounded inverses on all fixed Sobolev scales. The displayed formula is the orthogonal projection onto the closed graph. Its orthogonal complement is exactly `{(-F_r^*a,a)}`. For smooth real densities, the stars agree with the real transposes; after complexification keep Hilbert adjoints for norms and bilinear transposes for evaluation. Undoing the balancing gives original `(g,T_Bg)` and `(-T_B^t a,a)` exactly.

This constructs a smooth uniformly bounded quotient projection; it is more than a dimension count. Its parameter derivatives are bounded before substituting the radius profile. After substitution `r=r_delta(y)`, each fixed number `j` of base derivatives has at worst the profile allowance `C_j beta^j`. This is not a claim of a constant bound for every unweighted base derivative. Angular commutators are retained as pseudodifferential compositions, for example `[Lambda,Pi_r]`, of their actual orders.

Scaling the **output** as well is necessary for a uniform balanced norm: let `R=diag(I3,r)`, so output is `(S,r div S)`. Even local evaluation of unscaled divergence on `g(omega)=omega` has value `3/r`, while its balanced input trace is uniformly bounded. An output-scaled estimate is therefore a different assertion from I115's unscaled A*. If `hatPsi` represents balanced input and scaled output, the unscaled representative is

\[
 \Psi=R^{-1}\widehat\Psi\,\operatorname{diag}(I_3,r\Lambda^{-1}).
 \tag{3.3}
\]

Its lower-left block contains `r^-1`. A bound for `hatPsi` alone cannot simply be inserted into the unscaled four-component Taylor calculation. Section 5 identifies precisely which part of that lower-left block must gain a power of `r`.

## 4. Construction Q: projected angular equation and symmetrizer attempt

### 4.1 Frozen physical normal symbol — an exact obstruction to the scalar perturbation shortcut

Freeze any admissible constant pair in the upper half-space `t>0`. Let tangential covector `eta` have length `q>0`, put `v=(i eta,-q)^t`, and seek a decaying solution

\[
 u(z',t)=e^{i\eta\cdot z'-qt}(a+t b),\qquad
 d=e^{i\eta\cdot z'-qt}D.
\]

The divergence equation gives `Delta d=0`, so `v^t b=0`. The displacement equation and the boundary divergence identity give

\[
 b=\frac{\kappa}{2mq}vD,\qquad
 D=i\eta\cdot a_T-q a_n+b_n
   =\frac{2m}{2m+\kappa}v^t a.
 \tag{4.1}
\]

Substitution verifies both equations, since `v^t v=0`. These solutions realize every boundary vector `a`; uniqueness of the decaying Dirichlet branch identifies the symbol. The outward normal derivative has symbol

\[
 \mathsf N(\eta)=qI-\frac{\kappa}{(2m+\kappa)q}vv^t=qI-N,
 \quad N^2=0,\quad N\ne0.
 \tag{4.2}
\]

The scaled divergence trace has row symbol `2m v^t/(2m+kappa)`, of rank one and size comparable to `q`. Thus the physical normal derivative differs from the componentwise harmonic derivative by an **order-one** term. It is not an order-zero remainder, even in the frozen admissible medium `(lambda,mu)=(0,1)`.

There is no positive definite Hermitian matrix `H(eta)` making `H Ncal` Hermitian at a nonzero covector: such an `Ncal` would be similar to a Hermitian matrix and hence diagonalizable, whereas `qI-N` has a nonzero nilpotent Jordan part. This also precludes conjugating that normal symbol to `qI`. This is a fully proved, narrowly scoped obstruction to the proposed positive-Hermitian normal-trace symmetrizer and to M's bounded `Psi^0` perturbation argument on displacement traces. It does **not** exclude an energy argument for a nonnormal operator, a different symmetrizer for the full projected angular equation, or the self-adjoint physical traction operator. It supplies no pair with equal inverse data.

On unit-ball physical traces let `A_i^el g` be the trace of `partial_i u_g`. Derivatives commute with a constant Lamé operator, so Dirichlet uniqueness gives

\[
 \sum_i A_i^{el}A_i^{el}g=(\Delta u_g)|_S
 =-\frac{\kappa}{m}(\nabla\operatorname{div}u_g)|_S.
 \tag{4.3}
\]

This is generally nonzero, unlike the harmonic identity in M. For example let `H=e1(z1^2-z2^2)` and

\[
 u=H-\frac{\kappa}{3m+\kappa}(|z|^2-1)e_1.
\]

It is the physical Dirichlet solution with trace `H`; direct differentiation gives `Delta u=-6kappa e1/(3m+kappa)` and `div u=6m z1/(3m+kappa)`. Hence the nilpotent-symbol issue has an actual physical polynomial witness, independent of any pseudodifferential asymptotics. Applying the scalar degree-raising proof to this trace discards a nonzero term of size `r^-1` in its model after the outer factor `r`. One must build the physical cancellation into the full quotient equation.

### 4.2 The constructed quotient equation and its exact remaining residual

Let `C_i` be the moving-trace operators for the small-ball **unrestricted** normalized augmentation, used here only as an ambient extension to define differentiation of traces. Its Dirichlet realization is invertible for sufficiently small balls by the rescaled Laplacian limit. On physical traces it agrees with actual differentiation. Put

\[
 W=\operatorname{diag}(I_3,r\Lambda^{-1}),\quad
 \widehat C_i=(\partial_iW)W^{-1}+WC_iW^{-1},\quad
 \widehat D_i=\partial_i+\widehat C_i^t.
 \tag{4.4}
\]

This retains both the derivative of the radius and the angular Sobolev balancing. On a nontrivial sphere frame use horizontal derivatives and include the derivative of its fixed operator `Lambda` in the same formula. No factors are commuted across one another.

The output-scaled equation is `widehat Lcal2=R Lcal2 R^-1`. In flat base coordinates let `E4=diag(0,0,0,1)` and `f_i=partial_i log r`. Its coefficients are exactly

\[
 \widehat A_2^i=R A_2^iR^{-1}-2f_iE_4,
\]
\[
 \widehat A_2^0=R A_2^0R^{-1}
 -\sum_i f_i R A_2^iR^{-1}E_4
 +( |df|^2-\Delta f)E_4.
 \tag{4.5}
\]

In particular the top-right first-order block contains `kappa/(m r)`, even for constant coefficients. Disregarding that term because the original augmentation was scalar-principal would be incorrect. With the fixed conformal scalar multiplier, replace the base Laplacian by the corresponding scalar covariant contraction and include its fixed drifts; the conjugation rule is the same product rule.

For the actual fixed-radius physical transfer choose any smooth balanced density `hatPsi`; for instance the displacement density and its differentiated scalar output, balanced as above. Testing the output equation against all physical inputs gives

\[
 \Pi_r\widehat P\widehat\Psi=0,
 \qquad \widehat P=r\left(\sum_i\widehat D_i\widehat D_i
             +\widehat A_2^i\widehat D_i+\widehat A_2^0\right).
 \tag{4.6}
\]

Here the projection acts on each input row through the Hilbert identification; output matrices act on the other index. The full residual is in the annihilator, not necessarily zero.

This defines an actual quotient operator, not just a tested relation. If `n(y)` is a smooth annihilator section, its pairing with the trace of every local physical solution is identically zero. Differentiating and using (4.4) shows `Dhat_i n` is again in the annihilator. The dense physical traces are justified by solving on slightly enlarged physical balls and passing to the limit in fixed smooth norms, exactly the source's ball argument with the coercive physical inverse. Thus

\[
 \Pi_r\widehat D_i(I-\Pi_r)=0,
 \qquad \Pi_r\widehat P(I-\Pi_r)=0.
 \tag{4.7}
\]

The projected density `phi=Pi_r hatPsi` solves `Pi_r Phat Pi_r phi=0`. No nonphysical extension is asserted to solve the output equation on all augmented inputs.

For a section with `Pi_r phi=phi`, the exact discarded component is

\[
 (I-\Pi_r)\widehat P\phi
  =(I-\Pi_r)[\widehat P,\Pi_r]\phi,\qquad
 [\widehat D_i,\Pi_r]=\partial_i\Pi_r+[\widehat C_i^t,\Pi_r].
 \tag{4.8}
\]

In Euclidean base coordinates the commutator is, without suppressed compositions,

\[
 [\widehat P,\Pi_r]=r\sum_i\bigl\{
 \widehat D_i[\widehat D_i,\Pi_r]
 +[\widehat D_i,\Pi_r]\widehat D_i
 +\widehat A_2^i[\widehat D_i,\Pi_r]\bigr\}.
 \tag{4.9}
\]

The zeroth-order output coefficient commutes with the input projection; horizontal versions retain the corresponding fixed connection terms. The exact squared-norm decomposition is

\[
 \|\widehat P\phi\|^2
 =\|\Pi_r\widehat P\Pi_r\phi\|^2
  +\|(I-\Pi_r)[\widehat P,\Pi_r]\phi\|^2.
 \tag{4.10}
\]

Full-system coercivity therefore does not, by taking an orthogonal projection, give coercivity for the first term. The second term has not been estimated by a small multiple of the relevant weighted angular/base norm. Equations (4.2)–(4.5) show why the source's **specific** scalar lower-order absorption does not estimate it. Merely invoking symbol smoothness of `Pi_r` would omit the `r^-1` trace coefficients, the `f_i` terms and matrix principal commutators. The projection construction itself remains valid.

For a fixed base cutoff, `Pi_r` commutes with its multiplication, and

\[
 [\widehat P,\chi]=r\{2\chi_i\widehat D_i+
                \Delta\chi+\widehat A_2^i\chi_i\}.
 \tag{4.11}
\]

On the lower cutoff region the local-evaluation construction in §5 supplies uniformly bounded **scaled** densities, angular derivatives and the needed weighted base derivatives; on positive depth the radius has the fixed positive lower bound from M. The problem is the shrinking core, not unconstructed cutoff data. Subtracting a local evaluation representative gives an explicit known normalization, but ordinary angular mean-zero is not invariant under `Pi_r`. The physical constant/first-jet moments must be tracked as a finite block, not silently replaced by four independent constant augmented solutions. There are 15 physical first-jet coordinates per evaluation row and one divergence gauge in the 16 coefficients `(Z,D)` of that row. A finite source right inverse gives this block locally; it gives no small estimate for (4.8).

**Result of Construction Q.** A uniform smooth graph projector, a well-defined physical quotient equation and all its projection/cutoff residuals have been constructed. The direct scalar perturbation and positive-Hermitian normal-symbol symmetrizer proposals fail in the explicit frozen model. The remaining possibility is a new coercive estimate for the **full nonnormal quotient operator**, with its finite normalization block and the terms (4.8)–(4.11) paid. No estimate of that strength is proved here.

## 5. Construction D: displacement density with exact divergence recovery

### 5.1 An explicit frozen right inverse and a uniform trace-kernel projection

Let `h_l` be any homogeneous harmonic scalar polynomial of degree `l>=0` on the unit ball. Seek

\[
 v_l=a_l z h_l+b_l(|z|^2-1)\nabla h_l.
\]

The identities `div(z h_l)=(l+3)h_l`, `div((|z|^2-1)grad h_l)=2l h_l`, `Delta(z h_l)=2 grad h_l`, and `Delta((|z|^2-1)grad h_l)=(4l+2)grad h_l` give `div v_l=h_l` and the Lamé equation when

\[
 a_l=\frac{m(2l+1)+\kappa l}{m(2l+3)(l+1)},\qquad
 b_l=\frac{-(\kappa/m)(l+3)-2}{2(2l+3)(l+1)}.
 \tag{5.1}
\]

The two scalar equations have determinant `2(2l+3)(l+1)>0`. For `l=0` the gradient term vanishes and `a0=1/3`, giving the same assertion directly. The trace is simply `a_l omega h_l`. In particular, with harmonic expansion `h=sum h_l|S`,

\[
 \mathcal R_0h=\sum_{l\ge0}a_l\omega h_l,
 \qquad B_0\mathcal R_0=I.
 \tag{5.2}
\]

On any fixed compact admissible coefficient range, `a_l` and all fixed parameter derivatives are bounded by `C/(l+1)`; multiplication by `omega` only shifts harmonic degrees by one. Hence `R0:H^s -> H^(s+1)` is bounded for every real `s`. Rapid harmonic decay proves the identities for smooth `h` by convergence of all derivatives; Sobolev density extends them. This is an explicit full boundary right inverse, including the constant mode.

For variable coefficients in a sufficiently small ball, `B_r R0=I+O(r)` on each fixed `H^s`. The inverse Neumann series on one fixed scale and elliptic regularity give

\[
 \mathcal R_r=\mathcal R_0(B_r\mathcal R_0)^{-1},\qquad B_r\mathcal R_r=I,
 \tag{5.3}
\]

smoothly in center and radius down to zero, with the same fixed-scale bounds. This is a local construction, available for every smooth admissible medium. It assumes neither a small global shear gradient nor agreement of two media.

On real sphere `L2`, define

\[
 K_r=(B_rB_r^*)^{-1}B_r,\qquad
 \mathsf S_r=I-B_r^*K_r.
 \tag{5.4}
\]

These formulas are well defined. Indeed the right inverse (5.3) on `H^-1 -> L2` gives `||a||H1 <= C||B_r^*a||L2` by duality. The form `||B_r^*a||^2` is coercive on `H1`, so `B_rB_r^*:H1 -> H^-1` is invertible. Its symbol is scalar elliptic of order two by (4.1), and smooth elliptic inversion controls all fixed Sobolev orders and parameter derivatives. Thus `K_r` has order minus one and is uniformly `L2 -> H1`; `S_r` is a smooth uniformly bounded order-zero **orthogonal** projection onto `ker B_r` in `L2` (where `B_r:L2 -> H^-1`). In particular `S_r^2=S_r`, `S_r^*=S_r`, and `S_rB_r^*=0`. At frozen coefficients this kernel consists precisely of traces whose physical extension is divergence free. For variable coefficients it means **zero boundary divergence**; no assertion of zero interior divergence is made.

### 5.2 Sharp quotient norm criterion

**D118 (author proof, technical).** For the above small-ball family, let a smooth row `h` act on displacement traces, and put `Q=r h`, `J=S_r Q`, `a=K_r Q`. Its physical unscaled graph-dual norm is

\[
 \mathfrak q_r(h)=\inf\{(\|p\|_2^2+\|b\|_2^2)^{1/2}:
                  h=p+r^{-1}B_r^*b\}.
\]

There are constants independent of `0<r<=r0<=1` such that

\[
 c\bigl(\|J/r\|_2+\|a\|_2\bigr)
 \le\mathfrak q_r(h)
 \le\|J/r\|_2+\|a\|_2.
 \tag{5.5}
\]

All equalities with unbounded boundary operators are distributional; the constructed representative is smooth when `h` is smooth. The same inequalities hold after integration over a compact base region, with the fixed smooth sphere measures.

**Proof.** Orthogonal decomposition gives `Q=J+B_r^*a`, so `(p,b)=(J/r,a)` is an admissible representative. Conversely, from any admissible pair, `Q=r p+B_r^*b`. Apply `S_r` to obtain `J/r=S_r p`, whose norm is at most `||p||`. Apply `K_r`, using `K_rB_r^*=I` distributionally, to obtain `a=r K_r p+b`. Uniform `L2` boundedness of `K_r` and `r<=1` give the lower estimate. For nonsmooth `b`, the identity follows from the inverse on `H^-1` or by distributional density. Integrating the same uniform estimates proves the base version. This proves both directions; no source-conditioning estimate is hidden. ∎

Thus if `Q` is bounded in `L2`, bounded unscaled divergence representation is equivalent to the exact additional gain

\[
                    \|\chi\mathsf S_r Q/r\|_{L^2}\le C.
 \tag{D*}
\]

This improves the vague concern about differentiating a density into a necessary-and-sufficient criterion at this trace-norm scope. The criterion retains the whole infinite-dimensional kernel. Finite moment normalization cannot enforce it: for every large `l`, a nonzero field `g=z cross grad h_l` is homogeneous, harmonic, divergence free, and tangent on the sphere. Its components have harmonic degree `l`. Hence `g in ker B0` and its pairings with every fixed finite family of lower-degree polynomial moments vanish for `l` sufficiently large. Taking `Q=g|S` leaves `S0 Q=Q`, giving a `1/r` norm loss in (5.5). This is a counterexample only to an inference from bounded norm plus finitely many moments, **not** a proposed actual continued density or an inverse-data pair.

### 5.3 The local-evaluation seed really pays this loss

Let `P_{y,r}(z,omega)` be the physical Dirichlet Poisson kernel on the rescaled unit ball and set

\[
 F^{ev}_{y,r}(\omega)=P_{y,r}(0,\omega),\qquad
 Q^{ev}_{y,r}(\omega)=\sum_i\partial_{z_i}P_{y,r;i,*}(0,\omega).
 \tag{5.6}
\]

These are smooth kernels with uniform angular and fixed parameter derivatives down to zero: the evaluation point stays strictly inside the fixed ball; Dirichlet regularity and differentiation of its inverse prove the assertion, including smoothing terms. They represent `u(y)` and `r div u(y)` respectively.

For frozen coefficients, `div v` is harmonic. Its mean over the ball equals its value at the center, and the divergence theorem yields

\[
 Q^{ev}_{0}=B_0^*1=3\omega^t.
 \tag{5.7}
\]

Thus smooth parameter dependence gives `Qev_r-B_r^*1=O(r)` in every fixed smooth sphere/center norm. It follows that

\[
 u(y)=\int F^{ev}_{y,r}g\,d\omega,\qquad
 \operatorname{div}u(y)=\int\left\{
       \frac{Q^{ev}_{y,r}-B_r^*1}{r}\,g+d|_{\partial B}\right\}d\omega.
 \tag{5.8}
\]

This is a constructed uniformly bounded **unscaled** augmented representative for ordinary local evaluation. Its divided difference extends smoothly to `r=0` by the integral Taylor formula, so the assertion includes fixed parameter derivatives, not just an `O(r)` norm slogan. On a profile `r_delta`, its first base derivative is bounded by `C(1+|dr|)`, and `|dr|=r beta` is uniformly bounded. Higher derivatives retain the specified profile allowances. On conformal-reference geodesic spheres, the frozen harmonic-mean weight and Jacobian are pulled back first; their bounded center-dependent factor replaces `1`, and the same divided-difference proof applies. Choosing that exact frozen weight, rather than assuming geodesic surface measure is Euclidean, is essential.

There is also an explicit frozen displacement density. If `H_k` is a homogeneous harmonic vector polynomial of degree `k>=2`, its physical Dirichlet extension is

\[
 H_k-\frac{\kappa(|z|^2-1)\nabla\operatorname{div}H_k}
              {m(4k-2)+2\kappa(k-1)}.
 \tag{5.9}
\]

The proof is the same two product identities used above, with `div H_k` harmonic of degree `k-1`. Degrees zero and one need no correction. At the center only degrees zero and two contribute; normalized sphere moments therefore give

\[
 F^{ev}_{0}(\omega)=\alpha I+\beta_2\omega\omega^t,
 \qquad \beta_2=\frac{15\kappa}{2(3m+\kappa)},\quad
 \alpha=1-\beta_2/3.
 \tag{5.10}
\]

For verification, `integral omega_i omega_j=delta_ij/3` and
`integral omega_i omega_j omega_k omega_l=(delta_ij delta_kl+delta_ik delta_jl+delta_il delta_jk)/15`; pairing (5.10) with a harmonic quadratic gives exactly the constant correction in (5.9). These formulas also show directly why the physical evaluation seed differs from scalar mean value. The classical constant-coefficient Poisson formula in the newly read primary paper already contains this mechanism; it is not a substantial novelty claim.

### 5.4 Applying the construction to the actual continued transfer

Let `F_delta(y,omega)` be the displacement density obtained from I115's **physical** flux, with normalized moving-sphere measure. Write `C_i^el` for the physical displacement moving-trace operator. Differentiating the actual transfer gives the exact scalar-output density

\[
 h_\delta=\sum_i\{\partial_iF_{\delta;i,*}
                         +(C_i^{el})^tF_{\delta;i,*}\},
 \qquad Q_\delta=r_\delta h_\delta.
 \tag{5.11}
\]

The row transpose contains the surface/Jacobian normalization. On a fixed sphere chart any horizontal connection terms are included in `C_i^el`. This density produces the actual divergence of the output, so it introduces no extra scalar solution.

Equations (5.4)–(5.5) now give an exact construction of a representative:

\[
 \Psi_\delta=
 \begin{pmatrix}
 F_\delta&0\\
 r_\delta^{-1}\mathsf S_{r_\delta}Q_\delta&K_{r_\delta}Q_\delta
 \end{pmatrix}.
 \tag{5.12}
\]

Thus a sufficient and, for its scalar row, sharp target is bounded `chi F_delta`, bounded `chi K_r Q_delta`, and bounded `chi S_r Q_delta/r`. The full displacement density need not be norm-minimizing, so boundedness of this particular `F_delta` is not asserted necessary for every formulation of A*.

Differentiation does not commute with the splitting. With `J=S_r Q`, the exact identities include

\[
 \partial_iJ=(\partial_i\mathsf S_r)Q+\mathsf S_r\partial_iQ,
 \qquad \Lambda J=\mathsf S_r\Lambda Q+[\Lambda,\mathsf S_r]Q,
\]
\[
 r\partial^\alpha(J/r)
       =(\partial-f)^\alpha J.
 \tag{5.13}
\]

The last expression means the ordered products of `partial_i-f_i`; these commute in flat coordinates because `f=d log r`. On tensor bundles retain connection commutators. In (5.11), differentiating `Q` also differentiates `C_i^el`, including its order-one coefficient of size `r^-1`. Thus unweighted bounds for `Q`, or symbol bounds for `S_r`, do not control the right side of (5.13).

On the lower cutoff region (5.8) proves the required cancellation and uniform bounds for an actual representative. On the positive-depth cutoff region the continued kernel, inverse Dirichlet operator and all involved radii have fixed-separation bounds, so the same construction is uniformly controlled there. On the shrinking **unmatched core** no identity proves `S_r Q_delta=O(r)`, nor is `F_delta` uniformly bounded. The corresponding frozen equation is the physical nonnormal model from §4, not an entrywise Laplacian trace. The actual missing analytic quantities are now explicit in (5.11)–(5.13). Replacing the continued flux by the bounded local Poisson evaluation would lose reproduction of the second-medium source solutions, which is precisely the inverse problem.

**Result of Construction D.** The divergence right inverse, trace-kernel projection, sharp quotient norm equivalence and local/cutoff evaluation representative are proved. They are available for arbitrary fixed admissible smooth coefficients at small scales. The two core bounds just identified are unpaid. No actual admissible pair disproving P112 has been found.

## 6. What a paid bound would have to finish

No core estimate A*, (D*) or quotient coercivity is proved, so the following is a **conditional implication**, not a proof of P112. It also makes clear why existence at every positive radius is insufficient.

**T118 (technical conditional continuation).** Suppose at every interior frontier of a physical match the actual flux transfer is available on M's sphere family with one fixed spatial dilation, and has unscaled representatives satisfying I115's A* uniformly in `delta`, reproducing every paired cap-source response. Then the match extends through that frontier. If this hypothesis holds for every such frontier, P112 follows.

**Proof, including normalization and globalization.** On the matched open region, physical coordinates, coefficients and all cap-source responses agree. Their smooth differences have zero jets at a contact point. Source value surjectivity there supplies four paired physical responses forming matrices `V1,V2` with `V1(p)=V2(p)` invertible; both remain invertible on a smaller fixed neighborhood. These are actual displacement/divergence frames. Put `B=V2 V1^-1`, independent of `delta`, and `M_delta=integral Psi_delta`. Taylor's formula and bounded first derivatives of the fixed frame give

\[
 V_2=M_\delta V_1+E_\delta,
 \quad |E_\delta(y)|\le C r_\delta(y)\rho_\delta(y),
 \quad \rho_\delta(y)=\|\Psi_\delta(y,\cdot)\|_2.
\]

For any one fixed cap source, the same formula and inversion of `V1` give

\[
 |U_{2,F}-B U_{1,F}|\le C_F r_\delta\rho_\delta.
 \tag{6.1}
\]

On every compact subset of the fixed shrinking core `t<0`, `sup r_delta ->0`, whereas `||chi rho_delta||L2` stays bounded by the assumed **unscaled** A*. The left side is independent of `delta`, so it is zero in `L2`, hence pointwise by smoothness. This holds for every source; no compactness or simultaneous subsequence for an infinite family is used. The frame matrices equal on the known side, so `B=I` there. H115's divergence/symbol/UCP argument now gives `B=I` and coefficient equality on the connected new neighborhood. Equivalently extend the comparison by the identity over the old matched region and apply its original cap-normalized scope. Invertibility near contact follows from continuity, not compactness of `GL(4)`.

For completeness, define the maximal physical matched region as the union of connected open sets containing the cap on which both coefficients and every cap-source response agree in the **same** Euclidean coordinates. Its matches glue by literal equality, so no image escaping or fiber-group compactness issue occurs. Green equality on its square follows from source equality for the source variable in the cap and physical UCP in the other variable off the single pole; removing a point from a connected three-domain is harmless. It supplies the cross used in the local continuation.

If this maximal region has an interior frontier, choose a ball within it tangent to its complement in a fixed interior chart; the contact point can be chosen away from the source ball, which already lies in the match. This is the source's contact geometry with the partner point fixed to the same physical point. The hypothesized bound and the local argument extend the match, contradicting maximality. The enlarged domain is connected, so the match is its whole interior. Smooth continuity gives equality on its closure and hence on the original domain. Boundary components, disconnected measurement patches and inaccessible boundary collars cause no extra step. All sources stay in the one constructed cap. ∎

There is a still stronger, simpler sufficient input: a uniform `L2` bound for the actual displacement density `F_delta`. The flux reproduces the three **physical constant displacements**, since they solve both operators and the transfer agrees with them on the known side. Thus `integral F_delta=I3`. Taylor directly yields `|u2,F-u1,F|<=C_F r_delta ||F_delta||`; the preceding limit gives equality of displacements, and actual divergence follows by differentiating the exact equality. Physical jets and R112 then give coefficients. This is not an available estimate; §4 explains the obstacle to proving it with the scalar angular model. It is recorded to avoid making divergence recovery an asserted necessary condition for every possible successful proof of P112.

The original F115 path remains valid at its stated conditional budget. With a justified **unscaled** bound and a fixed source-jet normalization, the degree-one Taylor coefficients modulo `D^a_{alpha q}-=f_alpha delta_aq`, `Z_{alpha4}+=f_alpha` have a radius-independent finite right inverse. One would need the radius-independent `D,R` with

\[
 \|\chi D/r\|_2\le C,\qquad\|\chi R/r^2\|_2\le C,
\]

and their fixed high smooth bounds before using the interpolation. In dimension three, the source's choices are `d_*=23/2`, `eta=1/23`, `p_*>23`, `m>=45`. They give `D` through order ten of size `r^(1/2)` and `R` through order ten of size `r^(3/2)`. Testing zero lower jets uses `Lcal2 R` through order eight, thus `R` through ten, and gives `E` through eight. F115's order-three ODE state and third prolongation then give `D` through nine of size `r^(3/2)` along the monotone paths. The scalar input column participates in this coupled estimate. One must finally obtain an invertible zeroth-order comparison for **all** physical sources and apply H115, as the direct conditional proof above explicitly does.

These numbers are derivative bookkeeping, not established estimates for the continued density. The source angular coercivity itself retains six trace-operator base derivatives, profile derivatives through seven (within its allowance of eight), five derivatives in its squared-norm commutators, and its two half-order angular strengths. In Construction Q the additional projection/scaling commutators must fit that budget or a newly proved larger finite budget. In Construction D the derivatives in (5.13) and the scalar recovery loss must be paid **before** claiming an `r^2` Taylor remainder in unscaled variables. A bounded scaled density with an uncontrolled lower-left block does not meet that claim.

Physical spatial dilation and sphere shrinkage also remain separate. Under `x=p+epsilon z`, use `u_epsilon=u(p+epsilon z)` and `d_epsilon=epsilon d(p+epsilon z)`. The energy operator rescales by `epsilon^2`; physical Green displacement scales by `epsilon` in dimension three and each actual differentiated tensor factor has its additional derivative scale. Keep these weights when forming the augmented Green kernel. Fix the geometry, profile exponent and amplitude, positive separation/cutoff scales, then one sufficiently small spatial dilation; only then send `delta` to zero. Constants from fixed-separation continuation are allowed to depend on those fixed scales and do not substitute for a `delta`-uniform core bound.

## 7. Boundary route and continuation decision

No new construction here estimates the signed inaccessible collar flux. The naive expanding-Runge route remains parked. Its exact whole-domain budget is still

\[
 |\mathcal I_\Omega(u_1,u_2)|\le\epsilon M_1M_2+
 Cb(\eta_1A_2+\eta_2A_1+\eta_1\eta_2)
 +|\mathcal I_{C_t}(w_1,w_2)|+|\mathcal I_{C_t}(u_1,u_2)|.
\]

It must be combined with the physical cutoff divergence defect, every conjugated support term, both Carleman boundary signs and the amplified `tau^(2-N)` divergence remainder if those tools are used. On arbitrary P112 domains no coefficient factor vanishes on the whole inaccessible collar. No choice of shrinking volume alone pays its signed flux. The exact finite-rank and trace-kernel obstructions above likewise do not prove any signed collar lower bound or refute P112.

The strongest new fully proved assertion is D118's sharp quotient norm criterion, supported by the explicit right inverse (5.1)–(5.3) and the paid local normalization (5.8). Its full scope reduces to the homogeneous physical Dirichlet construction, smooth small-ball inversion, Hilbert graph decomposition and elliptic regularity. The projected equation and Jordan obstruction are also technical. These are not substantial nominations under the complete accepted source-operation standard. T118 is a fully proved **conditional implication**, not constructed uniqueness.

The useful next target is now concrete: either establish coercivity for the nonnormal projected operator with (4.8)–(4.11) and its finite physical normalization, or bound the actual continued displacement density and, if pursuing unscaled augmentation, its precise trace-kernel residual (5.11)–(5.13). Both routes have a paid lower cutoff seed and fixed-radius existence. Neither has a paid shrinking-core bound. P112 remains unproved and unrefuted, and no ninth finding is nominated.

## 8. Evidence contract and limitations

Only this report and the two assigned I118 directories were written. Exact inventory and the final seal bind every owned artifact, including preparation code, the independent finite diagnostics, failed-route record, frozen originals, current primary versions, reading passages and preseal validation. Only the four specified **live** ledgers may drift; their I118 snapshots and inherited snapshots are immutable. The mutable launch record is frozen and not bound as a live dependency.

The verifier first checks the entire owned seal and exact inventory, directly checks I112 and I115 inventories/seals and every immutable reference, and verifies the complete original-corpus Git/SHA/text mapping. It then verifies exact lexical membership/occurrences and all inherited/new passage bindings before running any diagnostics. It does not import an unverified inherited diagnostic or execute either earlier verifier. The I115 supplied-parent bindings and original I112 supplied-parent bindings are retained and checked directly. The original I112 and I115 finite diagnostics run once each only after the complete immutable preflight; I118 independently reconstructs the degree-four minor and checks additional exact rational instances of the polynomial formulas.

Corpus/TeX lexical lines use Python `str.splitlines()`; PDF passage lines use LF splitting and preserve form feeds; joined passage hashes append no newline. Selective PDF replay consists only of Tan–Liu v1 and the newly retrieved Hardy v1, extracting to stdout. The other inherited PDF texts, including the 776 mapped corpus texts, are hash-bound without re-extraction. There is no recursive corpus copy, whole-corpus download or repeated inherited evidence workflow.

Run `python3 -B frontier/experiments/i118_physical_quotient_angular/verify.py`. The sealed verifier is offline and read-only: no network, file writes, bytecode, repair or resealing. Preseal validation precedes a single final seal; the final invocation only reads and reports. Retained failures include oversized/truncated read output and the exact scoped method failures, alongside all inherited retrieval, orchestration and original mathematical failures. Source identity and finite algebra are not universal proof certification, substantiality acceptance, human review or priority certification.

### Primary references

- [E: pinned full-boundary elasticity paper](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026).
- [M: pinned metric/connection one-patch paper](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Determination-of-a-metric-and-a-unitary-connection-from-one-boundary-patch-October-5-2026).
- [C: pinned scalar companion](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Smooth-Anisotropic-Uniqueness-in-the-Calderon-Problem-from-One-Boundary-Patch-September-24-2026).
- [Tan–Liu, exact v1](https://arxiv.org/abs/2211.06650v1), all-order physical boundary symbols; no analytic continuation assumption used here.
- [Barceló–Pérez-Esteva–Marmolejo-Olea–Vilela, exact v1](https://arxiv.org/abs/2510.10798v1), constant-coefficient ball Poisson construction; no cross-medium bound imported.
