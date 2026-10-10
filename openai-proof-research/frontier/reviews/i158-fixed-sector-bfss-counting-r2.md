# I158 — Independent original-proof review of S155

**Complete requested gate: UNRESOLVED.** The independent mathematical check below supports **PASS without substantive repairs for the fixed-sector counting deduction in original §§3.1–3.7**, relative to the stipulated BFSS operations and the ordinary FNT weighted Poincaré theorem. This is a separated, narrower verdict. It is **not** a completed review of every recursively required historical original and comparator. The outstanding reading obligations in §10 prevent a blanket original-submission PASS. No assertion is repaired and then relabelled originally correct. No mathematical counterexample to S155 was found. No finding is accepted: eight accepted, two remaining, with a separate contribution gate still required.

Original I155 task: `frontier/iterations/iteration155-fixed-sector-bfss-counting-task.json`, SHA-256 `e32170f6d05bfcfea861e801830655650dfe8fb3813b893243bf3428dda775e1`. Original report: `frontier/iterations/i155-fixed-sector-bfss-counting.md`, SHA-256 `c6e05a0853e3232f86c8a8049cb9ecb373c9358ca58bfc1cb42c6e81d4b15f44`. The original report and finalized parent response were supplied in full in the task conversation. The report is not modified. Parent selected checks, inherited integrity results, and finite diagnostics are not this proof.

All OpenAI theorems **and lower operations** at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` remain stipulated. No truth audit, contradiction synthesis, or ex-falso reasoning is used. Only the three assigned I158 paths are authored. No children, shared edits, staging, commits, publication, or dependencies on I156/I157 are used.

## 1. Separated verdicts and inherited entrances

- **S155 §3.1:** PASS at the fixed source-constructed confined physical-type scope, including the explicit allowed type and its nonzero fiber. Constants are allowed to depend on that type.
- **§3.2:** PASS for the orbit, full stabilizer, Hom convention, finite-component projector, Jacobian, angular form, retained fermion matrix, and multiplicities. The representation and normalizations are derived below.
- **§3.3:** PASS for the inherited-core prescription and the matching statements as actually qualified there. The even/odd conditions are necessary restrictions of the full equivariant-slice condition, not a sufficient replacement for it. The references to simultaneous SO(2)/SO(3) rotations denote their vector images; the actual groups are their preimages in Spin(9) × SO(3). Reading them as unqualified direct products would be wrong, but the original explicitly retains the lifts and does not make that direct-product assertion.
- **§§3.4–3.6:** PASS for the physical-domain bound, localization, weighted mean comparison, horn and collar bounds, and local-to-global Weyl argument. Details below pay these claims without changing the physical realization.
- **§3.7:** PASS for convergence, positivity, phase integral, and all factors. In particular, full isotypic counting contributes `d_lambda m_lambda`.
- **Complete recursive original-review/evidence reading and full fresh comparator review:** UNRESOLVED in this review. The evidence package records incomplete coverage rather than importing ancestor reading as this review's own reading.
- **Contribution/acceptance:** not decided. The proof uses familiar reduction, localization, Poincaré, and Weyl methods. Its contribution may be technical; correctness alone cannot add a ninth finding.

The I153/I155 entrances retain their original distinctions. F150 is the fixed-beta consequence of the published finite-free triangular crossing theorem, not a moving-beta statement. The finite A150/MA, B150/V and K/K2 implications retain their conditional/model scopes. The exact triangular critical fixed-time stability premise remains unpaid. Treating its repetition in a task as a new user axiom remains **FAIL as external provenance**. The unconditional endpoint-window obstruction remains unresolved. Square-lattice spin or FK-bond statements do not supply the missing triangular-spin transfer.

For example, the finite resolvent identity is `K(g)=<g,A(1+A)^(-1)g>`, with minimizer `(1+A)^(-1)g`; `K=(1/2) integral exp(-t)NS_t dt`. Density and flip-rate comparison give `K_beta <= exp((2e_L+12)Delta) K_critical`, `e_L=48L^2+8L`. The exponent is at most `124 A0` on `Delta<=A0 L^-2`, including L=1. These finite statements do not establish critical stability. The color-fiber Fourier quantity includes its conditional mean: `T>=1-E Var(g|eta)>=1-2K(g)`. Unconditional balance does not remove that zero mode.

The C153 entrance is exactly source Proposition 3.4 on the projected closed supercharge form: `q>=||grad psi||^2/4+c_m integral r|psi|^2`. Source Lemma 2.2 supplies a projected smooth physical core, and Lemma 4.2 supplies actual constructed types. The source was read through its final theorem proof and references in this review. No pointwise coercivity is inferred. Q153's ambient upper comparison has the correct direction; its radial lower trial construction uses `r^-13`, with radial coefficient `13*12=156` before multiplication by the kinetic factor 1/2. Its individual Agmon identity has cost `9a^2 r/8`, so the threshold is `a<sqrt(8c_m/9)`. None of these estimates supplies a growing-channel-mode approximation.

FS153's complex-vector identity is valid by taking the real part of the ground-state weak equation tested against `F^2 psi`. The hard-exclusion `H_0^1` domain is preserved by the bounded symmetric sine/cosine multipliers. Common mixed-state centering is indispensable: the mass is `N S(k)`, the first moment is `N|k|^2`, and ground-space mass at zero is retained. A first moment cannot identify the mass. L153's fixed-order limitation remains: estimates with arbitrary constants `C_m` do not justify optimizing m with epsilon.

The historical I153 Bose screen stays incomplete. I155's specified comparison closure is new I155 work, not retroactive completion of I153 and not a proof of B153. I read the I155 operative notes, including their later completion entries; their top-level `status` still says partial, so that field alone is not a completion certificate. I have not freshly read all 54 Bose files and their thermal difference construction in I158. B153 remains parked; no covariance theorem is inferred from one-body information, local count bounds, Palm likelihoods, or an inherited reading receipt.

Inherited literal failures are not changed: I129's endpoint-only chi=2 claim is distinct from the corrected range; I114's unrestricted differentiability/inverse/stationarity and weighted-Q/ordinary-R claims remain failed; Cuesta's scalar factor, JTVW's squared-norm lemma, and the same-uniform flip-coupling monotonicity claim retain their failures. The unsquared norm estimate and common-resampling coupling are separate corrections. No parked unrelated target is reopened.

## 2. Actual representation, orbit, and invariant fiber

Let `W=R^16 tensor R^3`, with real Spin(9) spin representation on the first factor and the adjoint SO(3) representation on the second. Its dimension is 48. The unique complex irreducible Clifford module has dimension `2^24`. The simply connected Spin(9) and SU(2) actions lift to Spin(48); their lifts commute, since their commutator acts scalarly on the Clifford module and a connected semisimple group has no nontrivial continuous character.

The nontrivial loop in SO(3) rotates a real color plane once. On W it rotates sixteen mutually orthogonal real planes once. Its Spin(48) lift ends at `(-1)^16=1`. Thus the gauge representation on F really descends to SO(3), rather than merely acting projectively. Using gauge SU(2) yields the same invariants.

There is also an explicit joint character formula. For Spin(9) torus angles `theta=(theta_1,...,theta_4)` and gauge rotation angle phi, take the eight spinor weights `w=(1/2,epsilon_2/2,epsilon_3/2,epsilon_4/2)` and color weights `c=-1,0,1`. The twenty-four real-plane angles in W are `w.theta+c phi`. Therefore, with continuous spin lifts,

`chi_F(theta,phi)= product_(w_1=1/2, c=-1,0,1) [exp(i(w.theta+c phi)/2)+exp(-i(w.theta+c phi)/2)]`.

This follows by diagonalizing each Clifford two-plane into its two occupation states; it is an exact character formula, not a dimensional surrogate for the gauge projection. It also checks the gauge 2pi periodicity. Its angles must retain the Spin(9) lift, rather than being reduced modulo SO(9) periods.

For the first Cartan generator each of those twenty-four planes has speed 1/2. The spin-module weights contributed by each plane are ±1/4. Consequently the maximum first weight is 6 and its eigenspace is one-dimensional. On that line the other coordinates are `3*(1/2)*sum_(w_1=1/2) w_j=0`. Roots which increase the first coordinate kill the line. Roots of zero first coordinate belong to the semisimple Spin(7) centralizer; its character on a one-dimensional invariant space is trivial. Thus the line is highest of weight `(6,0,0,0)`. Gauge SU(2) commutes with this Cartan generator, preserves its unique top line, and acts there trivially. This proves uniqueness and gauge invariance simultaneously. Every first weight of F for the source Spin(8) stabilizer is at most 6, so `M=6` is valid.

The global Spin(9) central element acts on F as fermionic parity relative to this top state: if n occupation signs are reversed, the first weight is `6-n/2`, and a 2pi rotation has eigenvalue `(-1)^n`. Thus central invariance of a Hom vector is a real constraint, even though the bosonic matrix sees only SO(9).

For `X in Mat_(9,3)(R)`, the action is `(a,R)X=A X R^t`. Every distinct-positive singular-value orbit has a representative `D_s`, `s1>s2>s3>0`. Ordinary SVD can be made special orthogonal on both sides: adjust a right-frame orientation with a matching image-axis sign, and correct a left-frame orientation in the six-dimensional perpendicular space. Hence the chamber misses no open component and carries no additional orientation copy.

If `(A,R)` fixes D_s, then R commutes with `D_s^t D_s`. Distinct eigenvalues force `R=D=diag(epsilon_i)`, with product epsilon_i=1. Then A is `diag(D,Q)`, Q in SO(6). Conversely every such pair fixes D_s. Taking the preimage in Spin(9) gives precisely the original K. The preimage of SO(6) is connected Spin(6), and `K/K^0` has four elements.

Put `Hlambda=Hom(V_lambda,F)` with unitary action `rho(a,R)T=R_F(a,R)T pi_lambda(a)^(-1)`. Evaluation of an intertwiner `V_lambda -> physical functions` has exactly this transformation law, so the correct fiber is

`E_lambda=Hlambda^K=(V_lambda^* tensor F)^K`.

The convention is not `V_lambda tensor F` chosen without checking the pullback. Let `E0=Hlambda^Spin(6)`. Representatives of two sign components can be taken as left Clifford lifts `e1 e2` and `e1 e3`, paired with their right diagonal sign rotations. Their squares and commutators lie in Spin(6), including the global central element. On E0 those elements act trivially. Thus the induced operators on E0 are commuting involutions forming the Klein four group. Their average is the orthogonal projection onto E_lambda. This proves both original formulas:

`m_lambda=(1/4) sum_D Tr(A_D|E0)=integral_K conjugate(chi_lambda(a)) chi_F(a,R) dk`.

The Spin(6) center is larger than its order-two subgroup: its volume element has order four and square equal to the global Spin(9) central element. The E0 intertwining condition includes its action too. One cannot replace E0 by an invariant space for SO(6), or retain just the parity test. No such replacement occurs in S155. The character formula above, restriction to Spin(6), and the four-component projector specify an exact finite multiplicity; a gigantic decimal evaluation of it is not necessary for the stated theorem.

The norm budget is also literal. Clifford normalization gives `||theta||=1/sqrt(2)`. For a real orthogonal 16 by 16 gamma matrix, entrywise absolute sum is at most `sqrt(256)*sqrt(16)=64`. For each spatial/color coordinate there are two nonzero epsilon pairs, each with coefficient magnitude `2sqrt(2)` and Clifford-product norm at most 1/2. Hence

`||B(X)|| <=128sqrt(2) sum_(i,a)|x_i^a| <=384sqrt(6)|X| <1024|X|`.

With C=1024, m=3072 gives `c_m=(3072+9)/3-1024=3`. The source highest polynomial times the gauge-fixed vector above, with k=1540, has weight `(3086,3080,0,0)` and `3080>3072+6`. At columns `s1 e1,s2 e3,s3 e5`, its polynomial is `(s1^2 s2^2)^k`, nonzero for every regular s. The irreducible representation generated by a nonzero highest vector of this weight has nonzero evaluation there. Evaluation intertwines the stabilizer; transport to D_s therefore gives a nonzero element of E_lambda. This proves `m_lambda>=1` for the specified type. Multiplication by arbitrary radial compact cutoffs also gives infinitely many physical vectors, as in the stipulated source.

## 3. Reduction, signs, unitary normalization

For T(s) in E_lambda define

`I_T(w)(gD_s)=R_F(g) T(s) pi_lambda(g_left)^(-1) w`.

Replacing g by gk leaves this unchanged exactly because T is K-fixed. Gauge invariance follows on putting the extra group element in the right factor. Left pullback with its fermion action sends `I_T(w)` to `I_T(pi_lambda(a)w)`. This verifies the representation convention directly.

Use probability Haar measure on the orbit. Schur averaging of `T^*S` over the left group gives `Tr(T^*S)/d_lambda` times the identity. Thus the orbit integral of the inner product of `I_T(w)` and `I_S(v)` is the Hilbert--Schmidt pairing of T,S times `<w,v>/d_lambda`. The geometric integration formula has one constant c multiplying `J ds` and the probability orbit measure. Multiplying I by `sqrt(d_lambda/c)` makes the identification

`physical lambda-isotypic space = V_lambda tensor L^2(C,J ds;E_lambda)`

unitary. The constant is independent of s. This explains both why the fiber rank is m_lambda and why the count has an additional d_lambda, without an extra orbit-volume or finite-stabilizer factor.

There are eighteen rotations between an image axis i and one of the six perpendicular axes. Each tangent has length s_i. For an image pair i<j the left/right tangent coordinates (a,b) have Gram matrix

`G_ij=[[s_i^2+s_j^2,-2s_i s_j],[-2s_i s_j,s_i^2+s_j^2]]`.

Its eigenvectors `(1,1)/sqrt(2)` and `(1,-1)/sqrt(2)` have eigenvalues `(s_i-s_j)^2` and `(s_i+s_j)^2`. Its determinant is `(s_i^2-s_j^2)^2`. Radial directions are orthonormal and orthogonal to the orbit. Taking the positive square root of the determinant on the ordered chamber gives exactly

`J=(s1 s2 s3)^6 product_(i<j)(s_i^2-s_j^2)`.

The eighteen and six angular directions have total dimension 24; with three radial directions this is the ambient dimension 27. This calculation derives the measure rather than inferring it just from dimension.

Differentiating I along a left rotation gives `L_ij T=dR_F(e_ij)T-T dpi_lambda(e_ij)`. Differentiating along a right rotation gives `R_ij T=dR_F(right e_ij)T`: the right action on X is already by the transpose, so inserting another minus sign here would be wrong. Applying the inverse Gram matrix yields

`A_s[T]=sum_(i<=3,alpha>=4) s_i^-2 ||L_alpha,i T||^2`

`+ (1/2)sum_(i<j<=3) [||(L_ij+R_ij)T||^2/(s_i-s_j)^2 + ||(L_ij-R_ij)T||^2/(s_i+s_j)^2]`.

Individual generators take values in the larger Hom space; they need not preserve E_lambda. The summed invariant quadratic expression restricts to a nonnegative Hermitian form on E_lambda. The small denominator belongs to the simultaneous left/right generator L+R, in agreement with the vanishing tangent at a collision.

The original compact-regular form is therefore exactly

`integral J [ (1/2)|partial T|^2+(1/2)A_s[T]+V|T|^2+<T,B(D_s)T>] ds`.

The ambient invariant B is retained by postcomposition and maps E_lambda to itself. The source gives `B(D_s)=2i sum f_abc s_a gamma^a_(alpha beta) theta_alpha^b theta_beta^c`, with spatial axes 1,2,3 at this diagonal representative. The quartic potential is the sum of the three pair products, with coefficient one. Radial integration by parts yields `-(1/(2J)) sum partial_i J partial_i`. All kinetic terms carry the stipulated coefficient 1/2.

For reference, on a regular region the map `T -> J^(1/2)T` changes the radial expression into

`-(1/2)Delta + (1/4)Delta log J+(1/8)|grad log J|^2`.

The last scalar potential may have either sign. Keeping it bounded on a fixed compact regular domain is sufficient; no global sign is assumed.

## 4. Physical core, all stabilizers, and matching

A smooth E_lambda-valued section with compact support in the open chamber lifts by I. The regular set is smoothly `C times G/K`: the simple eigenprojections of X^t X give local smooth singular frames, and their ambiguities are precisely K. The formula therefore defines a smooth physical isotypic function. Its support is compact since the group is compact and the singular values range over a compact set. That support has positive distance from every singular stratum. Extending by zero is smooth on all R^27. This proves the claim for **every** compact regular section and every w, not just for the source polynomial. It supplies m_lambda independent radial components and all d_lambda representation vectors for the lower trial spaces.

The physical reduced domain is the image of the closure of the projected ambient smooth core. It is not characterized by imposing scalar wall traces. The exact general stabilizer describes all intersections as follows. For positive singular-value blocks of sizes k_j, let r=sum k_j. In vector images the stabilizer consists of

`(diag(O_1,...,O_l,Q), diag(O_1,...,O_l,P))`,

where `O_j in O(k_j)`, `Q in O(9-r)`, `P in O(3-r)`, and

`(product det O_j) det Q=(product det O_j) det P=1`.

Use the Spin(9) preimage. A zero-dimensional orthogonal block has determinant one. This includes all finite components and all central lifts at once.

Orthogonality to the tangents `A D-D B` imposes symmetry of both `Y D^t` and `D^t Y`. It forces off-block entries between distinct positive singular values and between positive and null blocks to vanish. Within an equal-positive block the normal matrix is symmetric; the null block is unrestricted. Thus the normal slice representation is

`N_D = direct_sum_j Sym(k_j,R) direct_sum Mat_(9-r,3-r)(R)`.

At a simple positive collision it contains two invariant radial directions and the two-dimensional traceless symmetric splitting plane. At rank two with distinct positive values it is `R^2 plus R^7`; at rank one it is `R plus Mat_(8,2)`; at a triple positive collision it is Sym(3); at the origin it is Mat_(9,3). This also covers a collision combined with rank loss without independent gluing prescriptions.

The connected stabilizers have the stated vector images. At rank two the connected group is Spin(7). At rank one it is Spin(8) × SO(2), the second factor acting on the two null gauge axes. At a simple positive collision, the connected lift is `(Spin(2) times Spin(6))/diagonal{±1}`, paired with the simultaneous right SO(2) rotation. At a triple positive collision it is `(Spin(3) times Spin(6))/diagonal{±1}`, paired with the right SO(3) image. These descriptions make explicit the covers already demanded by the original's stabilizer prescription.

For a slice near a singular orbit, an equivariant smooth map `f:N_D -> Hom(V_lambda,F)` obeys `f(hY)=rho(h)f(Y)`. It extends to the tubular neighborhood `G times_H N_D` by the same equivariant formula. Conversely an ambient smooth intertwining map restricts to such an f. Local invariant partitions of unity join these maps on overlaps. Its Taylor terms necessarily lie in `Hom_H(Sym^j N_D,Hom(V_lambda,F))`. This is a core description; it does not assert pointwise jets for arbitrary closed-form vectors.

For a pair collision a simultaneous quarter-turn in the two image/gauge axes reverses the signed splitting coordinate. Its square belongs to K, hence acts identically on E_lambda. The resulting W is an involution and `T(-u)=W T(u)` implies `W T^(j)(0)=(-1)^j T^(j)(0)`. At rank loss take the left pi rotation reversing the missing image axis and one perpendicular axis, with right identity. It normalizes K, lies in the enlarged stabilizer at the wall, and its square is the global central element in Spin(6). Its action W0 on E_lambda is again an involution; the same differentiated identity follows. A change of lift multiplies by that already trivial central action. These parity conditions alone are not sufficient: the full continuous stabilizer still constrains the Taylor tensors. Original §3.3 explicitly says they are part of the full slice condition, so this is not a false sufficiency assertion requiring repair.

The singular sets have ambient Lebesgue measure zero. They carry no separate L^2 summand in the original physical space. Possible concentration in their neighborhoods is nevertheless a genuine spectral issue; it is controlled by §6, not dismissed by the measure-zero fact.

## 5. Coercivity, closure, and invariant Lipschitz IMS

Let c=c_m>0 and C be the source's fermion bound. On the projected physical core there are two inequalities:

`q>=G/4+c R1`, and `q>=G/2+V1-C R1`,

where `G=||grad psi||^2`, `V1=integral V|psi|^2`, `R1=integral r|psi|^2`. Choose, for example, `epsilon=c/[2(c+C)]`. Their convex combination gives

`q>=a G+epsilon V1+b R1`, `a=(1+epsilon)/4`, `b=(1-epsilon)c-epsilon C=c/2>0`.

This uses only sector inequalities on physical vectors. Apply it to differences of a form-core Cauchy sequence. The gradients, sqrt(V) multiples, and sqrt(r) multiples are all Cauchy in L^2. Closedness of these distributional gradient/multiplication operators identifies their limits. The B-form is continuous on this weighted space since `||B||<=Cr`. Thus both the inequality and the exact expression for q pass to the physical form closure. No integrability of V was presumed before this argument.

For a bounded invariant Lipschitz scalar chi with bounded weak gradient, `Q_alpha(chi psi)=chi Q_alpha psi+[Q_alpha,chi]psi`, where the commutator is Clifford multiplication by its derivative and is bounded by a fixed constant times `||grad chi||_infinity`. To verify membership in the **minimal closed form**, approximate chi on compact sets by convolution with an ambient radial mollifier, which preserves both group invariances and the Lipschitz bound. For a fixed smooth physical core vector, these products converge in H^1 and in both weighted multiplication norms; the exact form identity proves form convergence. Then use a diagonal approximation for a general form vector, and the commutator bound. This establishes domain preservation, not merely membership in a maximal distributional domain.

Ordered singular values are globally Lipschitz in X. One proof uses the min--max formula for singular values: each changes by at most `||X-Y||_op<=||X-Y||_F`. Thus the invariant cutoffs composed with them are Lipschitz even at crossings. Rademacher derivatives and the weak product rule suffice. Nonsmooth crossing sets introduce no distributional surface term in the first-order form calculation.

For real invariant multipliers with `sum chi_j^2=1`, expansion of the exact form and `sum chi_j grad chi_j=0` gives

`sum q[chi_j psi]=q[psi]+(1/2)integral sum |grad chi_j|^2 |psi|^2`.

The potential terms commute with scalar multipliers, and the identity passes by the preceding approximation. Smooth profiles in `E^-1/4 s` have gradients bounded by `C_(R,delta) E^-1/4`; the IMS error is consequently `C_(R,delta) E^-1/2 ||psi||^2`. Choosing the two cutoffs as cosine and sine of a single bounded Lipschitz angle avoids the derivative singularity that an arbitrary square root could create. These are actual physical sector localizations.

After reduction, dropping the nonnegative angular energy gives the scalar comparison on restrictions of physical vectors:

`q[T]>=integral J [a|partial T|^2+W(s)|T|^2]`, `W=epsilon V+b|s|`.

It is not a newly selected physical Neumann realization.

## 6. Degenerate cells, means, horn endpoint errors, and collars

The relied-on external result is [Ferone–Nitsch–Trombetti, 1207.0680v2, Theorem 1.1](https://arxiv.org/abs/1207.0680v2). I read the actual text through Lemmas 2.1–2.2, the convex slicing Lemma 3.1, and the ending of the theorem proof. It gives the p=2 weighted mean inequality with diameter constant d/pi for Lipschitz test functions on bounded convex sets and nonnegative log-concave weights. Its proof uses one-dimensional log-concave comparison, exponential weights, and convex thin slicing; it is ordinary external evidence, not stipulated by the task. The theorem is used at its stated p=2 scope, not as an assertion of compact resolvent for every degenerate weighted form.

On the chamber, every factor s_i, s_i-s_j, and s_i+s_j is positive affine. Hence `log J=6 sum log s_i+sum_(i<j)(log(s_i-s_j)+log(s_i+s_j))` is concave. Extend J continuously by zero at the relevant walls. Every positive-volume intersection of an open Cartesian cube of side ell with C is convex and has diameter at most sqrt(3)ell. FNT therefore gives

`integral_Q J |u-u_Q|^2 <=(3ell^2/pi^2) integral_Q J |partial u|^2`.

Zero-volume intersections are discarded. For physical smooth core vectors, evaluation at the linear map D_s is smooth on any bounded closed coordinate box. Thus their restrictions are legitimate Lipschitz FNT tests even at a singular wall; no inverse angular frame is needed for this fact. On core differences the bound in §5 gives convergence in the weighted derivative norm on each cell. Weighted means are continuous by Cauchy–Schwarz since `0<integral_Q J<infinity`. Passing to this closure proves the inequality for actual physical form vectors. Real and imaginary components are treated separately, so the number of **complex** constraints is m_lambda, not 2m_lambda.

Choose `ell=kappa E^-1/2`, with `a pi^2/(3 kappa^2)>3`. A cell is eligible when `inf_Q W<=2E`. Impose zero weighted mean in every fiber component on each eligible cell. On eligible cells the gradient then costs more than 3E times the squared norm. On ineligible cells the potential costs at least 2E times the squared norm. Thus any vector in the joint kernel has scalar comparison energy at least 2E times its norm. A subspace all of whose Rayleigh quotients are at most 3E/2 injects into the eligible mean list. Its complex dimension is at most m_lambda times the number of eligible cells. For the full physical isotypic space this is multiplied by d_lambda.

This is a variational codimension statement. It needs no beforehand compact-resolvent assertion for a degenerate Neumann operator. If compact embedding on a bounded union of cells is desired, partition it into finer cells of side eta. Replacement by weighted cell means is finite rank and has L^2(J) error at most `sqrt(3)eta/pi` times the derivative norm. Finite-rank approximation of the embedding proves compactness on the closure being used. This also explains precisely which completion is meant; an unspecified maximal degenerate boundary space need not be invoked.

For a supported form space keep every cube which meets its support, and take W's infimum over the **whole** cell. Both operations enlarge the comparison space. They have the upper-count direction. A support point and an eligibility witness can differ by at most sqrt(3)ell. Eligibility implies `|s|<=2E/b+sqrt(3)ell` throughout the cell. If its first-coordinate interval is `[u,u+ell]`, u>0, the witness satisfies `s2,s3<=sqrt(2E/epsilon)/u`, using `V>=s1^2(s2^2+s3^2)`. Hence there are at most

`C_lambda (1+sqrt(E)/(u ell))^2 <= C_lambda (1+E/u)^2`

eligible transverse cells over that interval. The additive 1 is essential and charges all integer endpoints and transverse widths smaller than ell.

For support in `s1>A=R E^1/4`, retained cells start at `A-ell`; for fixed R>=1 and sufficiently large E, this is at least A/2. They stop by `C_lambda E+O(ell)`. Comparing the decreasing summand to its integral gives

`#cells <= C_lambda { ell^-1 integral_(A/2)^(C_lambda E+O(ell)) (1+E/u)^2 du +(1+2E/A)^2 }`.

The three integral terms are `O(E^3/2)`, `O(E^3/2 log(2+E))`, and `O(E^9/4/R)`. The lower-end correction is `O(1+E^3/2/R^2)`; upper endpoint changes also fit the lower-order bound. If A lies beyond the eligible range, only the harmless endpoint possibility remains, or the count is zero. Constants are independent of R>=1, with the large-E threshold permitted to depend on fixed R. This proves the original horn inequality at its stated order, including narrow channels.

Inside `s1<=R E^1/4`, the boundary consists of `s3=0`, `s1-s2=0`, and `s2-s3=0`. A scaled delta collar of any one is a flat slab of thickness `O(delta E^1/4)` in a box of side `O(R E^1/4)`. Grid enlargement by O(ell) gives

`#cells <= C_R {delta E^9/4+E^3/2+1}`.

There are only three walls. Their intersections and multiple collars are included by union overcounting, without a separate bad estimate at rank one, the triple collision, or the origin. The comparison threshold is independent of their degeneracy. The constants are chosen at fixed R before delta goes to zero.

## 7. Local matrix Weyl law and the physical global comparison

Set `s=E^1/4 t`, `h=E^-3/4`. The scaled measure is `E^27/4 J(t)dt`, so the flat-measure unitary includes `E^27/8 J(t)^1/2`. On any fixed bounded regular polyhedral domain Omega, divide the operator by E. Its expression is

`P_h=-(h^2/2)Delta+V(t)I+h B(D_t)+h^2 C_lambda(t)`.

Here C_lambda is the angular plus Jacobian matrix, bounded with its needed coefficients on that fixed domain. This follows because angular/Jacobian terms are homogeneous of degree -2 and B is linear. It is not a uniform statement as the domain approaches a wall or as lambda grows.

For Dirichlet boundary the domain is H_0^1(Omega;E_lambda). Bounded matrix errors bracket its eigenvalues between scalar operators `-(h^2/2)Delta+V ± C(h+h^2)`, repeated m_lambda times. Partition into fixed small cubes. A constant scalar potential v on a side-L cube has Dirichlet frequencies in positive integer triples, Neumann frequencies in nonnegative integer triples. For either choice, Riemann counting of the lattice ball gives

`h^3 N(1) -> L^3 (2pi)^-3 (4pi/3) [2(1-v)_+]^3/2`.

The coordinate-plane frequency triples are O(h^-2) at fixed L, so boundary conventions do not alter the coefficient. Bound V on each cube by its extrema, take h to zero first, then cube size to zero. For the polyhedral regular domains used here, boundary cubes have total volume tending to zero; alternatively bracket by interior/exterior grid unions in the Dirichlet case. Natural weighted Neumann boundary conditions conjugate to Robin conditions, not literally to flat Neumann conditions. On the fixed regular region the boundary coefficients are bounded; the trace inequality bounds the Robin term by an arbitrarily small fraction of kinetic energy plus O(h^2) mass. It has the same leading law. The global upper argument below can use only the larger **Dirichlet** domain and does not require identifying a physical wall with any Neumann condition.

Continuity of `(1-V)_+^3/2` pays the final Riemann-sum limit, including energy thresholds `1+o(1)`. Restoring d_lambda yields original (3.5):

`N_Omega(E)/E^9/4 -> d_lambda m_lambda (2pi)^-3 (4pi/3)2^3/2 integral_Omega (1-V)_+^3/2 dt`.

For the lower bound, H_0^1 trial vectors on an interior regular domain extend by zero and are limits of the lifted smooth physical sections from §4. All fiber directions and representation vectors are available. Therefore min--max gives the local Dirichlet count as a lower bound for the physical count. Exhaust C by bounded regular polyhedra; monotone convergence of the nonnegative phase integral gives the full liminf.

For the upper bound, fix R and delta, and choose a good cutoff supported in a bounded regular region, equal to one away from slightly wider collars and below the outer cutoff. Its companion bad cutoff is supported only in the union of enlarged collars and the horn. Their scaled Lipschitz bounds are those of §5. Define each supported form space as the closed subspace of the **original physical form domain** with essential support in the corresponding closed support region. These subspaces are closed in the form norm. They inherit compact embedding from source Proposition 3.4, even if their L^2 closures are proper support subspaces.

The map `U psi=(chi_good psi,chi_bad psi)` is an L^2 isometry. For every vector in the original spectral subspace below E,

`(q_good direct_sum q_bad)[U psi] <=(E+C_(R,delta)E^-1/2)||U psi||^2`.

The min--max principle therefore bounds the original spectral dimension by the sum of the supported counts at this shifted threshold. This uses the inequality for every linear combination in the spectral subspace; it is not an estimate on individual eigenfunctions only.

A good supported vector is, after the unitary, in H_0^1 of a slightly larger regular Dirichlet domain: its support has positive distance from that domain's boundary. Enlarging to that full Dirichlet domain has the upper-count direction and gives the local Weyl coefficient. The bad supported space is compared by §6 after localization, so source sector coercivity is applied only to actual physical vectors. The threshold shift is o(E), lies below 3E/2 for sufficiently large E at fixed R,delta, and is absorbed by the 2E/3E margins in the mean argument. Counting the union of bad-support cells merely overcounts overlaps.

Consequently, writing C_phase for the full coefficient,

`limsup_(E->infinity) E^-9/4 N_lambda(E) <= C_phase+C_lambda/R+C_(lambda,R)delta`.

The order is exactly E to infinity first, then delta to zero at **fixed** R, then R to infinity. No uniform bound on C_(lambda,R) as R grows is used. The interior exhaustion supplies the opposite liminf, so the asymptotic follows. Singular strata contribute no omitted Hilbert summand, and their neighborhoods have already been charged in the upper count. No Born–Oppenheimer approximation, sector mixing, full-Hamiltonian compactness, or massless gap is used.

## 8. Analytic phase integral and coefficient

Let `I=integral_C (1-V)_+^3/2 ds`. It is positive since an open set of positive regular s has V<1. On `s1=u>=1`, the condition V<=1 implies `s2^2+s3^2<=u^-2`. The positive-quadrant cross-sectional area is at most `pi/(4u^2)`. Thus the tail of I is O(1/R), and the bounded part has finite volume. This is an analytic convergence argument, independent of numerical quadrature.

Tonelli allows the following nonnegative integrations. In the positive octant integrate s3 first:

`Z_oct=integral exp(-V) ds=(sqrt(pi)/2) integral_(x,y>0) exp(-x^2 y^2)/sqrt(x^2+y^2) dx dy`.

Put `x=r cos theta`, `y=r sin theta`, `0<theta<pi/2`. The Jacobian r cancels the denominator r. The radial integral is

`integral_0^infinity exp[-r^4 cos^2(theta)sin^2(theta)] dr = Gamma(1/4)/[4 sqrt(cos theta sin theta)]`.

The angular integral is `B(1/4,1/4)/2=Gamma(1/4)^2/[2sqrt(pi)]`. Therefore `Z_oct=Gamma(1/4)^3/16`. Permutation symmetry partitions the octant into six chambers up to measure-zero faces, giving `Z_C=Gamma(1/4)^3/96`.

If `A=volume{V<=1} in C`, quartic homogeneity gives `volume{V<=v}=A v^3/4`. Hence `Z_C=A Gamma(7/4)`. Stieltjes integration, or the beta integral against `(3/4)A v^-1/4 dv`, gives

`I=Z_C Gamma(5/2)/Gamma(13/4)=Gamma(1/4)^3 Gamma(5/2)/[96 Gamma(13/4)]`.

Finally, `Gamma(5/2)=3sqrt(pi)/4` and `Gamma(13/4)=(9*5*1/4^3)Gamma(1/4)=45Gamma(1/4)/64`. Multiplying I by `(2pi)^-3(4pi/3)2^3/2` yields

`C_phase=d_lambda m_lambda sqrt(2) Gamma(1/4)^2/[270 pi^3/2]`.

The six chambers have already been accounted for. Neither J, an orbit volume, nor another order-four stabilizer factor is inserted into this flat three-dimensional phase volume. Their effects have entered the unitary and the invariant fiber. The kinetic coefficient contributes 2^3/2. This is full isotypic counting, not a count in a single multiplicity copy.

## 9. Corrections, objections, and contribution boundary

**No substantive correction of original §§3.1–3.7 is proposed by the mathematical check above.** The explicit slice formulas, norm factor, core approximation, supported-space definition, and endpoint-cell inequalities expand arguments already present in S155; they do not change its hypotheses, domain, fiber, or leading law. In particular, no new physical wall realization or uniform-in-lambda assumption was introduced.

Two readings which would be false are expressly rejected: parity alone is not the wall domain; natural weighted Neumann conditions do not conjugate literally into flat Neumann conditions. S155 does not assert the first, and its good-space upper proof can use its stated slightly larger regular Dirichlet domain. The local bracketing expansion above keeps the second distinction explicit. These are interpretation checks, not silent repairs of a claimed scalar physical boundary condition.

The unresolved objections to the **complete gate** are evidence/coverage objections in §10. They are not a claim that the mathematical Weyl law is false. Conversely the narrower proof check does not certify that every inherited report or every primary comparison has been independently reviewed.

FNT is the only external theorem needed for the singular-cell proof, and its operative proof was read in this review. [Danielsson–Ferretti–Sundborg, hep-th/9603081v2](https://arxiv.org/abs/hep-th/9603081v2), §§3.3–5 and ending were also read: the retained gauge charge combines fast bosonic and fermionic counts, the slow cone gives its radial centrifugal term, and its validity condition is an adiabatic separation away from the origin. That does not provide an all-mode fixed-Spin(9) counting remainder. Their result is not being dismissed just because its title differs.

The original I155 comparisons with Halpern–Schwartz's singular-value measure and connections, Luescher/Simon's scalar confinement and nonclassical asymptotics, Arefeva's smaller SU(2) × SO(2) model, and compact-support equivariant Weyl laws are retained as **inherited comparisons**. Their primary files and exact bindings are frozen, not re-extracted. Apart from the reading explicitly recorded here, I do not claim a full fresh operative review of those papers. The current FNT page identifies v2; the Halpern–Schwartz page identifies v1. Metadata does not certify either proof. The concrete overlap already acknowledged by I155 remains for the later contribution gate. There is no worldwide-priority claim.

## 10. Evidence, exact limits, and replay

The evidence package retains thirteen raw recursive task identities, all ordered field/line occurrences from the inherited decoding convention plus the new I155 task, scalar occurrences, and a supplemental decoder for embedded nonterminal JSON blocks. Extraction of these fields is not their semantic reading. The complete I155 task itself was read via its new and reused string views and scalar view. Its I153 report and finalized response were thus read; the whole recursively required historical corpus of original reports was **not** read to completion in this I158 review. The base 798,775-character inherited reading view has only the ranges in `coverage.json`; failed oversized displays are preserved. This is an explicit unmet requirement, not an assertion that the parent or a hash check performed that reading for this reviewer.

Fresh complete operative reading includes the stipulated positive-eigenvalue BFSS source and FNT. DFS reading runs from §3.3 through the actual ending. The I155 Bose operative notes were read, but the 54-source Bose closure and thermal equal-run/change reconstruction have not all been independently reread. Other primary comparison readings remain inherited. `coverage.json` and `pending-obligations.json` distinguish these scopes. A complete requested original-proof gate remains unresolved until these obligations are discharged.

The replay uses the existing complete map: 13,223 tree entries, 749 manuscript roots, 10,373 original positions, including all 776 PDF/text bindings. Each replay has one flat original-map traversal with cached path digests, not recursive ancestor executions. All fifteen inherited packages are checked as immutable bytes and exact inventories. No ancestor verifier, diagnostic, converter, or numerical experiment executes. No corpus is copied. The four live ledgers may drift; their reused immutable snapshots remain checked. No I156/I157 path is bound.

Own semantic receipts contain exact UTF-8 character ranges, passage endings and hashes, raw LF and splitlines counts, and separate truncated statuses. Lexical occurrence lists retain exact repeated matches and positions. Search coverage is not semantic reading. The supplied-in-conversation original I155 report and parent response are explicitly identified separately from tool-display receipts. Current primary metadata and failed/truncated attempts are retained.

The owned inventory is canonically sorted. Read-only prevalidation precedes one seal. The offline read-only verifier checks all immutable owned/reference/corpus bytes before any new finite diagnostics. It denies writes, network, subprocesses, bytecode, repair, and resealing. The new diagnostics check finite arithmetic only; they do not prove any domain statement, representation classification, Poincaré theorem, Weyl limit, or contribution claim.

Run from the research root:

```sh
python3 -B frontier/experiments/i158_fixed_sector_bfss_counting_r2/verify.py
```

An integrity PASS must be read together with `complete_requested_review: false`. It cannot upgrade the complete gate from UNRESOLVED. The original S155 bytes and the accepted count are unchanged.
