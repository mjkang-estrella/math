# I51 — independent operation-level significance review of H49

**Verdict: SUBSTANTIAL, conditional on I50 approving the original H49 proof.** This is a significance verdict, not an original-proof PASS. No I50 draft or task status was read. I found neither an exact duplicate nor a noncircular reduction of the unrestricted higher-dimensional claim to the checked antecedent operations. The reason is the finite-error bridge from the accepted tensor construction to one global compatible product and both original endpoints, uniformly over nonsmooth convex bodies. A finite exponent by itself would not justify this verdict.

The attribution boundary is essential. The retained tensor squares, positive regularizer, hard moment compactness, signed contact measure, and qualitative common-block equality mechanism are strong antecedents in Liu–Sun–Xiong (LSX), not discoveries of H49. John normalization, hard-target Hessian control, Poincaré estimates, eigenvalue grouping, BV smoothing, convex-hull reconstruction, surface-area continuity, and anisotropic perimeter stability also have established antecedents. What is substantive here, if I50 validates it, is making these operations compatible at nonzero defect without an exact common normal support, reflection group, generating measure, or facet-mass floor. The global and two-endpoint interfaces below cannot be deleted from the comparison.

## 1. Claim and premise boundary

For every integer $n\ge3$, every fixed $0<r<R$, and every $0<\tau_0<1/2$, H49 claims a constant $c(n,r,R,\tau_0)>0$ such that every origin-symmetric pair $rB\subset K,L\subset RB$ and every $\lambda\in[\tau_0,1-\tau_0]$ satisfies

\[
\log|\mathcal W[h_K^{1-\lambda}h_L^\lambda]|
 -(1-\lambda)\log|K|-\lambda\log|L|
 \ge c(n,r,R,\tau_0)d_{\mathcal E}(K,L)^{\alpha_n}.
\]

Here $\mathcal E$ is the entire class of pairs $K'=\sum_iD_i, L'=\sum_ic_iD_i$, with origin-symmetric factors in common nonzero complementary subspaces and $c_i>0$. One block and oblique subspaces are allowed. The distance is the infimum of the maximum of the two Hausdorff errors. Comparison bodies need not satisfy the original ball bounds. There is no uniform smoothness, number of facets, minimum facet mass, reflection, or block-angle assumption. The claimed exponent is

\[
\alpha_n=64n(n+2)(a_n+b_n+1)/b_n,
\]

using the dimension-only constants defined in I49 §5.2a. Its size and lack of sharpness are not the contribution.

All statements **and proof operations** at `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are accepted premises. I read the actual logarithmic manuscript's introduction, reduction, moment, identities, density, tensor and variance files, and its measure-transfer companion file. The complete preprints tree and all ignored corpus files are inventoried and hash checked; this is not a claim to have read every manuscript. Searches cover the full corpus, with line-multiset replay preserving duplicates.

The full I49, I46 and I47 reports, I48 contribution disposition, and relevant I44/I45 moment and flux arguments were read and frozen. I45's symmetric equality specialization remains fully attributed to **Yude Liu, Qiang Sun and Ge Xiong, *The centered logarithmic Brunn–Minkowski inequality*, arXiv:2610.10152v2**. That external paper is a proposed proof, not an assumed theorem; the nonsymmetric centered result is not a premise here. I45 checks the symmetric specialization separately. H49's quantitative endpoint is not inferred from qualitative equality alone.

The planar P10 disposition is unchanged: its independent proof approval and TECHNICAL ONLY significance disposition remain separate historical inputs. I have not reopened its proof, improved its exponent, or transferred its planar graph reduction to higher dimensions. The Neumann and interval diagnostics in I49 are scoped method limitations, not counterexamples to H49. This report makes no acceptance, count, score, or worldwide priority certification.

## 2. Strongest antecedents, read at proof level

### 2.1 LSX and the pinned tensor operations

The freshly retrieved [LSX v2](https://arxiv.org/abs/2610.10152v2), revised 8 October 2026, is the strongest direct antecedent. I read Lemma 3.4 and its proof, equations (3.10)–(3.16) with their derivation, and §3.3's contact and direct-summand argument. The current official abstract record and explicit PDF agree on v2.

Its proof does retain the square involving $D_zW-P\tau$, derivative energy in $P$, and the regularizer term. It does not merely assert concavity and then invoke an abstract equality theorem. At exact equality its limits make $P$ constant and $W=A\nabla\varphi$; symmetry gives a symmetrizable constant matrix, and the commutator forces splitting. Positive slab contact measures preserve boundary information. Exact affinity also identifies the relevant endpoint and intermediate normal supports, which then turns block information into both bodies. These are actual operations available for comparison, not a qualitative black box.

The distinction is not “LSX qualitative, H49 quantitative” as a slogan. In LSX the vanishing squares and exact contact identifications remove error terms before normal and endpoint reconstruction. In H49 those identifications are unavailable: the squares are only small, the limiting fields retain nonzero energy, normals may jump, and endpoint contact information lives initially on an intermediate surface measure. Quantifying the already retained squares is a natural and largely standard first step. Paying all the subsequent interfaces is the substantive issue.

There is also a specific compactness interface. LSX Lemma 3.4 is stated for the relevant linear-tilt hard targets. H49 uses a fixed positive quadratic regularizer while the slab/net parameters exhaust. It supplies that compactness separately through the compact-target moment equation, source-density convergence, and interior sections. It does not simply substitute a Gaussian tilt into the LSX lemma without checking its hypotheses.

### 2.2 Existing moment regularity and quantitative stability

[Berman–Berndtsson, Theorem 1.1 and §2.12](https://afst.centre-mersenne.org/item/10.5802/afst.1386.pdf) supplies a smooth entire moment potential for the compact convex target and positive smooth target density under the barycenter condition; the target boundary need not be smooth. The proof's interior regularity and full gradient-image statement are the relevant operations. [Bonnet–Rubinstein v1, Theorem 1.3 and its proof in §3.5](https://arxiv.org/abs/2604.09914v1) supplies quantitative source-density continuity from target (W_1) distance with nondegeneracy parameters. Its proof truncates an exponential tail and balances the core with a logarithmic radius. [Cule–Samworth, Proposition 2 and its proof](https://arxiv.org/abs/0908.4400), gives the local uniform log-concave density convergence needed to fix domains. [Figalli–Jhaveri–Mooney, Theorem 1.1 and §2](https://people.math.ethz.ch/~afigalli/papers-pdf/Nonlinear-Bounds-in-Holder-Spaces-for-the-Monge-Ampere-Equation.pdf) gives the interior section estimates, with dependence on the actual strict-convexity and right-hand-side data.

These results make the fixed-regularizer compactness step credible as an operation-level extension. They do not produce tensor-compatible fields from a small Wulff deficit or control endpoint normals. H49 uses the initial local convergence only to construct the hard fields. It obtains the later power rate from fresh hard estimates, so an unspecified convergence rate at this existence stage does not by itself destroy the final power.

[Klartag, *Logarithmically-concave moment measures I*](https://www.math.tau.ac.il/~klartagb/papers/lc_moment.pdf), Theorem 1.1 and its proof, gives the bounded-target Hessian cap used here. Its proof removes the smooth-target approximation; it is not a radius-only bound for every unbounded soft target. H49's cap and determinant/coercivity bounds are used after taking the hard limit. John normalization is needed to make the exponents in core and tail estimates dimensional. Calling an arbitrary soft ellipticity constant “effective” would not pay this requirement.

An additional fresh search found **Machado–Ramos**, [*Quantitative stability for the Brascamp–Lieb inequality and moment measures*, arXiv:2511.22636v3](https://arxiv.org/abs/2511.22636v3), revised 29 July 2026. This is stronger than merely qualitative moment continuity. I read Theorems 1.1–1.3, the full main inequality proof of Theorem 3.2 including its approximation lemmas, and Theorem 4.1's proof. Their dimension-only bound controls the $L^1$ distance of a scalar test function to $a\cdot\nabla\varphi+b$ by the square root of its Brascamp–Lieb deficit. Their moment variational theorem controls distance to a fixed moment-measure optimizer from its variational energy gap. The proof uses sharp Prékopa–Leindler stability, linearization, control of the translation parameters, and quadratic regularization; the uniform result is not restricted to a fixed strong-convexity constant.

I grant this strong interface in the comparison rather than dismissing it for nonsmoothness. It can simplify scalar almost-affinity estimates once the appropriate finite scalar deficit is supplied. H49 starts with a Wulff deficit and a boundary score whose hard moment Dirichlet energy can diverge. The checked proof does not identify that score with an admissible finite-deficit scalar test, does not make the matrix rows tensor-compatible, and does not construct a product or compare two original endpoints. Its moment energy gap is not automatically bounded by H49's deficit. Even granting all its stated estimates, these missing interfaces remain. No claim about the correctness of every unrelated formula in that external preprint is needed for this exclusion.

### 2.3 Quantitative logBM with reflections, and cone-volume products

**Böröczky–De**, [arXiv:2101.02549v6](https://arxiv.org/abs/2101.02549v6), current v6 revised 29 June 2024, is a genuine higher-dimensional quantitative logBM result. Theorem 1.4 gives common-factor approximation with exponent $1/(95n)$ under $n$ common independent linear hyperplane reflections. I read Theorem 3.3's log-coordinate Prékopa–Leindler proof, Proposition 4.1's spectral grouping and cap argument, and the reflection-to-unconditional reduction in §8.

This is a substantial antecedent for H49's **operations**, not just a theorem with an inconvenient title. The diagonal alignment, grouping of nearly equal dilation factors, product of coordinate sections, and support-excess cap contradiction are already there. In §8 a reflection group's chambers generate an unconditional model and provide the needed coordinatewise inclusion. Arbitrary origin symmetry supplies neither that chamber decomposition nor that inclusion. H49's symmetric matrix and spectral clustering are standard analogues; its transverse moment-gradient reconstruction must supply the missing global product without assuming unconditionality. Borrowing the grouping operation is legitimate; borrowing its geometric hypotheses without payment is not.

**Böröczky–Henk**, [*Cone-volume measure and stability*](https://users.renyi.hu/~carlos/cone-volume-stability.pdf), Theorem 1.1, assumes almost maximal cone-volume mass on an **exact** proper subspace and gives a volume-distance power $1/5$ (homothetic-distance power $1/(5n)$). Its proof is quantitatively strong: the divergence identity makes the fiber-volume function nearly flat on most of the projection; Lemmas 5.1–5.2 quantify that; Proposition 4.3 combines quantitative Minkowski stability of fibers with an affine centroid graph to construct a complementary product. I read those proofs, not only the theorem statement.

This is a viable alternative reconstruction mechanism if its input can be proved. A near-block neighborhood of normal directions is not its exact-subspace hypothesis. Smooth approximations to a product may put zero surface or cone-volume mass on every fixed proper subspace while remaining close to the product. Conversely, applying it after one has constructed a nearby exact product does not prove that construction. H49 cannot be demoted by composing “near subspace” with this theorem while omitting the conversion. Nor does its one-body product conclusion automatically synchronize both original endpoints.

### 2.4 BV, surface measures, and the classical endpoint theorem

The normal-map part is not a new general BV theorem. For a ball-bounded convex gauge, the positive spherical Hessian measure controls its gradient variation; normalization gives a BV radial normal map. Smoothing a bounded BV residual and balancing a dual-Lipschitz error with smoothing error is an established interpolation operation. **Chazal–Cohen-Steiner–Mérigot**, [*Boundary measures for geometric inference*](https://geometrica.saclay.inria.fr/team/Fred.Chazal/papers/JFOCMboundaryMeasure.pdf), Theorem 3.5 and its proof, proves quantitative $L^1$ stability of gradients of locally convex functions via a one-dimensional estimate and integral geometry; Theorem 3.7 passes to BV-weighted projection measures. I read both proofs. These are stronger precedents than just an unquantified statement that normals are stable.

**Hug–Schneider**, [*Hölder continuity for support measures of convex bodies*](https://home.mathematik.uni-freiburg.de/rschnei/ArchivHugSchneider.pdf), Theorem 1.1, (1.2), and the proof, supplies $d_{BL}(S_C,S_D)\le C(R)d_H(C,D)^{1/2}$ for arbitrary convex bodies. Its parallel-set projection estimates and coefficient extraction already handle nonsmooth boundaries. It assumes geometric closeness of two bodies; it does not turn a small signed position-test residual into an absolute normal residual, nor produce the comparison product in the first place.

**Figalli–Maggi–Pratelli (FMP)**, [*A mass transportation approach to quantitative isoperimetric inequalities*](https://people.math.ethz.ch/~afigalli/papers-pdf/A-mass-transportation-approach-to-quantitative-isoperimetric-inequalities.pdf), Theorem 1.1, supplies the square-root asymmetry estimate for arbitrary convex Wulff anisotropy and finite-perimeter sets. I checked the theorem's normalization and both steps of its main proof, including John's affine normalization removing shape dependence. It is fully strong enough for H49's endpoint application once the correct anisotropic perimeter and volume errors have been obtained. The application itself, removal of translation for even convex bodies, and cap conversion to Hausdorff distance are technical consequences. Obtaining that input for **each** original endpoint from an intermediate contact measure is the unpaid part in a purported routine reduction.

### 2.5 Current nearby results and restricted equality mechanisms

**Böröczky–Machado–Ramos**, [*Quantitative stability for Minkowski's problem*, arXiv:2603.17726v3](https://arxiv.org/abs/2603.17726v3), revised 13 May 2026, was checked in its current official record and actual Theorems 1.1–1.2 and variational proof in §3.1. It gives quantitative inversion of surface-area data and extensions for $p>1$ with the stated exceptional parameter. Its proof compares variational energies and uses classical Brunn–Minkowski stability. It is not an unrestricted quantitative $p=0$ theorem. Applying its inverse bound still requires suitable measure or energy closeness; H49's small Wulff deficit does not hand that over. It therefore cannot replace the contact/product/two-endpoint bridge by its title alone.

**Lu**, [arXiv:2608.20730v3](https://arxiv.org/abs/2608.20730v3), revised 28 September 2026, supplies (n-2) reflection results. I read the fiber inclusion/Hölder proof and Lemmas 4.1–4.2 and Proposition 4.3's equality synchronization. Exact equality fixes planar fiber directions and ratios. This gives neither unrestricted fibers nor quantitative synchronization at finite defect. **Xi**, [arXiv:2307.04266v4](https://arxiv.org/abs/2307.04266v4), revised 14 November 2024, is stronger than a local or two-zonoid theorem: Theorem 4.4 permits a zonoid base and arbitrary symmetric comparison body. Its actual projection/generating-measure induction and reverse-to-forward minimization were read. The generating measure is structural and unavailable for a general body in dimension at least three. **Van Handel**, [final author version `logzon221121.pdf`](https://web.math.princeton.edu/~rvan/logzon221121.pdf), has a genuine nonsmooth mixed-area equality operation in Lemmas 4.2–4.3. Neither “nonsmooth” nor retained squares alone removes the zonoid hypothesis.

**Kolesnikov–Livshyts–Rotem**, [arXiv:2507.12099v3](https://arxiv.org/abs/2507.12099v3), current revised 26 August 2026, Theorem 1.4 and Proposition 4.8's transport-Hessian/Bochner calculation, gives a strong scalar variational framework. **Wang**, [arXiv:2510.19061v2](https://arxiv.org/abs/2510.19061v2), revised 4 November 2025, uses smooth conditional local rigidity and adapted perturbation/erosion. **He–Liu**, [arXiv:2510.21530v1](https://arxiv.org/abs/2510.21530v1), uses positive smooth density, regularity of the equality path, determinant differentiation and a maximum argument. Their actual relevant statements and proof passages were read. None supplies the needed uniform finite-error reconstruction for arbitrary nonsmooth pairs under ball bounds alone. I have not assumed that their smoothness or density constants remain bounded in a facet approximation.

## 3. Operation-level account of the proposed bridge

### 3.1 Finite-defect fields: a necessary extension, not the whole novelty case

H49 fixes $\varepsilon\asymp\delta>0$, exhausts directions and slab powers, and chooses interior times with **unnormalized** curvature defect $O(\delta)$. Dense tests are completed before taking the hard limit. The mean survives as $m=-\ell'+O(\delta)$; setting it to zero would erase dilations and break the endpoint volume argument.

The retained square controls $D_zW-P\tau$; the $DP$ energy and the bound on $W$ control the otherwise free constant part of $P$. Local smooth convergence of moment coefficients then gives Sobolev weak compactness and strong local convergence of the fields, retaining identities and a finite nonzero energy budget. Positive joint slab contact measures and their radial marginal pass the signed flux, with continuous directional slope $b(u)$; the global $W$ bound controls tails. No bulk $L^2$ limit of the diverging score is asserted.

Much of this is standard compactness once the correct estimates are in hand. Its significance is that the accepted squares and regularizer are arranged to produce fields with **all** the identities required downstream at finite defect. Merely solving a scalar Neumann problem would supply the boundary flux but not the moment tensor compatibility. H49's ball diagnostic separates those requirements. I do not treat that diagnostic as a theorem ruling out every alternate variational construction.

### 3.2 A finite position-test error must become an absolute normal residual

After hard normalization, Poincaré/coercivity estimates, symmetrization by the mean Hessian, and spectral clustering give approximate affine fields and a position-test residual. The rate bookkeeping here is a quantitative version of the LSX constant-matrix operation and has substantial classical precedent.

The boundary interface changes the kind of control. On the intermediate boundary the residual has the form

\[
F(x,u)=b(u)h_C(u)+(A_\gamma x)\cdot u.
\]

Only integrals of $F$ against admissible smooth functions of **position** are initially small. One cannot insert the sign of $F(x,\nu_C(x))$, or an arbitrary measurable normal test, into that bound. For the radial parametrization $X(\theta)=\theta/p_C(\theta)$, the normal is BV, while $F$ is Lipschitz in its two arguments on the bounded range. Thus $f(\theta)=F(X(\theta),N(\theta))$ has a uniform BV bound. Smoothing $f$ and lifting it to an admissible radial position test yields

\[
\int F^2\le C(e/s+s),\qquad \int|F|\le Ce^{1/4}
\]

after choosing $s=\sqrt e$. The interpolation estimate is familiar. Its role as the conversion for this signed contact identity, uniformly across facets and ridges, is an essential interface absent from the checked LSX equality proof and not a consequence of weak convergence alone.

The Jacobian notation requires care: $J=p^{-n}|\nabla p|$ uses the **full homogeneous Euclidean gradient** $\nabla p=p\theta+\nabla_Sp$. Using only $\nabla_Sp$ would give zero area for the unit sphere. I49's adjacent normal formula makes the full-gradient interpretation coherent. The independent exact checks verify it for the sphere and anisotropic ellipsoids. This is a notation clarification, not a detected counterexample or a replacement proof.

### 3.3 A single global product, without coordinate symmetries

Small off-block mixed Hessian entries imply that $\Pi_i\nabla\varphi$ is nearly independent of the complementary coordinates. H49 uses **transverse averages over a full cube**, not restrictions to coordinate axes whose traces are uncontrolled by a bulk Sobolev estimate. Poincaré gives the $L^2$ approximation, and the hard Lipschitz bound upgrades it to a sup estimate.

Writing those averages as $F_i(z_i)$, H49 forms the one compatible body

\[
D=\prod_i\operatorname{conv}\overline{F_i(Q_{L,i})}.
\]

Independent choices of coordinates occur together in the same cube, and independent convex combinations expand to convex combinations of joint choices. Hence this product compares to the convex hull of the actual gradient image, rather than to unrelated favorable slices. The exponential source tail and a target cap lower bound then cover all of $C$, giving $d_H(C,D)\le Ce^{1/[2(n+2)]}$.

The elementary product-of-convex-hulls identity is not new. The indispensable application is the combination of mixed-Hessian information, transverse averaging, hard Lipschitz control and source-tail coverage. This replaces the unconditional coordinate inclusion in Böröczky–De and the exact commutation/splitting in LSX. Neither antecedent supplies it merely by setting its error variable to a small positive number. Different blocks chosen separately or a product covering only a high-probability source core would not satisfy the target.

### 3.4 Both original endpoints, with a common product

Hug–Schneider continuity can now be used because $D$ has actually been constructed. Since $S_D$ is supported on block spheres, it bounds the normal mass of $C$ away from those spheres. Combining that information with the **absolute** residual and Wulff contact identities gives integrated absolute support errors for

\[
K^\sharp=e^{tA_\gamma}D,\qquad
L^\sharp=e^{-(1-t)A_\gamma}D.
\]

The transfer uses only the Lipschitz functions $|h_K-h_{K^\sharp}|$ and $|h_L-h_{L^\sharp}|$ when changing from $S_C$ to $S_D$. It does not pass an arbitrary discontinuous normal test through bounded-Lipschitz convergence. For a block dilation $T|_{E_i}=s_iI$, the exact product surface Jacobian on the $i$-th block sphere is $\det(T)/s_i$. This transfers the two errors onto their respective comparison surface measures.

The surviving mean/trace relation and volume chord estimate fix **both** endpoint volumes. Only then does FMP turn the resulting anisotropic deficits into translation/dilation $L^1$ errors. Even convex overlap removes translation, volume comparison fixes dilation, and cap estimates give Hausdorff error. These final steps are established tools. The preceding synchronization is the reason they prove distance to a common block pair instead of two independent near-products or just closeness of one intermediate body.

This gives the rate chain, with $e=\delta^{\theta_n}$,

\[
\theta_n=\frac{b_n}{8(a_n+b_n+1)},\qquad
\omega\lesssim e^{1/[4(n+2)]},\qquad
d_{\mathcal E}\lesssim\omega^{1/(2n)}
=\delta^{1/\alpha_n}.
\]

The constants $a_n,b_n$ must be dimensional before this balancing. A body-dependent exponential core rate would yield a body-dependent power and would not establish H49. This is one of I50's mathematical obligations. The final upper-budget passage at zero deficit avoids assuming the equality theorem as an axiom.

## 4. Why this is not a technical reduction certificate

I tried the strongest plausible operation combinations, not just statement matching:

1. **LSX plus ordinary compactness and spectral grouping.** This obtains the natural almost-constant matrix stage, but exact common normal support is lost at positive defect. Ordinary compactness yields no fixed power. The radial residual, compatible global product, and two-endpoint transfers are still needed.
2. **Uniform scalar Brascamp–Lieb stability plus moment continuity.** Machado–Ramos removes a potential scalar uniformity objection, but it needs its own finite scalar deficit or moment variational gap. Neither is the raw hard boundary score. Granting its strongest estimates does not supply the missing contact or product geometry.
3. **Böröczky–De grouping plus cone-volume near-product stability.** The first uses reflection/unconditional structure; the second needs near saturation on an exact subspace. H49 has neither as an initial hypothesis. Normal concentration near a subspace cannot be relabeled exact mass on it. Constructing an exact product before applying these results makes the proposed reduction circular at its decisive step.
4. **Hug–Schneider plus quantitative Minkowski inversion or FMP.** These are valid later operations. Their hypotheses require the geometric or anisotropic data that the residual/product/endpoint bridge is designed to supply. Applying them immediately to the small Wulff deficit skips that bridge.
5. **Lu or zonoid equality synchronization.** Exact fibers, reflections, or a generating measure are structural inputs in their proofs. No checked argument removes them while preserving finite defect and a dimensional power.

This does not prove that no shorter classical argument exists. It does show why the checked operations do not presently form the requested noncircular routine reduction. Conversely, calling every step “standard” after H49 has chosen the compatible fields, tests, product and endpoint measures would erase the actual interface work. The claimed result also uses the accepted higher-dimensional tensor/concavity operations materially; unlike the prior planar reduction, the comparison above does not yield the same unrestricted claim from already available planar machinery.

The substantial component is therefore the **integrated finite-defect moment-to-product-and-endpoints construction**, especially the normal residual conversion coupled to global transverse reconstruction and endpoint synchronization. I would not nominate the scalar Neumann construction, the interval obstruction, the rate arithmetic, the qualitative symmetric equality statement, or any individual standard lemma as separate substantial findings.

## 5. Proof-risk boundary and independent diagnostics

I found no specific original-proof counterexample in this significance screen. This is not a declaration that every analytic estimate has passed an independent full audit. I50 must check, in particular, the nonzero-energy compactness and limit identities, dimension-only core/tail constants after both bounded changes of variables, the BV chain rule/test norm, coverage of the entire target by the constructed product, and both endpoint perimeter/volume normalizations. Failure at one of these gates would change proof status; it would not itself establish TECHNICAL ONLY significance.

The owned exact checker performs 309 assertions using rational arithmetic. It verifies the full-gradient radial Jacobian on a sphere and anisotropic ellipsoids; an alternating signed residual with $L^1=1$ and dual-Lipschitz bound tending to zero while its BV norm grows; transverse averaged gradients of a convex polynomial on a full three-dimensional cube; expansion of independent convex combinations into a common product image; block surface Jacobians for rational box dilations; both endpoint trace/volume coefficients; and the complete exponent composition over a rational parameter grid. These checks target signs, norms, compatibility and dependency bookkeeping. They are not numerical evidence for the theorem and do not substitute for I50.

For example, on $Q=[-1,1]^3$ with $\varphi=|z|^2/2+\eta z_1^2z_2^2$, $0\le\eta\le1/8$, the transverse averages are $F_1=(1+2\eta/3)z_1, F_2=(1+2\eta/3)z_2, F_3=z_3$. The exact mean-square error is $32\eta^2/135$, whereas the sum of the two mixed-Hessian square expectations is $32\eta^2/9$. The axis restrictions are different. This is a concrete check of the operation H49 uses, not a test mirroring its final exponent alone.

## 6. Evidence, failures, and bounded-search scope

All writes are confined to this review and its assigned source/experiment directories. The original current brief, including appended I49/I46 briefs, prior reports and objections, relevant source bytes, parent record, and immutable seals are frozen. Only relevant prior inputs and seals are copied; old archives are checked in place. The four shared ledgers and live I51 orchestration record are explicitly mutable observations. I did not edit or reseal any predecessor artifact, inspect unfinished review drafts, stage, commit, or publish.

Fresh primary retrieval produced 31 successful response bodies: the 28-response initial batch and three additional responses for Machado–Ramos and Chazal–Cohen-Steiner–Mérigot. The 19 PDFs have reproducible `pdftotext -layout` extracts. Official current abstract records are preserved for the versioned recent results; author-hosted papers are identified by URL and byte hash, not assigned invented version numbers. The exact primary passages read, source hashes, current-version evidence, five bounded search responses, corpus-search outputs, and exact diagnostics are retained. Search snippets and aggregators were used only to discover candidates, never as substitutes for the compared primary proofs. No exact unrestricted duplicate was found within this scope; that is a bounded-search statement.

The parent I49 record is not flattened into an unqualified PASS. It records an **initial unmodified verifier failure** on raw `rg` stdout byte ordering, a later **successful unmodified retry**, direct replay comparisons, and an explicitly **order-normalized in-memory replay**. My own I49 replay replaces only that comparison by sorted line comparison, preserving duplicate lines, and leaves the original file and seal untouched. It passes with the author's 163 sealed artifacts, 35 frozen inputs, six predecessor seals/2253 predecessor artifact checks, all 9340 corpus files, and 506 exact assertions. Those are integrity/diagnostic outcomes, not proof or significance approval.

There was one additional local evidence-preparation failure: the initial freeze script selected the wrong list element as the task JSON and raised `JSONDecodeError`. Its failed source is preserved; selecting the task file by its explicit path fixed the preparation. No author mathematical file changed, and no failed result is presented as a successful vanilla run. There were no failed fresh primary HTTP responses in these two retrieval batches.

The owned evidence has 55 frozen inputs and 61 exact read-passage records. The read-only verifier checks its exact artifact set and seal, frozen/live immutable bytes, mutable observations, source passages, response hashes, all PDF text replays, the full 13223-entry tree/749-manuscript inventory and 9340-file corpus, line-multiset search replays, the predecessor seals without refreshing them, and its own exact diagnostics. The separate normalized author replay is labeled as such in its retained record. Passing these checks establishes the evidence boundary only.

**Disposition for the parent:** retain H49 as SUBSTANTIAL conditional on the separate original-proof gate I50, with full LSX and classical-tool attribution and the scope limitations above. If the original bridge does not pass, report that proof outcome separately; this significance review does not authorize repairs, acceptance, counting, or publication.
