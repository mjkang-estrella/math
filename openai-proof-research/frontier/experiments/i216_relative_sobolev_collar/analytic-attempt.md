# I216 — exact boundary by the paid smooth cubical cutoff

## 0. Verdict, hypotheses, and dependence

**PROVED SOURCE-DEPENDENT RELATIVE DENSITY; TECHNICAL OVERLAP. NO SUBSTANTIAL NOMINATION.** The boundary target in the question follows from a lower operation already in the stipulated source. A stronger linear-cost correction stated in §6 remains unpaid. Both independent acceptance gates and the count remain with the parent.

Put B=B(0,1)⊂R³, D=B(0,2), and fix 3<p<∞. The target proved here is:

**Theorem.** If f:cl(B)→cl(B) is a homeomorphism, f=id on ∂B, and f∈W^{1,p}(B), then there are orientation-preserving C∞ diffeomorphisms g_j:R³→R³, each identity on a neighborhood of R³\B, such that g_j|B→f strongly in W^{1,p}(B). Consequently the restrictions are smooth and nonsingular on cl(B), have smooth inverses there, and fix ∂B exactly.

The input orientation is forced by its boundary identity. The source ordinary approximation theorem, and *all* its lower operations, are accepted at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. I213's strong Alexander compression is used as a paid reduction; it is not reproved. No inverse Sobolev convergence, elastic-energy convergence, incompressibility, quantitative bi-Lipschitz constant, or p=∞ assertion is made.

The decisive operation is `hp:smooth-cutoff` in high-range `05-high-preparation.tex`, lines 1945–2046, together with its normalized hypotheses in `hp:cutoff`, lines 1104–1131. The former was not used in the supplied I213 argument. Its conclusion is stronger than a topological opening and exactly covers a **smooth input** such as an ordinary approximant. This resolves I213's stated gap by a source-dependent localization, rather than by a new annular extension theorem.

## 1. Exact paid interfaces used

Let Q=[−1,1]³, t(y)=||y||∞−1, and Q_s={t<s}. There are fixed c>0, C>2 and a sufficiently small dyadic-scale threshold such that, if h is a smooth diffeomorphism on a neighborhood of cl(Q_{Cs}) and

    |h(y)−y|≤cs  whenever |t(y)|≤Cs,

then for every ε₀>0 there is a locally bi-Lipschitz homeomorphism K, equal to id on Q and to h near and outside ∂Q_{2s}, preserving the previous local image, with

    ∫_{0<t<2s}|DK|^p ≤ C_p ∫_{|t|≤Cs}|Dh|^p + ε₀.       (1.1)

The constants in (1.1) do not depend on h or small s. The local forward/inverse Lipschitz constants of K may depend on h,s,ε₀. In the source proof a *finite* family of normalized smooth hole fillings is fixed first, with bound L(h,s); a positive squeeze parameter α is then chosen so α^p L(h,s)^p times the hole volume is below ε₀. There is no uniform inverse bound. This choice order is essential.

The ordinary high-range theorem supplies G_j:D→D, smooth diffeomorphisms in W^{1,p}, strongly approaching any Sobolev homeomorphism F:D→D. Morrey on the fixed smooth domain gives uniform convergence when p>3. The full proof of `sm:bilip-pl` and `sm:pl-smoothing` supplies the local approximation mechanisms used in §3. The argument does not infer derivative estimates from `hp:opening`, `sm:relative-pl`, or `sm:local-extension` alone.

`hp:carrier` protects internally selected exact cores, and `hp:full-rank-correction` already uses (1.1) for smooth approximants and small-energy shells. Thus the central energy operation needed below is already paid. Re-running the entire carrier with a prescribed collar is unnecessary.

## 2. Inverted-collar correction, with derivative estimate

Here is the precise intermediate assertion, in the locally bi-Lipschitz category. Fix

    0<r<a<b₀<b<1.

Let F:D→D be a Sobolev homeomorphism equal to id on D\B_r. Suppose G_j:D→D are smooth diffeomorphisms converging strongly to F in W^{1,p}(D). There are globally locally bi-Lipschitz homeomorphisms H_j:R³→R³ such that

    H_j=G_j on B_a,       H_j=id on R³\B_{b₀},
    ||H_j−G_j||_{W^{1,p}(D)}→0.                         (2.1)

All equalities can be arranged on neighborhoods of the indicated closed separating surfaces by leaving fixed positive geometric margins. In particular (2.1) supplies exact inside and outside agreement before smoothing.

### 2.1 A fixed smooth chart turning exterior into interior

Choose R∈(a,b₀). For θ∈S² let ρ(θ)=1/||θ||∞. Thus 1≤ρ≤√3 and ρθ parametrizes ∂Q. Choose a positive smooth function ρ̃ on S² sufficiently uniformly close to ρ. Define, for y≠0,

    J(y)=R ρ̃(y/|y|) y/|y|².                            (2.2)

Each ray is mapped by u↦Rρ̃(θ)/u. Hence J is a smooth involution of punctured R³. It reverses orientation and has bounded derivatives and inverse derivatives on every fixed compact annulus. On ∂Q,

    |J(ρθ)|=Rρ̃(θ)/ρ(θ).

Choose the approximation so this surface lies strictly between B_a and B_{b₀}. After fixing a small s₀>0, the same is true for all cubical surfaces |t|≤Cs₀. The image of their bands has volume at most a fixed constant times their width.

There is also a round sphere |y|=q<1 on whose neighborhood J takes values inside D and outside B_a. Indeed choose ρ̃ so R max ρ̃<2, and then q with R max ρ̃/2<q<1, shrinking the gap to 1 if necessary. For q<|y|≤(1+Cs₀)ρ(θ), the radial image ranges from near R to at most R maxρ̃/q<2. Take fixed positive margins. All these images lie in a compact annular set

    A₀⊂{a₀<|x|<2},  with r<a₀<a.

In particular F=id on A₀. Put η_j=||G_j−id||_{C⁰(A₀)} and d_j=||G_j−id||_{W^{1,p}(D\cl(B_{a₀}))}. Both tend to zero. By enlarging A₀ slightly first, all images needed for chain-rule estimates remain in fixed compact annuli.

### 2.2 Fill only the discarded side

On the cubical annular neighborhood just described set

    h_j=J∘G_j∘J.

For large j this is well defined, because G_j(J(y)) stays away from zero. It is smooth and injective there, and

    ||h_j−id||∞ ≤ L η_j                                  (2.3)

with fixed L. Choose a sphere |y|=q' slightly larger than q and still less than 1. The image h_j(q'S²) is a smooth embedded sphere, bounds a smooth ball, and contains zero on its bounded side: the straight homotopy to q'S² avoids zero by (2.3). The smooth ball-filling operation used explicitly in the proof of `hp:smooth-cutoff` extends the prescribed map of a two-sided collar of this sphere to a smooth diffeomorphism of its interior onto that ball. It is the combination of smooth three-dimensional Schoenflies and extension of a sphere diffeomorphism by a smooth isotopy. Keep h_j unchanged outside a smaller inner collar of q'S².

This gives a smooth diffeomorphism ĥ_j on a neighborhood of cl(Q_{Cs₀}), equal to h_j throughout all the bands |t|≤Cs₀. Gluing is smooth because the filling agrees on an open collar, not just on the sphere. Its derivatives in the filled interior can be arbitrarily large. They are never estimated or used: the cutoff replaces the entire cube by id, and (1.1) samples only its boundary band. The existence of this filling is the same paid topological step as in the source proof; no quantitative Schoenflies claim is being inserted.

### 2.3 Apply the cutoff at a scale fixed by displacement

For η_j>0, choose a dyadic s_j satisfying

    (2L/c)η_j ≤ s_j < (4L/c)η_j,

so for large j it is below s₀ and the source threshold. Then (2.3) implies the source smallness condition with room. Use (1.1) for ĥ_j and an arbitrary ε_j↓0. It returns K_j=id on Q and K_j=ĥ_j near ∂Q_{2s_j}. Define H_j as follows:

- inside the bounded physical surface J(∂Q_{2s_j}), use G_j;
- on T_j=J(Q_{2s_j}\Q), use J∘K_j∘J;
- on the unbounded side of J(∂Q), use id.

Near the first interface, J∘K_j∘J=J∘h_j∘J=G_j. At the second interface the transformed map is locally bi-Lipschitz across the interface since K_j is locally bi-Lipschitz across ∂Q and is id on Q. Thus the piecewise definition is a local homeomorphism everywhere, including the interfaces; near zero only G_j is used. It is id outside B_{b₀} and hence proper. A proper local homeomorphism R³→R³ is a covering; its degree is one, since it is id near infinity. It is therefore a global homeomorphism. Both it and its inverse are locally Lipschitz. The fixed geometric margins give H_j=G_j on B_a and H_j=id outside B_{b₀}.

If η_j=0, G_j=id on the fixed open collar itself, so one simply glues G_j on the inner component to id on the exterior; no cutoff is needed.

### 2.4 Derivative accounting; no hidden filling constant

On the shell, K_j(y) belongs to ĥ_j(Q_{2s_j})\Q. The first set is bounded by its outer boundary h_j(∂Q_{2s_j}), which lies in a fixed ball by (2.3); the second excludes the unit ball. Hence J and DJ at K_j(y) are bounded uniformly. Also J,DJ and the change-of-variables Jacobians are bounded uniformly on the fixed source bands. The chain rule and (1.1) give

    ∫_{T_j}|DH_j|^p
       ≤ C_* ∫_{|t|≤Cs_j}|Dh_j|^p + C_* ε_j
       ≤ C_* ∫_{A_j}|DG_j|^p + C_* ε_j,                (2.4)

where A_j=J({|t|≤Cs_j})⊂A₀, |A_j|≤C_*s_j. Constants C_* depend only on the fixed collar geometry, p, and the paid constant C_p. They do not depend on ĥ_j's interior filling, its Lipschitz constant, or j. Thus

    ∫_{A_j}|DG_j|^p ≤ 2^{p−1}(3^{p/2}|A_j|
                                      +∫_{A_j}|DG_j−I|^p)
                         ≤ C_*(s_j+d_j^p).             (2.5)

On T_j, the pth derivative-error integral is bounded by (2.4) plus the original derivative integral on T_j. Both map values stay in a fixed ball, so their pth value-error integral there is at most C_*|T_j|≤C_*s_j. On the untouched inner region the error is zero. On the exterior region H_j=id and its error from G_j is bounded by d_j^p. Consequently

    ||H_j−G_j||_{W^{1,p}(D)}^p
        ≤ C_*(η_j+d_j^p+ε_j).                          (2.6)

This proves (2.1). Notice that (2.4) estimates actual derivatives. Qualitative isotopy, uniform closeness, and a scalar interpolation are not used to infer it.

## 3. Exact-exterior smoothing of the locally bi-Lipschitz output

For completeness, the relative smoothing fact needed for the boundary theorem follows by making local choices in the *fully read* source proofs, as follows.

**Lemma (identity-exterior smoothing).** Let H:R³→R³ be a locally bi-Lipschitz homeomorphism equal to id outside B_u, and let u<v. For each finite p and ε>0 there is a global C∞ diffeomorphism S equal to id outside B_v and with ||S−H||_{W^{1,p}(B_v)}<ε.

**Proof.** Such an H is globally bi-Lipschitz: take finite local bounds on a compact neighborhood of B_u, use identity elsewhere, and integrate along subdivided line segments; apply the same argument to H^{-1}. The following is a support-preserving specialization of `sm:bilip-pl`, not a consequence of its statement alone.

Use a uniform dyadic mesh of small side h on R³ with its conforming affine subdivision. Its normalized shapes, enlarged boxes and color configurations are finite, exactly as required in `sm:mesh`. It can be processed on any large fixed cube; all nonidentity changes below have compact support strictly inside that cube. The source proof uses S₀=2n₀ color stages, a number independent of h. Quantize vertex values to a dyadic target grid fine enough for the source interpolation error. Choose its denominator to contain the finitely many dyadic vertex/face-center coordinates in this uniform subdivision. Thus wherever H is id at all the interpolation vertices, the interpolant L is exactly id, with no rounding error.

In the first round use the source's good-patch interpolation and insertion. On a patch where the current map and L are both id on the full support box, take the inserting domain homeomorphism to be id. Declare its inner core protected just as for any other patch. In the second round, whenever the current map and H are id on the support box, use the identity as the PL model and the identity as its insertion. This realizes all identity overlap data. Otherwise use the source's finite libraries and protected-core construction without modification. Including the identity choice in the library is harmless; its derivative bound is fixed. Each stage can spread the nonidentity set by at most the diameter 10√3h of a support box. Interpolation uses vertices in the fixed enlargement B_Q(20), which adds at most 40√3h once. Therefore the final nonidentity set lies within distance (40+10S₀)√3h of B_u. Choose h below the fixed buffer divided by this constant.

The finite-library derivative constants are chosen *before* h is further decreased, exactly as in `sm:model-derivative-bound`. The good-cube error is unchanged. On bad cubes the estimate remains (M+K)^p times their volume. Almost-everywhere differentiability and Lebesgue differentiation make this volume tend to zero on the fixed compact active region, as in `sm:bad-error-budget`. Outside that region the error is identically zero. The added identity decisions introduce no bad derivative terms. Thus the source resolution choice gives a PL homeomorphism P, arbitrarily strongly close to H and equal to id outside B_{v₁}, for any fixed u<v₁<v. Every stage is a domain homeomorphism, so injectivity and the target are preserved. This justifies the support claim and the energy estimate simultaneously.

Now apply the explicit `sm:pl-smoothing` construction to P, allowing supports only within an intermediate B_{v₂}, v₁<v₂<v. There are only finitely many nontrivial simplex stars on its compact nonidentity region. At artificial edges and vertices whose stars carry id, use the trivial edge model and trivial sphere isotopy. All other edge tubes and vertex balls can be chosen inside B_{v₂}. The source bounds their derivatives by fixed local constants before shrinking their volumes, giving the prescribed sum of pth errors. For face smoothing choose a symmetric probability kernel. Convolution of id is exactly id, even with variable radius w, since its first moment is zero. Choose all integration balls based outside B_{v₂} to remain in the identity region; this is possible because v₂>v₁. Hence this stage also fixes the exterior. The source's positive-determinant convex-hull argument and its vertex/edge determinant estimates apply without change. The resulting smooth map has positive determinant, is proper because it is id outside B_v, and has degree one. It is a global diffeomorphism. Allocate ε/2 to each stage. ∎

This proof uses the derivative estimates from the smoothing construction; `sm:relative-pl` alone would not suffice. It only promises exact identity on an exterior region. It does not, as stated, retain an arbitrary smooth G_j exactly on the inner ball.

## 4. Complete proof of the boundary theorem

First suppose f is already id on B\B_r for some r<1. Extend it by id to D and then to R³, denoting the extension F. It is a Sobolev homeomorphism on D. Apply the pinned high-range approximation theorem to obtain G_j→F strongly in W^{1,p}(D). Morrey gives the uniform convergence used in §2. Choose fixed r<a<b₀<b<1. Obtain H_j by §2. Apply the lemma of §3 to H_j with u=b₀, v=b and error ε_j→0. Denote the resulting global diffeomorphism by S_j. It is id on R³\B_b, and (2.6) plus the smoothing error give

    ||S_j−F||_{W^{1,p}(B)}
      ≤ ||S_j−H_j|| + ||H_j−G_j|| + ||G_j−F|| →0.

Since S_j fixes the exterior, it maps B onto B and is identity in a full boundary collar. Its inverse and differential are smooth and nonsingular on cl(B), indeed on all of R³.

For arbitrary boundary-identity f, invoke the supplied, paid I213 Alexander-compression lemma: F_r→f strongly as r↑1, with F_r identity outside B_r. Apply the preceding paragraph to each F_{r_m}, choosing one smooth approximant with W^{1,p}(B) error <1/m. The triangle inequality proves the theorem. No rate for the compression is asserted or needed. ∎

**Relation to the exact formulation CS_p.** §2 proves exact inside/outside CS_p with H_j locally bi-Lipschitz. §3 gives smooth corrected maps with exact exterior and vanishing error, which suffices for the boundary theorem. The present proof does not assert that the *smooth* maps also equal G_j on B_a. That additional relative smoothing condition is not needed here and is not silently promoted to a proved assertion.

## 5. A genuinely different route: localizing a smooth isotopy

This route is conditional and does not supply the theorem independently. It identifies precisely why a topological extension theorem alone is insufficient.

Suppose a smooth isotopy Φ_t of ambient diffeomorphisms, Φ_0=id, has velocity v_t=∂_tΦ_t∘Φ_t^{-1}. Choose a fixed spatial cutoff χ equal to one on the relevant inner tracks and zero outside the desired outer collar, and put w_t=χv_t. Let Ψ_t be its flow. Uniqueness of the ODE gives Ψ_1=Φ_1 on the protected inner set whose full Φ_t-track remains in {χ=1}, while Ψ_1=id outside suppχ. There is no scalar interpolation of endpoint maps here.

For a measurable initial region A and a region U containing its swept set ⋃_{0≤t≤1}Ψ_t(A), set

    L=∫₀¹||Dw_t||∞dt,
    Q=∫₀¹(||w_t||_{L^p(U)}+||Dw_t||_{L^p(U)})dt.

The differential equation DΨ_t'=Dw_t(Ψ_t)DΨ_t gives ||DΨ_t||∞≤e^L, and |det DΨ_t^{-1}|≤e^{3L}. Minkowski and change of variables therefore give

    ||Ψ_1−id||_{W^{1,p}(A)} ≤ C e^{(1+3/p)L} Q.          (5.1)

For the value part use Ψ_1−id=∫w_t∘Ψ_tdt; for derivatives integrate Dw_t(Ψ_t)DΨ_t. This proves (5.1), with a harmless fixed norm convention constant. The change of variables integrates over Ψ_t(A)⊂U, so invariance of A is not required. To use this for correction, take A=D\B_a, control the swept annular region U, and compare Ψ_1 with G there by adding ||G−id||_{W^{1,p}(A)}; on B_a the endpoints agree exactly.

A sufficient annular path estimate is e^{(1+3/p)L_j}Q_j→0, together with the track separation and exact matching requirements. Endpoint strong W^{1,p} convergence does not give any such bound on an isotopy, on its time-dependent velocity, or on L_j. Edwards–Kirby supplies compact-open deformation/extension, not (5.1)'s analytic hypothesis; Smale/Li–Watts gives existence/smooth dependence of sphere isotopies, not uniform Sobolev velocity control. We have not proved or disproved the needed path estimate. This route is genuinely different from §2, which pays for bad derivatives by a shrinking shell and the source's finite fillings plus strict squeezing.

The I213 fixed-cutoff example remains valid and relevant: g_s→id strongly and uniformly, yet id+χ(g_s−id) folds, with determinant −exp(−1/s)/2 at its designated point. Neither §2 nor the flow construction uses that false inference. In particular the factorization through smooth ĥ_j and K_j is not a disguised scalar cutoff.

## 6. Stronger unpaid consequence after recognizing the overlap

The theorem in §4 and estimate (2.6) use a paid operation, so neither is nominated as a substantial new finding. To seek a stronger consequence, consider a **linear defect-cost collar retraction**:

For fixed a₀<a<b<1 and p>3, does there exist C,δ>0 such that every smooth diffeomorphism G:D→D with

    d=||G−id||_{W^{1,p}(D\cl(B_{a₀}))}<δ

admits a smooth diffeomorphism S:R³→R³, id outside B_b, equal to G on B_a, satisfying

    ||S−G||_{W^{1,p}(D)} ≤ C d ?                       (LD_p)

The constants must be independent of G, its inverse derivative, its minimum determinant, and all higher derivatives. The annular norm is on a fixed Lipschitz region, so Morrey gives a displacement bound O(d); containment of G(B_a) in B_b holds when d is small. The precise strong estimate and exact inner equality remain additional demands, not consequences of that containment.

What has actually been paid here is only O((η+d^p)^{1/p}) plus arbitrary smoothing error, η≤C d. This gives at best O(d^{1/p}) in terms of d. The source controls ∫|DK|^p by ∫|Dh|^p; on a width-s shell the identity derivative itself costs O(s). Its applicability requires s≳η. Thus the displayed proof cannot replace the O(η) term in the pth error by O(d^p). Choosing a thinner shell violates the input closeness condition; making the source filling parameter smaller affects ε₀, not the shell's baseline energy. This identifies the exact unpaid estimate, rather than claiming that a failed choice disproves LD_p.

A sufficient strengthening would directly control ∫|DK−I|^p by the displacement/derivative *defect*, uniformly under arbitrarily small Jacobians, or construct the isotopies of §5 with e^{(1+3/p)L}Q≤C d. No such estimate has been obtained in this investigation. No counterexample to LD_p has been proved. The scalar-cutoff example refutes its naive proof, not LD_p itself. A genuine solution of this stronger uniform estimate, with a separate novelty/contribution check, would be a different candidate from the routine exact-boundary localization now established.
