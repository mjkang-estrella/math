# I252 — contribution analysis of quantitative complete-witness scalarization

**Verdict: TECHNICAL.** Q1–Q4 are a useful explicit stability refinement of R016's exact coefficient-rank mechanism, and are not a theorem I found already stated in the inspected external primary literature. On the requested standard of a *distinct substantial* finding requiring a nonroutine advance, the submitted argument does not clear the contribution gate. This is a contribution judgment, conditional on independent proof validation; it is neither a proof failure nor a proof PASS. No finding is accepted, and the supplied count of ten toward twenty is unchanged.

The exact assessed proof is `frontier/experiments/i247_quantitative_complete_rigidity/analytic-attempt.md`, SHA256 `7d8b629513741abab53339c19bb05c9f611ecbd0af1b6ace3246dff8af0eae8b`, matching the request. I read the entire file, including all Q1–Q4 hypotheses, proof stages, active-block extension and counterexamples. I did not review an earlier version or read other current reviews. Early notes were written before the primary comparison was complete.

## 1. Exact scope receiving the verdict

Fix d≥2 and R,δ,g,ℓ>0. A∈M_d(C) has K=W(A) with interior and K⊂R Dbar, dist(σ(A),∂K)≥δ, and a regular analytic boundary arc of length at least ℓ on which the top eigenvalue of Re(conj(ν)A) is simple and separated from the next by at least g. For every finite m, every finite-degree M_m-valued polynomial P with max_K‖P‖=1, and 0≤ε≤1/2 with γ=‖P[A]‖≥2−ε, every unit maximal singular pair x=vec X,y=vec Y has

    t_X=1−‖X‖op² ≤ min(1,C0√ε),
    t_Y=1−‖Y‖op² ≤ min(1,C0√ε),
    C0=8(d−1)R(3R)^(d−1)δ^(−d)[9πR²/(gℓ)+1/√6].

Leading Schmidt product vectors approximate x,y within √(2C0) ε^(1/4). Their coefficient factors u,v give the compression of the *original specified witness*

    p(z)=v*P(z)u,  max_K|p|≤1,
    ‖p(A)‖≥γ[1−t_X−t_Y−√(t_Xt_Y)]≥2−ε−6C0√ε.

There is no dependence on m, degree, or coefficient magnitudes. The active-block extension assumes a reducing block B satisfying the geometric hypotheses and ‖P[B]‖=‖P[A]‖, with the bound on P normalized on the full W(A). It gives existence of p for A. It does **not** give the every-pair assertion for arbitrary full-matrix singular pairs spanning several active blocks.

This is positive-deficit coefficient recovery, not a compactness modulus and not merely a nonattainment argument. Disk proximity, global approximation of P, optimal exponents/constants and a nilpotent reducing block of P[A] are all outside the statement. I assess scalarization on its own merits: the absence of disk geometry is not by itself the reason for TECHNICAL.

## 2. Closest external results: real differences, no demonstrated duplicate

### ACV v3

I read actual statements and full proofs in Sections 5, 7, 9, and Section 11 through Corollary 11.5. In Section 5, Lemma 5.1 compresses a complete witness to coefficient subspaces of dimensions at most d. Lemma 5.2 is a first-variation orthogonality statement at an exact homomorphism-norm extremum. Theorem 5.3 obtains orthogonal base Schmidt families for a minimal rectangular extremal, with r+s≤d. It does not give small tails for each near-extremal witness. Its compression can still have r,s>1.

Section 7's row/column argument proves scalar/complete equality equivalence through dimension three; its dimension-four reduction leaves (2,2). Section 9, Theorem 9.5, bounds the tuple products (Σ_ij‖T_iT_jx‖²)^(1/2) at a norming input, using a column square function. Theorem 9.7 gives the corresponding scalar sharp second-iterate bound. Theorem 9.8 constructs a nearly reducing norm-two square-zero block for an operator satisfying *both scalar iterate square functions*. Corollary 9.9 applies this to a scalar value f(A), with error at most 8√ε for its stated small-deficit range. Neither the hypotheses nor the conclusion concern the Schmidt ranks of a general matrix polynomial witness. Theorem 11.2 is scalar polynomial equality classification; Corollaries 11.4–11.5 concern complete equality only in dimensions ≤3.

Thus Q2 and Q4 are not obtained by simply substituting P[A] for f(A) in ACV. The submitted weighted-chain example correctly marks that obstruction. Equally, observing this difference does not establish a new substantial advance over the *already accepted R016*, which addressed precisely the complete coefficient channel. [ACV v3](https://arxiv.org/html/2608.27346v3).

### Jin v2 and the additional kernel paper

I read Jin v2 Sections 1–8 and Corollary 1, and independently read live Section 9 in full. Theorem 1 concerns ψ(A) defined by scalar polynomials. Its proof uses exact boundary-kernel equality, rational collapse (Proposition 3), identification of the full rational lemniscate (Proposition 4), and projective contact/divisibility (Propositions 5–6). Lemma 4 is scalar Schur interpolation. Section 9's Theorem 3 gives a uniform scalar domain-stability modulus, but the full proof defines it by a supremum and proves positivity by compactness. It gives neither an explicit power law nor coefficient recovery for a specified complete P. These are genuine differences from Q1–Q4. [Jin v2](https://www.preprints.org/manuscript/202609.0079/v2).

A current primary link led to Jin, *Degeneracy of the Operator-Valued Poisson Kernel Near the Numerical Range Boundary*, v3. I read Lemmas 2–3 and Proposition 10 with their full proofs. Proposition 10 already gives, at a nonspectral support point with support eigenspace multiplicity r,

    λ_(r+1)↑(Re(ν(wI−A)^−1)) ≥ gap_support/‖wI−A‖².

Its proof is the congruence identity plus Courant–Fischer. Up to the factor 2|q|, this is precisely the local positive-eigenvalue estimate in I247 Section 2. Its nearby-subspace result is about the boundary kernel under domain exhaustion, not about complete-witness Schmidt tails. I do not count it as a duplicate of Q2–Q4, but it further limits novelty credit for the local coercivity estimate. Note that this paper's scalar *support mismatch* δ(w,ν) is different from I247's spectral distance δ and from its support-eigenvalue gap g. [Kernel degeneracy v3](https://doi.org/10.20944/preprints202602.0563.v3).

### Stipulated companions

The direct pinned paper's thm:main, lem:faber, prop:coefficients, lem:resolvent and thm:domain, including the full two-ordered-product proof, were read. They provide the dimension/degree-independent coefficient energy, original positive field and nonnegative block comparison. The structural companion's thm:structural, thm:representation, prop:density and bridge/lem:comparison were read at the actual statement/proof level. The mass-one similar-matrix density does not itself force original coefficient rank one. Neither retained source states Q1–Q4. Both raw manuscripts and all retained excerpt blocks were authenticated against the immutable revision, not audited for truth.

## 3. The decisive comparison is R016, not only ACV

R016 already earns the structural step: small complete certificate data are connected to the codimension-one range of the *original* boundary field. In the exact proof, X*Y=0 and H^(1/2)(XX*−YY*)H^(1/2)=0 combine with rank H=d−1 to force rank X=rank Y=1. The singular-pair-to-scalar-compression step and arbitrary coefficient size/degree are already present. Its general-dimensional conditional Lemma S already covers any interior-spectrum A with a simple-support analytic arc; using general d with that arc supplied is not a new classification of high-dimensional matrices.

More specifically, the fully read I242 Section 7 explicitly identifies that, for fixed irreducible B with a boundary arc and lower bounds on nonzero support gaps, its residual controls proximity of D to rank-(1,1) inertia data. It identifies collapsing support gaps, arc length, spectral distance and reducing strata as the missing uniformity in the unrestricted target. I247 assumes positive lower bounds on exactly those quantities. This is an anticipated quantitative localization of the old argument, rather than a solution of the degenerating-strata problem.

I246's accepted contribution rationale credits the first discovery of this inverse boundary-rank mechanism. It does not reserve all future quantitative results as automatically substantial. Conversely it does not prohibit any future scalarization theorem from qualifying: a genuinely new robust mechanism or substantial removal of the nondegeneracy restrictions could do so. The present comparison must subtract the already credited mechanism.

## 4. Assessment of every claimed new ingredient

**Residual and energy.** Keeping positive deficit in the direct identity and replacing the fixed resolvent constant by (3R)^(d−1)/δ^d is useful explicit bookkeeping. The determinant/singular-value estimate is standard and costs only base dimension. It fixes a legitimate nonnormality issue but is not a new inverse argument. The old proof already controlled the same field in L²; the candidate replaces qualitative boundedness by an explicit fixed-class bound.

**Arclength weighting.** This is the strongest technical refinement. With F(t)=‖H^(1/2)DH^(1/2)‖HS and λ_min^+(H)≥2g|q|/(3R)², the pointwise bound has F/|q|. Since ∫_I F²≤S and ∫_I |q|=length(Γ)/(2π), Cauchy–Schwarz gives ∫_I|q|²≥ℓ²/(4π²), and weighted averaging gives inf_I F/|q|≤2π√S/ℓ. A pointwise lower bound for the conformal speed is genuinely unnecessary. This is a well-chosen quantitative formulation; it is not just assuming the desired lower speed. Nevertheless, once the existing field and congruence are available, it is one elementary averaging estimate. It resolves a technical parameterization problem, not a new geometric or operator-algebra obstruction.

**Approximate inertia.** The candidate properly avoids declaring ran X and ran Y orthogonal when X*Y is only small. Its minmax argument gives, for a₂=λ₂(XX*) and κ=‖X*Y‖op,

    λ₂(D) ≥ a₂−κ²/a₂,
    a₂ ≤ η+κ,

and the exchanged estimate bounds YY*. This is the natural quantitative version of the same exact inertia proof, using a right inverse on the top two-dimensional spectral space. It is a worthwhile lemma, but short finite-dimensional perturbation algebra once the old mechanism is fixed. No new rank obstruction is overcome after g,ℓ,δ are bounded away from zero.

**Stationary-pair cancellation.** This part materially improves the displayed scalar deficit from a naive ε^(1/4) loss to √ε. But the improvement is the ordinary second-order loss of the bilinear norm functional at a maximal singular pair. For x₀=ax+e,y₀=by+f, e⊥x,f⊥y, both mixed terms vanish because Tx=γy and T*y=γx; thus y₀*Tx₀=γab+f*Te. This requires no singular-value gap and no new Crouzeix-specific structure. It should be used, and should not be advertised as a separate nonroutine advance. It differs from ACV's operator-ball variation, but is an equally elementary stationarity calculation.

**Uniformity.** The uniformity is genuine: fixed d,R,δ,g,ℓ yields an explicit recovery guarantee tending to equality uniformly as ε→0. There is no hidden compactness in m or degree, and the statement is nonvacuous on the known four-dimensional Crabb chain. Poor constants alone do not disqualify it. However, normalization ‖X‖HS=‖Y‖HS=1 and the pre-existing complete energy estimates already avoid coefficient dimension and degree. The new estimates preserve that uniformity; they do not discover it independently. Q3 follows by the usual Schmidt truncation. The normalized active-block extension is a correct scope requirement to assess, not a further substantial theorem.

**Counterexamples.** The doubled-disk/stadium family distinguishes every-pair recovery from mere existence of a good scalar channel and explains necessary degeneracy dependence. It does not establish a sharp rate, remove a restriction or prove a new classification. The output-chain and unused-channel examples protect the scope but were already known diagnostics. They receive no separate finding credit.

## 5. Verdict and what would change it

Taken together, Q1–Q4 make R016 effective on a prescribed uniformly nondegenerate class. They provide useful new-to-project quantitative content, potentially suitable as a stability proposition accompanying R016. The accumulated work is more than a literal substitution ε=0→ε>0, but its conceptual core has already been credited: each remaining operation is a routine quantitative strengthening once that core and the explicitly imposed gaps are supplied. On this task's elevated substantiality rule, that is TECHNICAL rather than SUBSTANTIAL.

KNOWN would overstate the external overlap: I found no matching full recovery statement. UNRESOLVED would obscure that a contribution judgment can be made without worldwide priority certainty or another proof review. The rejected gate is substantiality, not correctness, external novelty certification, or an unstated requirement that every theorem include disk geometry.

No repair to the mathematics of Q1–Q4 is prescribed at this gate, and none was made. A promotion would require additional conceptual content beyond re-optimizing constants or repackaging these lemmas—for example explicit geometric rigidity without an inverse-polynomial assumption, or a robust scalar-channel theorem through support-gap/reducing degeneration (which must distinguish existence from every-pair recovery). Those are examples of an additional result, not claims established here and not an instruction to repair during this review. The original quantitative disk program remains unresolved.

Primary search was bounded and current on 2026-10-12, with full relevant arguments read for the comparisons above. It is not a worldwide priority certificate. Details, read extents, retrieval failures and detached hashes are in the accompanying literature, reading log and authentication JSON. No shared state or candidate proof was edited.
