# R162CP independent substantial-contribution review

**Verdict: TECHNICAL, conditional on full correctness of the entire unchanged frozen theorem and proof.** This is exclusively a substantial-contribution judgment. It supplies no correctness grade, acceptance decision, count, or worldwide-priority claim. Source177 at pin `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, including its operative proofs, is stipulated true. No correctness review or other review namespace was accessed.

The decisive comparison is with the actual Fourier proof of Khot–Naor, not merely its final quotient nonembedding theorem. Character modulation moves their dual-code support calculation to any affine dual-code coset. For the graph cut group, endpoint characters give exactly the affine classes of edge sets with boundary two specified vertices. Their least Hamming weight is graph distance. Applying the source's weighted cut inequality to the common potential increments then gives the required lower bound for every law on arbitrary sections. The remaining conclusions are covered by a compatible path-cone/chain-homotopy averaging construction, uniform coset transport, and one common uniform cut. This gives a complete source/classical reduction of the full frozen scope. No distinct substantial new operation remains after that reduction.

This conclusion is not based on absence of a search hit, a failed naive argument, or length/elegance of the author proof. The author's lower inequality is useful and its scope matters. The issue is whether its operation survives the strongest compatible reduction. Below I give that reduction, with the common objects and normalizations exposed, and explain why the proposed affine-character distinction does not survive it.

## 1. Fixed scope and source interfaces

I reviewed the entire authorized `STATEMENT.md`, `PROOF.md`, `COMPARISON.md`, `FREEZE.json`, `private/PREFREEZE.md`, `private/DERIVATION.md`, `private/WORKING.md`, `private/READING-LIMITS.md`, and `FINAL.md`. The statement and proof hashes are respectively

- `ebbecfde0342e866f1401764980ccaf1f3f0c08bc1aea5269e217021774594c9`;
- `7331535f72a9c9dbab2da0396af34c78eb0a1065afb5e96d4cfc618a22a052b6`.

All assertions below retain the original Source177 complex: fixed d≥3, N=2d+1, fixed sufficiently large odd prime q, congruence quotients modulo t^m, original common-intersection coset complex and its d-skeleton, F₂ coefficients, and intrinsic weights. There is no subdivision, replacement by an irreducible-polynomial quotient, change of coefficient group, weaker marginal requirement, or restriction to linear sections in the lower bound. The estimates are simultaneous for all m in a tail, with constants depending only on d,q. The two-law identities retain every m≥2. No algorithmic conclusion is added.

For a fixed m write H=X_m(1), V=|X_m(0)|, E=|X_m(1)|, A=F₂^E, B=im δ₀, and Z=im δ₁. The source gives connectedness, ker δ₁=B, and expansion at the displayed intrinsic weights. Fix a source constant ε_* >0 depending only on d,q. It supplies both

    ||δ₀h||₁ ≥ ε_* min(||h||₀, ||1+h||₀),
    min_{δ₁f=z} ||f||₁ ≤ ε_*⁻¹ ||z||₂.

The theorem's two-law upper bound holds with any admissible ε as stated. For the asymptotic constants it is enough to fix ε_*. There is no dependence on an arbitrarily weakened presentation of ε.

The source's incidence bound D and purity give graph degree at most Δ=dD, and

    1/(DV) ≤ w₀(v) ≤ D/V,
    Σ_{e containing v} w₁(e)=2w₀(v),
    Σ_{τ containing e} w₂(τ)=3w₁(e).

In particular Σ_e ||δ₁1_e||₂=3. These identities use the actual normalized weights, not uniform edge weights substituted for them.

The source quotient group acts on faces, preserving all intrinsic weights. For a type set J let c_J be the stabilizer order. Source intersections give 1≤c_J≤M=q^(N choose 2), independent of m, and the orbit size is |G_m|/c_J. For an edge type J its total weight is

    α_J = [Σ_{K⊃J, |K|=d+1} 1/c_K]
          / [binom(d+1,2) Σ_{|K|=d+1} 1/c_K].

Consequently α_J≥α>0 depending only on d,q; for example α=[M binom(d+1,2) binom(N,d+1)]⁻¹ suffices. Full edge transitivity is unnecessary. This is the exact source-symmetry interface needed by the upper bound.

The full nine source texts, including wrapper, all operative includes, references and figure code, were read. Their ten associated blobs were independently authenticated against the complete tree metadata and stipulated pin. This identifies the interfaces; it is not an upstream truth audit.

## 2. Uniform coset transport and common uniformization

Each fiber is an affine B-coset. If δ₁a=z+z', translating f by a maps the uniform law on F_z to the uniform law on F_z'. Choose a of minimum weighted norm. This gives a coupling with constant cost Q(z+z'). Conversely every pair (f,f') from these fibers has δ₁(f+f')=z+z', and hence cost at least Q(z+z'). Thus

    W₁(μ_z,μ_z')=Q(z+z').

This is exactly the translate-a-minimizing-pair argument in Khot–Naor Lemma 3.6 (PDF p.10), with the same finite-group cosets and a translation-invariant metric. Weighted Hamming cost changes no step. The triangle incidence identity gives ||δ₁f||₂≤3||f||₁, and the source cofilling inequality gives the other direction. This pays the all-m identity and both source-scale bounds.

There is a further elementary compatibility observation. For ANY law on sections, choose one independent uniform b∈B and replace every output s(z) by s(z)+b. Conditional on s, each output is uniform on its required fiber; every pair difference is unchanged. Thus the unrestricted and exact-uniform objectives S and U have equal infima for this family. I use this equality internally to compare the specified optimizations; it is not a proposed replacement theorem or additional nominee. In particular, enforcing every uniform marginal simultaneously adds no operation once a common section law exists. For the linear upper law below, the same translation gives precisely the required affine support. Nonzero s(0) causes no difficulty.

For any uniform law, Q≤ε_*⁻¹||·||₂ implies its R-objective is at least ε_* times its source-scale objective. Thus the lower bound for arbitrary section laws also pays the required lower bound on R. The upper construction will control the sharper denominator Q directly.

## 3. The strongest compatible KN reduction of the lower bound

### 3.1 The translated support calculation is already in the Fourier interface

Let K=B^⊥ in the edge cube; under the graph boundary map ∂ this is the cycle space ker ∂. Write W_a(x)=(-1)^{⟨a,x⟩}. Suppose a real function F on A obeys

    F(x+b)=W_a(b)F(x)  for every b∈B.

Then W_aF is B-invariant. The proof of Khot–Naor Lemma 3.3 (PDF pp.7–8) puts its Fourier support in K. Multiplication by W_a translates Fourier support, so

    supp F̂ ⊂ a+K.

This is the same Walsh diagonalization in another character component. Using KN equation (1), with ∂_eF=(F(x)-F(x+1_e))/2, Parseval gives

    Σ_e E_x |∂_eF(x)|²
      = Σ_c |c| F̂(c)²
      ≥ min_{c∈a+K}|c| · E_x|F(x)|².                 (1)

There is no new spectral estimate here. One must apply the identity to F itself: applying an invariant Poincaré bound blindly to W_aF and forgetting the changed derivatives would be wrong. Formula (1) explicitly accounts for the translation and needs no mean-zero premise. This is stronger than trying to use only the minimum nonzero weight in K.

For vertices u,v, the cut-group character

    λ_uv(δ₀h)=(-1)^{h(u)+h(v)}

is well defined because H is connected. An extension a is any u–v path. The class a+K consists exactly of edge sets with boundary u+v. Every such set has a component containing both odd-degree vertices, and thus contains a u–v path; a shortest path attains the bound. Therefore

    min_{c∈a+K}|c|=dist_H(u,v).                      (2)

For u=v both sides are zero and the trivial character is harmless. Equations (1)–(2) are the classical dual-code argument with a character twist and the elementary parity description of graph boundaries. The existence of triangles makes min(K\{0}) small, but has no adverse effect on these prescribed-boundary cosets.

### 3.2 Apply the calculation to every section, with no seed-dependent pair

Fix any section s, with no linearity, marginal, or s(0)=0 condition. Put

    p_s(x)=x+s(δ₁x) ∈ B.

It satisfies p_s(x+b)=p_s(x)+b. It is an equivariant map onto B; if s(0)≠0 it is not literally the identity on B. Subtracting that fixed cut normalizes it to a retraction, but no normalization is needed below. Choose a root and the unique root-zero potential g_s(x) with δ₀g_s(x)=p_s(x). Define

    F_uv(x)=(-1)^{g_s(x)(u)+g_s(x)(v)}.

These signs have exactly the equivariance used in (1), and |F_uv|=1. Hence

    Σ_e Pr_x[F_uv(x+1_e)≠F_uv(x)] ≥ dist_H(u,v).      (3)

The measure on x is uniform on A and the sum over input edges is counting measure. The vertex and output-cochain weights enter in the next step, not in this Fourier identity.

For fixed x,e let h=g_s(x)+g_s(x+1_e). If t=||h||₀, two independent w₀-distributed vertices are separated by h with probability 2t(1-t). Source degree-zero expansion gives

    2t(1-t) ≤ 2 min(t,1-t) ≤ (2/ε_*)||δ₀h||₁.

Moreover

    δ₀h = 1_e+s(δ₁x)+s(δ₁x+δ₁1_e).

Average (3) over u,v with weights w₀(u)w₀(v), then over x, and sum e. With D̄=Σ_{u,v}w₀(u)w₀(v)dist_H(u,v), the triangle inequality gives the single deterministic-section inequality

    D̄ ≤ (2/ε_*)[1+Σ_e E_{z uniform on Z}
                    ||s(z)+s(z+δ₁1_e)||₁].        (4)

Uniform x pushes to uniform z because all fibers have the same cardinality. The constant 1 is Σ_e w₁(e). This conversion is where the common potential and the source's actual weights matter; no unweighted-output surrogate is introduced.

Now average (4) over an arbitrary law P on all sections. For each fixed z and e, the expected summand is bounded by L(P)||δ₁1_e||₂ (and is zero if δ₁1_e=0). Using the exact sum 3 gives

    L(P) ≥ ε_* D̄/6 − 1/3.                         (5)

This uses a single inequality valid for every deterministic section, followed by linear averaging. It does not select a bad pair after observing a random seed, exchange a maximum with an expectation, assume independence between section outputs, or require affine sections. Thus it covers precisely the all-law quantifier that distinguishes the frozen statement from scalar filling.

Bounded degree and w₀(v)≤D/V imply that an r-ball has w₀-mass at most D(Δ+1)^{r+1}/V. Choosing r a fixed positive multiple of log V makes this at most 1/2 for large V, uniformly in the center. It follows that D̄≥r/2≥c₀log V. Source growth V_m→∞ permits one m₀. Equation (5) proves the required unrestricted lower scale; Section 2 transfers it to U and R with the stated constants and scope.

### 3.3 Why the author's L₁ distinction does not isolate a new operation

The author is right about the ordinary syndrome metric: Q(z+z') is uniformly equivalent to ||z+z'||₂, a weighted Hamming/L₁ metric. KN's final nonembedding conclusion for a different code quotient, or Li–Anantharam Proposition 42 applied indiscriminately, cannot prove this lower bound. The ordinary invariant Fourier support K also has triangles and gives no logarithmic minimum distance. Both objections to those naive applications are valid.

They do not exhaust the actual KN proof. Prescribed-character equivariance is reduced to invariance by multiplication by a character; the exact derivative identity then gives (1) with the affine support. Endpoint characters are the canonical characters of the cut group, and (2) is the standard path/boundary interpretation of the corresponding cosets. Evaluating those characters on the equivariant map p_s is the direct way to use a section in this representation. The remaining passage is the source's existing cut Poincaré inequality and finite averaging. It introduces no new Fourier inequality, expansion principle, nonlinear stability theorem, extension theorem, or minimax argument. The full all-law scope survives this reduction rather than being discarded. This is the specific reason the proposed affine-character sensitivity operation is technically derived rather than a distinct substantial contribution in this review.

## 4. A compatible source/classical construction for all upper conclusions

Degree-zero expansion also bounds graph diameter by O_{d,q}(log V). For a vertex set of mass at most 1/2, its crossing-edge weight is at least ε_* times its mass. The total weight of edges entering the new outside vertices is at most twice their vertex mass, by Σ_{e∋v}w₁(e)=2w₀(v). Thus ball mass grows by a factor at least 1+ε_*/2 until it exceeds 1/2. The lower bound w₀(v)≥1/(DV) makes the number of steps O(log V). Two such balls intersect. A breadth-first tree T therefore has root radius R=O(log V).

Take the integral graph path cone H₀(v)=the oriented root-to-v path in T, as in the degree-zero example in Oppenheim–Valentiner-Branth, and reduce modulo 2. Its dual sends an edge cochain f to the vertex potential obtained by integrating along tree paths. Define

    Q_T f = f+δ₀H₀* f.

It kills B and satisfies δ₁Q_Tf=δ₁f. Consequently Q_T descends to a linear section ℓ_T:Z→A. For each output edge b its row in Q_T is the fundamental cycle b+path_T(endpoints of b), of length at most 2R+1. Hence

    Σ_{input e} ||Q_T1_e||₁
       = Σ_{output b} w₁(b)|fundamental cycle_b|
       ≤ 2R+1.                                    (6)

The same operation fits the stronger chain-homotopy interface literally. Since H₁(X;F₂)=0, choose a triangle filling H₁(b) of each fundamental cycle, so ∂H₁+H₀∂=Id on edge chains. On exact z=δ₁f, the dual satisfies H₁*z=Q_Tf. Thus large or uncontrolled filling areas do not enter (6); exactness cancels them. No global integral contraction or bounded triangle-filling radius has been assumed.

Conjugate Q_T by a uniformly chosen source group element γ. For an input edge e of type J, invariance of the weights and uniformity on its orbit yield

    E_γ ||Q_γ1_e||₁ ≤ (2R+1)/|O_J|
                     ≤ (2R+1) w₁(e)/α.

For every f, the F₂ support union bound then gives

    E_γ ||Q_γf||₁ ≤ K||f||₁,   K=(2R+1)/α=O(log V).

The law of γ is one law chosen for all inputs. For each z,z' a minimum primitive of z+z' can be used to estimate this already fixed linear map, so

    E_γ ||ℓ_γ(z)+ℓ_γ(z')||₁ ≤ KQ(z+z').            (7)

Source cofilling converts (7) to the S and U source-scale upper bounds, while the exact transport identity makes it the R upper bound directly. Adding one independent common uniform b∈B gives the required affine sections and exact μ_z marginal for every z. Equations (6)–(7) use actual finite type-orbit masses, so they do not silently impose edge transitivity. All maps operate on the original complex and all syndromes. This construction does not conflict with, or alter the hypotheses needed for, the lower bound.

## 5. Stronger primary interfaces actually compared

The following are comparisons with operative proofs, not a claim that their final theorem statements literally restate R162CP. The explicit reductions above supply the compatibility work.

**OVB integral cones, averaging, and nonabelian companion.** In [OVB v2](https://arxiv.org/pdf/2504.05823v2), normalized weights, cone equations, integral-to-abelian passage, symmetry estimates, join constructions, and vertex-layer extension are all operative. Example 2.6 (PDF pp.9–10) includes the graph path cone. Proposition 2.7 and Theorems 2.9–2.10 (pp.10–12) connect cones, coefficients, and averaging. Proposition 2.15 (pp.14–15) and Theorem 3.1 (pp.16–17) give actual extension formulas. In the independent-vertex layer, the new cone on [w,σ] is the old cone of the link cone of σ minus [w,link cone of σ]; its radius is controlled by a product of the old and link radii. The type-A construction through Corollary 6.10 (pp.28–33), not just the abstract, was read.

These are substantially stronger than an existential scalar coisoperimetric constant, and they already pay linear cone operations and averaging. Their local link contractions cannot automatically be called a global constant-congestion primitive map for these growing graphs. But that failure does not leave the upper bound unpaid: the global path cone, exact-image dualization and finite-orbit calculation above give the required logarithm within the same framework.

The [nonabelian companion v1](https://arxiv.org/pdf/2510.18351v1) was also checked for its actual normal-generation and quotient assumptions, path/contraction operations, joins, vertex layers and local-to-global argument. Its irreducible-polynomial congruence argument uses t invertible modulo that polynomial and its coefficient hypotheses have content. It cannot be substituted for the t^m source quotients. This limitation is not used to deny its stronger cone/correction operations, nor to infer novelty. The source supplies the exact t^m interfaces required here. No coefficient or monodromy assertion is imported.

**DD correction and short cones.** I retrieved the [full DD v3](https://arxiv.org/pdf/2304.01608v3), rather than treating the conference version's deferred proofs as verified. Algorithm 3.3 and Claims 3.4–3.8 (PDF pp.16–18) perform star corrections, prove termination by strict decrease of violated constraints, and telescope the repair cost against syndrome decrease. Lemmas 3.9–3.11 and the proof of Theorem 3.1 (pp.18–23) give the actual local-to-global control. The short-cone proof through Theorem 5.4 and its supporting construction (pp.29–37) supplies considerably more than a scalar assertion: shifted cone operators and star decompositions, rank/support bounds, duality, and symmetry averaging.

It would be too weak to dismiss DD merely because a naive separately chosen correction is not joint. In the abelian setting, fixed tie-breaking can select correction increments as a function of the current syndrome; starting from a given syndrome therefore gives a common, possibly nonlinear selector, with equivariance under cocycles. Where the small-syndrome correction theorem applies this gives an individual norm estimate; source cofilling can supply a choice elsewhere. However, the telescoping proof bounds the distance from each input to its corrected cocycle. It supplies no bound of the form ||c(z)+c(z')||≤C||z+z'|| when both syndromes are large and close. Running identical randomness is not such a bound. The lower bound does not assert that DD cannot select one common function; it concerns the sensitivity of any such function. That sensitivity is paid here by Sections 3–4, not declared new because DD stops at an individual estimate. The unrestricted theorem does not depend on unverified portions of DD's color-restriction proof.

**KoM stochastic chain homotopies.** [Kozlov–Meshulam v1](https://arxiv.org/pdf/1802.03210v1), Theorem 2.5 and its proof (PDF pp.6–7), explicitly dualize chain homotopies, use δT+Tδ=Id, and average their incidence congestion. This is already a common random linear primitive map, not an unrelated scalar statement. Its displayed counting norms are not the frozen intrinsic weights; equation (6), followed by the α_J estimate, is the explicit weighted adaptation. Restriction of H₁* to exact inputs eliminates any need to control arbitrary filling coefficients. There is no conflict between this classical framework and the simultaneous all-syndrome upper law.

**KN coset transport, support, and transitivity.** [Khot–Naor](https://cs.nyu.edu/~khot/papers/nonembed-final-new.pdf), equation (1), Lemma 2.1, Lemma 3.3, Theorem 3.4, Lemma 3.6 and Corollary 3.7 (PDF pp.5–10), were read in their proofs, together with the subsequent transitive-invariance discussion. Lemma 3.6 pays the exact pair transport identity; the earlier support calculation pays (1). The argument above does not incorrectly identify cycle-space minimum distance with graph diameter or replace the actual fibers by a different code. The source-weighted graph comparison is performed after the unweighted cube Fourier calculation. This resolves both the weighted-cost and the ordinary-L₁ objections.

**LA v2 simultaneous lifting: upper and lower proofs.** [Li–Anantharam v2](https://arxiv.org/pdf/1908.01388v2) studies precisely a common random lifting with prescribed marginals and pairwise transport denominators. Definition 19, the Poisson/sequential constructions, Lemma 27, the complete finite-ground-space Theorem 15 proof (PDF pp.23–32), and the deferred Lemma 26 proof in Appendix D (pp.62–65) provide an actual simultaneous upper coupling, not merely independent pairwise couplings. For clarity, its finite-ground Poisson input can also be checked without any untraced ancestral theorem: take independent Exp(1) clocks T_i and choose argmin T_i/p_i. The winner has law p. For two laws p,q, the probability that both select i is [Σ_j max(p_j/p_i,q_j/q_i)]⁻¹ when p_iq_i>0, by integrating the density of T_i; it is zero otherwise. If t is their total variation distance, summing and bounding each denominator by (1+t)/min(p_i,q_i) gives disagreement at most 2t/(1+t)≤2t. Independent clocks at successive stages and induction give the prescribed sequential marginals. The complete Appendix D proof additionally handles the infinite initial-index limit using its stated summability conditions and total-variation approximation. Thus common randomness and marginal correctness, rather than only pairwise existence, are credited. The finite-family upper construction in Appendix J (pp.87–88) glues pair couplings on a random tree. Direct application gives O(log |A|) or O(log |Z|), which here is O(V): E=Θ(V), dim Z=E−V+1=Θ(V), by bounded degree, connectedness and purity with d≥3. Their existence does not supply the sharper log V bound by simply relabeling the family. The structural path-cone construction above supplies that improvement without a new transport coupling theorem.

For the lower comparison I read the deleted-point and frustrated-cycle arguments of Propositions 34–35 (pp.45–49), the lifting-to-L₁ proof of Proposition 40 (pp.54–55), the cube lower bound Proposition 42 (p.58), and the substantial discrete-torus/deleted-point lower argument in Appendix G.1 (pp.72–77). These are genuine common-coupling obstructions; they were not dismissed merely because one generic embedding test fails. The deleted-point families have overlapping supports and their lower proofs exploit that structure. The prescribed family here has disjoint uniform affine-coset supports. No direct identification of those objects is available. Proposition 42 obtains its cube obstruction from KN nonembedding for an appropriate larger family, so it does not automatically restrict to these L₁-comparable syndromes. Proposition 39 and the ensuing discussion already distinguish distribution-preserving lifting from an arbitrary L₁ embedding; the author's L₁ distinction is therefore also part of the antecedent conceptual framework. The stronger Fourier calculation in Section 3 supplies the compatible obstruction for this particular family. No claim that LA alone contains the precise graph lower bound is needed.

## 6. Contribution decision and remaining limits

The assembled derivation covers all frozen conclusions at once: the original source family and weights; all m for pair identities; a uniform tail for the sharp logarithmic asymptotics; all arbitrary nonlinear section laws in the lower bound; one common linear upper law; one common uniform cut giving the affine exact marginals; and both normalizations of sensitivity. No repair or narrowed substitute is used.

The only plausible candidate for a distinct operation after source, transport and upper-bound payment is the affine-character lower inequality. Its support step is precisely a character modulation of the actual KN invariant-support proof, with the same Parseval identity. The affine minimum is ordinary shortest-path length. The use of a section is the standard equivariant map x↦x+s(δx), and the final comparison is the existing weighted cut inequality followed by averaging. All-law validity follows from the deterministic inequality without a further selection or minimax theorem. These concrete reductions are why I judge the residual work technical. The result may be a useful and well-organized synthesis; neither usefulness nor a long proof makes this particular classical composition a distinct substantial operation under the assigned criterion.

There is **no unresolved essential comparison obligation for this conditional TECHNICAL decision**: the explicit reduction does not depend on an unread external theorem. This does not certify exhaustive ancestry. I did not perform an optional original-history traversal, did not read every page of each primary, and did not trace every reference cited inside those primaries (including FRT and all Poisson-matching ancestry). Those limits are itemized in `READING-LIMITS.md`. Such ancestry could strengthen the technical assessment; it is not being used to assert a surviving novel operation. No worldwide or project-history clearance is claimed.

The conclusion assumes the entire frozen theorem and proof are correct as required. The mathematical reconstruction here serves contribution comparison only; it is not a second correctness verdict. Integrity authentication likewise supplies no mathematical grade.
