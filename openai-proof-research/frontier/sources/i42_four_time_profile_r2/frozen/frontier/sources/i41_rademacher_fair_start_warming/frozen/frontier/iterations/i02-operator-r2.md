# Dyadic operator research, round 2

**Status (2026-10-08): the requested substantial advance was not obtained.** The independent audit passes the specified arguments, subject to prior-art and scope qualifications. The exact rank-two existence question remains unresolved: I have neither constructed bounded rank-two U,W satisfying all of (7.1), (7.3), (7.4) for the accepted global S, nor proved that none exist. In particular I have not proved that S is, or is not, finitely multicyclic.

The completed work below consists of elementary structural results and a materially different infinite-rank construction, with its ordinary-invariant-subspace gap exposed. None is offered as a new substantial case of MathDB 315900. No upstream truth audit, staging, commits, shared-index edits, other-project writes or further agents were used.

## 1. Contracts, source retrieval, and early prior-art screen

The working rules are AGENTS.md and frontier/iterations/README.md. The immutable source revision is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The full twelve-file TeX/bibliography source of *Backward intertwiners and a transitive commutant* was downloaded from pinned raw GitHub URLs. Every blob SHA-1 matches sources/preprints-tree.json. Paths, URLs and SHA-256 hashes are in [upstream_manifest.json](../sources/i02_operator_r2/upstream_manifest.json). Relevant actual sources read include `introduction.tex`, `weights.tex`, `criterion.tex`, `intertwiner.tex`, `subspaces.tex`, and `conclusion.tex`; the accepted criterion was used as a premise, not re-proved or audited.

The precise definitions needed below are on `H=L²(Z₂;ℓ²(Z))`, with θx=x+1, Haar probability, c=10, D=100, N_m=2^m, ℓ_m=8^m, ℓ_0=1, I_m=[ℓ_(m−1),ℓ_m)∩Z, J_m=100(N_m−2). For k∈I_m,

`a_k^+(x)=10(k+1)+J_m+100 T_m(x)`,

`a_k^−(x)=10(k+1)+J_m+100(N_m−1−T_m(x))`.

Both a_0^±=10. Set a_j=a_j^+ for j≥0, and a_j=a_(-j−1)^− for j<0; β_j=exp(−a_j). The accepted S sends the basis vector at (x,j) to β_j(x) times that at (x,j+1). Its global power bound is

`||S^n||≤exp(−10 floor((n+1)²/4))≤exp(−(5/2)n²)`.

The accepted V sends (x,j) to (x+1,j−1), with positive a.e. weights b_j≤1. The exact unnormalised recurrence is

`tilde b_0=1`, `tilde b_(j+1)(x)=tilde b_j(x) β_(j−1)(x+1)/β_j(x)`.

On the common conull set X_* from the manuscript, `L(x)=sup_j tilde b_j(x)<∞` and b_j=tilde b_j/L. Off X_* all b_j=0. Uniform lower bounds on b_j and a bounded inverse of V are **not** available. The scalar-multiplier algebra together with S,V is accepted to be transitive. Fixed coordinate tails are ordinary S-invariant subspaces.

**Prior art checked before claiming a construction:** [Tcaciuc 1805.03277v2](https://arxiv.org/abs/1805.03277v2), Lemma 2.1, Theorem 2.3, Proposition 2.4, Theorem 3.3 and Section 4. The results concern rank-one spectral perturbations, with exceptional parameters; Section 4 explicitly supplies the rank-at-most-two similarity trick. They do not themselves answer the present minimal rank-two realization question. [Shkarin 1209.1458v1](https://arxiv.org/abs/1209.1458v1), Corollary 1.5, already proves cyclicity of every scalar quasinilpotent bilateral weighted shift. Its Theorem 1.1 relates cyclicity of a double copy to supercyclicity of a scalar shift. Neither result identifies the multiplicity of this diffuse operator-valued direct integral. Both complete PDFs and text extractions are in [literature_manifest.json](../sources/i02_operator_r2/literature_manifest.json).

A bounded targeted search also inspected finite-rank perturbation and positive-operator results. For example [Abramovich–Aliprantis–Burkinshaw (1994)](https://doi.org/10.1006/jfan.1994.1099) requires compact domination, a commuting kernel operator, or a Dunford–Pettis condition in its stated sample results. Positivity and quasinilpotence alone on the present nonatomic L² space do not verify those additional hypotheses. I did not find a verified general prior-art theorem settling the whole class under study; this is a bounded search result, not a priority claim.

## 2. Audit outcome and the exact rank-two problem

The separate [audit](../reviews/i02-crossfield-r2.md) verifies Proposition R, all requested thresholds and sunflower exclusions, the slope lift, the shadow counterexample, and equations (7.1)–(7.4). It also identifies the exact transversal threshold computation as explicit primary prior art in Shangguan's Section 4.

For `F=UW`, U:C²→H, W:H→C², rank F=2, put

`R(z)=zW(I−zS)^(-1)U`, `D(z)=det(I₂−R(z))`.

If D has a zero, S+F has a nonzero eigenvalue. Otherwise D≡1 by logarithmic-square growth and the zero-free entire-logarithm argument. The coefficient equations are

`tr(WS^(j−1)U)=sum[a+b=j−2] ((WS^aU)11(WS^bU)22−(WS^aU)12(WS^bU)21)`.

The sum is empty for j=1. In addition, absence of ordinary invariant subspaces requires

`C_S(U)=closure span{S^n ran U:n≥0}=H`,

`N_S(W)=intersection[n≥0] ker(WS^n)={0}`.

No determinant-one-to-zero-moments argument is used. The original finite 2×2 example was only reproduced as part of the requested audit; it is not recycled as a candidate for this problem.

## 3. A genuine dyadic symmetry, and what it does not prove

Let ρ(x)=−1−x on Z₂. For every m,

`T_m(ρx)=N_m−1−T_m(x)`.

The actual weights, including the two central weights, therefore satisfy

`β_j(ρx)=β_(−j−1)(x)` for every j.

Define the conjugation (antiunitary involution)

`(Cf)(x,j)=overline{f(ρx,−j)}`.

Checking coordinates gives **CSC=S***. In particular, for every finite integer r, S is r-multicyclic if and only if S* is r-multicyclic: C takes the closed span of `{S^n u_i}` onto the closed span of `{(S*)^n C u_i}`. This is an exact global statement using the dyadic reflection, not a statement about each fibre separately.

Thus an infinite-multiplicity obstruction for either side of (7.3)–(7.4) would apply to both sides. But no such obstruction has been proved. Positive weights make S and S* injective, so the elementary lower bound using the dimension of an adjoint eigenspace gives no information. The fact that each scalar fibre is compact and cyclic does not give a measurable global cyclic vector whose *single scalar polynomial sequence* works in L² across the base. Conversely, the infinite multiplicity of the scalar multiplier algebra does not by itself imply infinite analytic multiplicity for S.

A finite truncation at a coordinate boundary artificially creates zero eigenvectors of infinite base multiplicity. That defect cannot be used as an eigenvector or multiplicity argument for the bilateral injective limit. We did not use finite controllability matrices for a universal inference.

### Finite-rank stability of finite multicyclicity

For any bounded A and finite-rank F of rank r, finite multicyclicity of A and A+F are equivalent. More quantitatively, if A+F has m cyclic generators then A has at most m+r. Adjoin a basis of ran F to the m generators and take its closed A-cyclic span L. Since ran F⊂L, L is also A+F-invariant, so it contains the dense orbit span of the original generators. Reverse A and A+F for the converse.

Likewise `C_A(ran F)=C_(A+F)(ran F)`: either closed cyclic span contains ran F and is invariant for both operators. Applying this to adjoints gives equality of the unobservable kernels when F=UW and W is fixed. These are elementary control identities, not a new invariant-subspace theorem. If S were proved not finitely multicyclic, they would rule out *all* finite-rank attempts: an operator with no nontrivial invariant subspace has every nonzero vector cyclic. The missing premise is exactly the multiplicity assertion about S.

## 4. Why an apparent infinite-multiplicity obstruction fails

The uniform source estimate is

`0≤a_k^±(x)−10(k+1)≤400 k^(1/3)` for k≥1.

Define a fixed scalar forward shift B on ℓ²(Z) by weights

`γ_j=exp(−10(j+1)−400 j^(1/3))` for j≥0,

`γ_j=exp(−10(−j))` for j<0,

where 0^(1/3)=0. Let B_∞ act by B on every base fibre. Put d_0(x)=1 and solve

`d_(j+1)(x)/d_j(x)=γ_j/β_j(x)`.

For j≥0 the ratio is ≤1. For j<0 it is ≥1, so solving backwards also gives 0<d_j≤1. The diagonal multiplication operator J with entries d_j(x) is a contraction, injective, and has dense range: truncate coordinates and then the sets on which each d_j is small. It satisfies

`JS=B_∞J`.

This looked like a way to force an infinite analytic multiplicity. It does not. In fact **B_∞ is supercyclic**, even though its coordinate multiplicity is infinite. Here is a direct verification of the criterion, avoiding a false multiplicity heuristic. Let E be the dense space of finite-coordinate vectors with arbitrary L² base coefficients. The formal inverse B_∞^(-1) maps E to E. For fixed f,g∈E, as n→∞,

`log( ||B_∞^n f|| · ||B_∞^(−n) g|| ) ≤ −300 n^(4/3)+O_(f,g)(n)`

when both are nonzero. The −300 term is `−400 sum[k≤n] k^(1/3)`; the quadratic terms from the positive and negative ends cancel, and fixed endpoint shifts contribute O(n). Thus the product tends to zero. To see supercyclic transitivity directly, take λ_n with

`|λ_n| ||B_∞^n f||→0`, `|λ_n|^(−1)||B_∞^(−n)g||→0`,

and use `f+λ_n^(−1)B_∞^(−n)g→f`, whose scaled n-th image tends to g. The standard countable-base Baire argument then gives a supercyclic vector. This also proves finite multicyclicity of the target without any fibre selection.

The inequality is not a claim that J is invertible, nor that supercyclicity transfers backwards along a dense-range intertwiner. The reverse implication is unavailable. This comparison route therefore supplies no obstruction to (7.3). It was abandoned as soon as that failure was identified.

## 5. Exact similarity realizations, including the minimality trap

The following general construction is exactly the family already noted by Tcaciuc, not a discovery. Let u≠0 and φ≠0 satisfy φ(u)=0. Write N=uφ, so N²=0, and let a=φ(Su). Define

`T=(I−N)S(I+N)=S+F`,

`F=(Su)φ−u(φS+aφ)`.

Choose `U(c₁,c₂)=c₁Su+c₂u` and `Wf=(φ(f),−φ(Sf)−aφ(f))`. Since S and S* are injective and quasinilpotent, neither has an eigenvalue. Therefore u,Su are independent and φ,φS are independent. U is injective and W is onto C², so **rank F=2**. T is similar to S and quasinilpotent. Hence its transfer determinant has no zeros, and the growth argument forces D≡1.

The two minimality conditions simplify exactly:

`C_S(U)=closure span{S^n u:n≥0}`,

`N_S(W)=intersection[n≥0] ker(φS^n)`.

Thus this family is controllable and observable precisely when u is cyclic for S and the representing vector of φ is cyclic for S*.

If S is cyclic, the reflection in Section 3 makes S* cyclic too, and the orthogonality φ(u)=0 can be imposed **without** losing either cyclicity. To check this last point rigorously, start with cyclic u and a cyclic functional φ₀. If φ₀(u)=0, use φ₀. Otherwise the span of `{S^n u:n≥1}` is dense, because S has dense range and u is cyclic. Hence φ₀(S^n u)≠0 for some n≥1. Let `λ=φ₀(S^n u)/φ₀(u)≠0` and set `φ=φ₀(S^n−λI)`. Since S^n−λI is invertible and commutes with S, φ remains a cyclic functional, and φ(u)=0. This proves:

**Conditional diagnostic:** if the global S is cyclic, then the exact rank-two question in Section 7 has an affirmative answer, already within the similarity family.

This conditional statement is a warning about that question's significance, not a solution to its missing cyclicity premise. Every resulting T has the explicit ordinary invariant subspaces

`(I−N)L²(Z₂;span{e_j:j≥h})`, h∈Z.

They are closed, nonzero and proper because I−N is boundedly invertible. Therefore even a future affirmative minimal-realization answer would need to distinguish nonsimilarity constructions and prove substantially more. The original necessary conditions were never sufficient for the ISP.

## 6. Another finite-rank stability fact: Gaussian decay survives determinant one

This observation is valid for every finite rank and uses no dyadic structure. Assume `||Q^n||≤A exp(−c n²)`, let F=UW have rank r, and assume

`det(I_r−zW(I−zQ)^(-1)U)≡1`.

The Woodbury identity is

`(I−z(Q+F))^(-1)=A_z+z A_z U(I_r−zWA_zU)^(-1)W A_z`,

where A_z=(I−zQ)^(-1). The finite matrix inverse is its adjugate, a polynomial of degree at most r−1 in entries of zWA_zU. For R≥1, completion of the square gives `||A_z||≤C exp((log R)²/(4c))` on |z|≤R. Consequently

`max[|z|≤R]||(I−z(Q+F))^(-1)|| ≤ C' R^r exp((r+1)(log R)²/(4c))`.

Cauchy's coefficient inequality and `log R=2c(n−r)/(r+1)` yield, for integers n≥r,

`||(Q+F)^n||≤C' exp(−c(n−r)²/(r+1))`.

For our rank-two problem, c=5/2 gives `||T^n||≤C' exp(−(5/6)(n−2)²)` for n≥2. The constants depend on Q,U,W,r. For n<r one can enlarge the constant. Thus all determinant-one candidates remain in a Gaussian decay class. This is an elementary resolvent estimate and does **not** prove an invariant subspace for the rank-zero member of that class. Applying Proposition R to a further rank-one perturbation of T cannot be reversed to prove an invariant subspace of T.

## 7. A materially different construction: positive infinite-rank coupling

The comparison obstruction failed, and the exact finite-rank candidates presently available were similarities. I therefore tested a new single operator that uses the accepted V with a nonconstant multiplier, at full coupling and without separated diagonal spectra.

Write the 2-adic digits of x as ε_k(x)∈{0,1} and put

`a(x)=1+sum[k≥0] ε_k(x) 2^(−k−1)`, so 1≤a≤2,

`B_a=M_a V`, `T_a=S+B_a`.

This is a concrete bounded positive operator on the complex Banach lattice L²(Z₂×Z). It uses the actual normalized b_j; no finite approximation to L(x) is substituted. Its perturbation B_a has infinite rank: V is injective by positivity of its weights and the invertibility of the base shift, and M_a is invertible. No small-coupling Riesz projection argument is being reused.

### 7.1 An operator-specific estimate for V

For an even 2-adic x, no residue T_m(x) is N_m−1. Thus the exact drift sums in the source, not merely their almost-everywhere estimates, give

`sum[k=0..n−1] Δa_k(x)=100(n−1)`,

`sum[k=−q..−1] Δa_k(x)=−100(q−1)`.

Insert these into the unnormalised b formulas. For j≥1,

`log tilde b_j(x)≤−90(j−1)+400(j−1)^(1/3)`;

for q≥1,

`log tilde b_(−q)(x)≤−90q+100+400q^(1/3)`.

Since L(x)≥1, normalization only decreases b_j. The elementary maximum of `400 t^(1/3)−45t` on t≥0 is less than 460. On the even part of X_*, therefore,

`b_j(x)≤min{1,exp(560−45|j|)}` for all j∈Z.

Off X_* the same inequality holds since b_j=0. All other bases retain the bound b_j≤1.

An n-fold orbit of V has coefficient `product[r=0..n−1] b_(j−r)(x+r)`. At least m=floor(n/2) of these bases are even. Select m successive such visits. Their coordinate indices have spacing 2, and

`min[j∈Z] sum[r=0..m−1] |j−2r|=floor(m²/2)`.

Dropping the remaining factors, each at most 1, proves the **global uniform bound**

`||V^n||≤min{1, exp(560m−45 floor(m²/2))}`, m=floor(n/2).       (V)

In particular `||V^n||≤exp(5000−n²)` for all n≥0. Indeed n≤2m+1 and `floor(m²/2)≥m²/2−1`; adding n² to the exponent leaves at most `−18.5m²+564m+46<5000`. This proof controls the essential supremum over every base and coordinate. Merely knowing that each b_j(x) tends to zero would not have sufficed.

### 7.2 Quasinilpotence of the new operator

A product of the a-multipliers along an orbit is bounded by 2^n, so

`||B_a^n||≤2^n ||V^n||≤exp(5000) 2^n exp(−n²)`.

S commutes with B_a, because it commutes with both V and every scalar multiplier. The binomial theorem and `k²+(n−k)²≥n²/2` give

`||T_a^n||≤exp(5000) 3^n exp(−n²/2)`

`≤exp(5000+(log 3)²) exp(−n²/4)`.

Thus T_a is norm-quasinilpotent with spectrum {0}. There is no spectral splitting to exploit. This also avoids confusing von Neumann generation with analytic recovery: no claim that S,V or M_a can be recovered from polynomials in T_a is made.

### 7.3 No finite-dimensional or finite-codimensional invariant subspaces

One can further exclude the elementary eigenvector alternatives for this exact candidate. The proof uses the actual one-step supports and the uniform even-base estimate above; positivity alone would not prove injectivity of a sum.

If T_a f=0, its coordinates satisfy

`f(x−1,j+2)=r_j(x) f(x,j)`,

`r_j(x)=−β_j(x)/(a(x)b_(j+2)(x−1))`.

On the common invariant conull set all coefficients are finite and nonzero. Pair two consecutive steps. Exactly one of x−1,x−2 is even. For j→+∞, the lower bound

`β_j(x)≥exp(−10(j+1)−400j^(1/3))`

and the upper bound on that even-base b give, uniformly in x,

`log |r_(j+2)(x−1) r_j(x)| ≥ 25j−O(j^(1/3)+1) -> +∞`.      (E1)

Here the two β factors cost `20j+O(j^(1/3)+1)`, while the one even-base reciprocal b supplies at least `45j−O(1)`; both a factors cost at most 2 log 2. This gives a uniform lower bound, including the bases where the other b is exceptionally small.

For clarity about measurability and pointwise orbits, fix parity p∈{0,1}, put j=2k+p and y=x+k. The change of variables identifies that parity component of H with `L²(Z₂_y;ℓ²(Z_k))`, by

`z_k(y)=f(y−k,2k+p)`.

The recurrence is now an ordinary scalar recurrence in k for almost every y. By (E1), every nonzero such sequence grows without bound towards +∞ along pairs of steps. Since its coefficients never vanish, it cannot be square summable. Fubini therefore gives f=0, proving ker T_a={0}.

Similarly, T_a* f=0 gives

`f(x−1,j+2)=r_j^*(x) f(x,j)`,

`r_j^*(x)=−a(x)b_(j+1)(x−1)/β_(j+1)(x−1)`.

For j→−∞ the same pair-of-bases argument gives the uniform upper bound

`log |r_(j+2)^*(x−1) r_j^*(x)| ≤ −25|j|+O(|j|^(1/3)+1) -> −∞`.      (E2)

Both reciprocal β factors cost `20|j|+O(|j|^(1/3)+1)`, while one even-base b saves `45|j|−O(1)`. In the same parity disintegration a nonzero sequence consequently grows without bound towards −∞, by reversing the recurrence. Thus ker T_a*={0}; T_a has dense range.

Since T_a and T_a* are quasinilpotent, zero is their only possible eigenvalue and has now been excluded. A nonzero finite-dimensional invariant subspace would have an eigenvector over C. A proper invariant subspace of finite codimension would give a nonzero finite-dimensional invariant subspace for the adjoint on its orthogonal complement. Neither is possible. **Every nonzero proper closed T_a-invariant subspace, if one exists, is therefore a half-space.** This is still a technical diagnosis of the candidate, not the required invariant-subspace theorem.

### 7.4 Invariant ideals and the remaining ordinary-subspace gap

T_a has **no nonzero proper closed invariant ideal** in this L² lattice. This follows from positivity and the accepted transitive algebra, as follows. If a closed ideal I is T_a-invariant and f∈I is positive, then

`0≤Sf≤T_a f`, `0≤B_a f≤T_a f`.

Solidity of I gives S-invariance and B_a-invariance; modulus inequalities extend this to complex f. Every ideal is invariant under every bounded scalar multiplier, so multiplying by 1/a also gives V-invariance. Accepted transitivity of the algebra generated by S,V and the multipliers forces I=0 or H.

This is a routine consequence of the accepted algebra theorem, **not** an ordinary-invariant-subspace result. A closed linear invariant subspace need not be an ideal: f∈M does not imply |f|∈M or membership of functions dominated by |f|. Neither the domination argument nor transitivity can be applied to such an M. I have not constructed or ruled out the ordinary invariant subspaces of T_a, and I have not proved that T_a is not similar to S by an arbitrary bounded similarity. Similarity by an invertible scalar multiplication or any lattice isomorphism is excluded, since it would transport S's invariant ideals to invariant ideals; that much narrower exclusion is all the proof establishes.

The positive-operator prior-art conditions mentioned in Section 1 have not been verified for T_a. The no-ideal conclusion itself precludes a domination argument that would force a nontrivial invariant ideal under those hypotheses, assuming the accepted premises. It is not evidence that arbitrary closed subspaces are absent.

This construction is therefore a precise alternate candidate and a verified weight estimate, but it does not clear the user's success gate. The exact new missing step is either (a) an ordinary invariant subspace of this specified T_a, or (b) a valid mechanism forcing every T_a-invariant closed subspace to be an ideal/common invariant subspace. Nothing here supplies (b).

## 8. Validation, novelty, and next decision

[checks.py](../experiments/i02_operator_r2/checks.py) and [checks.json](../experiments/i02_operator_r2/checks.json) reproduce the original finite outputs exactly and add 16 exhaustive rational cover-cost checks, 10,240 dyadic reflection identities, 6,432 even-base log estimates, and finite checks of the two integer minimum formulas. These support transcription and algebra only. In particular, they do not approximate the infinite normalizer L(x), prove Gaussian decay by sampling, or establish global cyclicity. Each universal claim in Sections 3–7 has a separate proof above.

**Proof status:** audit complete; dyadic reflection and equal analytic multiplicities proved; finite-rank stability statements proved; conditional minimal similarity family proved; V bound (V) and the specified T_a's Gaussian decay, empty point spectra for it and its adjoint, and no-invariant-ideal properties proved. **Unproved:** finite analytic multiplicity of the global S; simultaneous rank-two determinant-one controllability/observability beyond the conditional similarity family; ordinary invariant-subspace analysis sufficient to settle either operator route.

**Novelty limit:** the similarity mechanism is explicitly Tcaciuc's; finite-rank cyclic-span and adjugate estimates are elementary; the new weight estimate is a technical observation; the no-ideal conclusion is a short consequence of accepted transitivity. None is a substantial new theorem or a substantial new MathDB case. No new accepted finding should be counted from this report.

A continuation must address the global cyclicity issue with a uniform L² argument, or the ordinary invariant-subspace gap for T_a. Rechecking determinant identities, proving fibrewise cyclicity again, or identifying further invariant-ideal obstructions would not resolve either gap.
