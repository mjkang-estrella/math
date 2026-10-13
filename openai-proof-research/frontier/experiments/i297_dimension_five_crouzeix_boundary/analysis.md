# I297 — the dimension-five boundary for attained complete equality

**Outcome: E5 is proved, relative to the stipulated complete bound, the reviewed dimension-free equality mechanism of R016, and the credited scalar rigidity/interpolation inputs. The smallest base dimension of failure of same-witness constant scalar compression is therefore exactly six, using R019 for existence. This is a research deduction, not an acceptance or contribution-gate verdict. Count 13/20 is unchanged.**

The primary collision is decisive and old: Leake–Lins–Spitkovsky, *Pre-images of boundary points of the numerical range*, Operators and Matrices 8 (2014), 699–724, [Theorem 5.7](https://files.ele-math.com/articles/oam-08-39.pdf), excludes more than two multiply generated round boundary points for a unitarily irreducible 5-by-5 matrix. Its statement, proof, and supporting Lemmas 5.1, 5.2, 5.8, 5.9 were read. One cannot nominate the needed size-five pencil fact as new. The analytic passage from support multiplicity to round points is supplied below, rather than inferred from a characteristic factorization.

## 1. Exact theorem and dependencies

Let 1≤n≤5, A∈M_n(C), m≥1 finite, and P(z)=Σ z^j C_j∈M_m(C)[z] of arbitrary finite degree. Use Euclidean norms and P[A]=Σ A^j⊗C_j. Put M=max_{z∈W(A)}||P(z)||>0. If ||P[A]||=2M, then there are constant unit u,v∈C^m such that

    p(z)=v*P(z)u,
    ||p(A)||=2M,             max_{W(A)}|p|=M.

Moreover W(A)=a+ρ Dbar with ρ>0 and

    p(a+ρz)=Mη z^k,         |η|=1, 1≤k≤deg P.

There is no genericity, simple ordinary spectrum, unitary irreducibility, degree bound, or coefficient-size bound in this theorem. It concerns the specified P. It asserts no strict scalar-supremum gap, rational-witness theorem, nonattained complete-supremum rigidity, or near-equality modulus.

Dependencies, kept distinct:

1. All OpenAI results at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true. The direct complete theorem supplies the bound, Faber coefficients, original positive resolvent, ordered tests, and nonnegative residuals. The structural companion's density for a similar matrix is not used as the original field.
2. I242's **completed Sections 1–3** and I245's detailed check are dimension-free: their limiting field and isotropy argument have no d≤4 hypothesis. Section 4 alone supplies the old d≤4 pencil step. I297 reads and reuses that interface; it does not infer a dimension-five theorem merely from R016's statement.
3. The 2014 theorem supplies the missing size-five pencil restriction. No general Kippenhahn reducibility conjecture is invoked.
4. Jin v2 Theorem 1 and Lemma 4 are the credited scalar disk and finite-interpolation inputs already used in R016. Their actual statement, Lemma 4 proof, and final Theorem 1 proof were reread in the completed retained primary extraction. Earlier internal proofs supporting Jin's final theorem are not claimed newly audited here.
5. R019/I287, authenticated at the supplied hash and with completed I291/I292 reviews, supplies the dimension-six counterexample. Its truth is reused; no new construction is claimed.

## 2. Generic support intervals without a simple-spectrum assumption

We first establish the precise geometry needed to apply the old theorem. Let B=H_0+iK_0 be unitarily irreducible of size d≥2 and set

    T(θ)=Re(e^{-iθ}B)=cosθ H_0+sinθ K_0.

Outside finitely many directions, its distinct eigenvalues, their orthogonal projections, and their multiplicities are analytic and the multiplicities are constant on each interval. Here is an algebraic justification covering permanently repeated eigenvalues. In a chart with cosθ≠0, use t=tanθ and the polynomial

    c(t,s)=det(sI-H_0-tK_0).

Take its square-free part over C(t). Characteristic zero makes the discriminant of that square-free polynomial nonzero as a rational function of t. Exclude its finitely many real zeros and poles and the poles of the coefficients. Each distinct root is then analytic by the implicit-function theorem; the original c assigns it a fixed multiplicity. Orthogonal spectral projections are analytic, for example by the product formula in the distinct roots, or a small resolvent contour. The chart boundaries add finitely many directions. A second chart or continuity handles them. Thus the excluded set is finite, even when the ordinary discriminant of c vanishes identically. This argument gives no common eigenvector from a linear factor.

On a remaining interval let λ be the largest eigenvalue, E its orthogonal projection, r=rank E, and F_j the projections of the other distinct eigenvalues μ_j<λ. Differentiating T E=λE and sandwiching with E gives

    E T' E=λ' E.

Define the positive reduced resolvent S=Σ_j (λ-μ_j)^{-1}F_j on E⊥. The same differentiated equation gives

    (I-E)E'E=S T'E.

Differentiating E T'E=λ'E once more and using T''=-T and E E'E=0 gives the operator identity

    (λ+λ'') E=2 E T' S T' E.                         (G)

This holds for a repeated top eigenvalue: it is a projection identity, not a simple-eigenvector formula. The right side is positive semidefinite. If λ+λ''=0, then (I-E)T'E=0. Together with E T'E=λ'E, every vector of ran E is a common eigenvector of T and T', hence of H_0,K_0 and B,B*. This contradicts irreducibility. The case E=I on an interval would already make both Hermitian generators scalar. Consequently

    λ+λ''>0.

For every unit ξ∈ran E, the identities B=e^{iθ}(T+iT') and E T'E=λ'E give

    ξ*Bξ=z(θ):=e^{iθ}(λ+iλ').

The face on the supporting line is therefore the singleton z(θ). Its derivative is

    z'(θ)=i e^{iθ}(λ+λ''),

so it parametrizes a regular real-analytic curved exposed arc. In particular its points are round in the 2014 paper's definition: they are neither corners nor relative-interior points of flat portions. If r≥2, every point on this arc has at least two linearly independent unit preimages, and is multiply generated. Strictly positive curvature makes the arc contain infinitely many distinct points.

This pays the essential distinction: an isolated repeated support eigenvalue may give a flat segment, but a branch whose maximal multiplicity persists on an interval yields the curved multiply generated arc above. No polygon or flat-boundary exception survives this argument for an irreducible B.

## 3. The size-five pencil obstruction is impossible

Suppose an irreducible B∈M_5(C) had no simple maximal eigenvalue in any support direction. On any interval from Section 2, r≥2. Section 2 then produces infinitely many multiply generated round boundary points. This contradicts Leake–Lins–Spitkovsky Theorem 5.7, which permits at most two for an irreducible 5-by-5 matrix.

In fact every generic support interval has r=1: even one interval with r≥2 would contradict that theorem. Hence an open regular arc with simple maximal support eigenvalue exists. For d≤4 the reviewed elementary argument of I242 Section 4 supplies such an arc. Equivalently the 2014 Theorems 3.2 and 4.1 give stronger finite-point restrictions in those dimensions.

The attempted `(2,1,2)` obstruction is therefore eliminated at the level of maximal support geometry, before constructing any equality witness. A claim that the pencil determinant is Q²L, or that such a factorization forces a reducing subspace, is unnecessary. Odd-dimensional spin pencils do not invalidate this proof: the proof never turns a linear eigenvalue branch into a fixed eigenvector. The common-eigenvector conclusion above follows only when the explicitly positive curvature identity (G) vanishes.

## 4. Transfer to the original positive boundary field

Normalize M=1. Decompose A into unitarily irreducible reducing blocks and select B with ||P[B]||=2. The stipulated bound gives

    2=||P[B]||≤2 max_{W(B)}||P||≤2,

so max_{W(B)}||P||=1. A one-dimensional block cannot be active. An irreducible block of dimension d≥2 has W(B) with interior and σ(B)⊂int W(B): a boundary eigenvector lies in the kernel of a positive supporting slack and is also an adjoint eigenvector, giving a reducing line.

Fix **any** unit top singular pair P[B]x=2y, P[B]*y=2x and write x=vec(X), y=vec(Y) in base-first order, with X,Y of size d-by-m. The reviewed dimension-free boundary passage gives

    X*Y=0,
    D=XX*-YY*,
    H(t)≥0,
    H(t)^{1/2}D H(t)^{1/2}=0 a.e.                     (E)

Here R=q(hI-B)^{-1}, H=R+R*, h is the exterior map of W(B), and q=wh'(w). This is the **original** mass-two field. To specify what is being reused: for shrinking analytic convex outer domains, the exterior Herglotz formula gives |h'_j|≤4c_j, r≤c_j≤R, and strong boundary L² convergence via square-summable logarithmic Fourier tails. Interior spectrum bounds the fixed resolvent. Thus R_j→R strongly in L² and the fixed-pair forward coefficient energies stay bounded. The exact residual identity is

    E_X,j+E_Y,j+E_B,j+2T_j
       =2(4/γ_j²-1)a_j² →0,
    T_j=3||Y*X||_HS²+Σ_{k≥1}||X*b_{k,j}(B)Y||_HS²≥0.

Its nonnegative terms give orthogonality and zero positive-block slack. Expanding the difference of tr(H_jDH_jD) and tr(HDHD) passes the quadratic quantity in L¹; its zero integral gives (E). These steps apply for every fixed finite d,m and degree, not just d≤4.

On any reflected regular boundary arc the congruence is

    (hI-B)*H(hI-B)=2|q|[sI-Re(barν B)],

with ν=q/|q| the outward unit normal and s=Re(barν h). If the maximal support multiplicity is r, then rank H=d-r. Orthogonality makes the inertia of D exactly (p,q_0,d-p-q_0), where p=rank X≥1 and q_0=rank Y≥1. A totally isotropic subspace for D has dimension at most d-max(p,q_0). Hence, on an arc where r is constant,

    max(p,q_0)≤r.                                    (R)

The almost-everywhere statement causes no loss: the exterior map reflects with nonzero derivative over the regular arc, whose preimage is an open circle interval of positive measure. The rank inequality applies at a point of that interval. There is no substitution of the similar matrix's normalized density for H.

For d≤5, Section 3 gives an arc with r=1. Therefore p=q_0=1 for every chosen top singular pair. Write X=ξu^T and Y=ηv^T with unit factors; the transpose is required by base-first vectorization. Then x=ξ⊗u, y=η⊗v and

    η*(v*Pu)(B)ξ=y*P[B]x=2.

The polynomial p=v*Pu has |p|≤||P|| on the **full** W(A). The scalar bound gives ||p(B)||=2 and max_{W(B)}|p|=1. Thus this is precisely a constant coefficient compression of the original witness.

## 5. Disk geometry and reducible outer summands

Jin v2 Theorem 1 applies to the scalar witness just constructed and gives W(B)=a+ρDbar, ρ>0. Put T=(B-aI)/ρ and g(z)=p(a+ρz). Then σ(T)⊂D, ||g(T)||=2, and max_Dbar |g|=1.

The finite contiguous spectral jets determining g(T) have minimum Schur interpolation norm one. Indeed, if an interpolant f had norm c<1, its radial dilates f(rz) are holomorphic near Dbar and bounded by c there. Polynomial approximation and the stipulated scalar bound give ||f(rT)||≤2c. Convergence of the finitely many interior jets as r↑1 gives ||g(T)||≤2c<2, a contradiction. Jin's Lemma 4 therefore makes the Schur interpolant unique and a finite Blaschke product. Since g itself is a polynomial, no nonzero Blaschke zero is possible: its reciprocal reflected pole lies outside D and cannot cancel a numerator zero inside D. Thus g=ηz^k, |η|=1, k≥1.

The global polynomial identity p(z)=η((z-a)/ρ)^k and |p|≤1 on W(A) force W(A)⊂a+ρDbar. The reverse inclusion follows from W(B)⊂W(A). Also ||p(A)||≥||p(B)||=2, while the scalar bound gives the reverse inequality. Rescaling restores M. This proves E5, including reducible A and the outer numerical-range geometry. No claim that a top singular vector of the entire reducible A must be a product vector is made.

## 6. A wider complete boundary statement: the Schmidt-rank ceiling

To seek more than the immediate old size-five pencil extension, the same original-field method gives the following additional structural statement. It is proved here but receives no independent novelty or substantiality verdict.

**Proposition.** Let B∈M_d(C) be unitarily irreducible, d≥3, and let P be any finite square matrix polynomial with max_{W(B)}||P||=1 and ||P[B]||=2. For **every** unit maximal singular pair, its input and output Schmidt ranks p,q_0 satisfy

    max(p,q_0)≤floor((d-1)/2).                         (C)

For d=2 they both equal one. For d=5 the stronger conclusion p=q_0=1 follows from Section 3.

**Proof.** Put k=max(p,q_0). The dimension-free equality system applies to this fixed pair. Section 2 supplies regular curved arcs for every generic support interval. Inequality (R) makes the top support multiplicity at least k on each such interval. Applying the same assertion at θ+π makes the bottom multiplicity at least k outside a finite set. Top and bottom eigenspaces are distinct on these intervals; otherwise B would be scalar. Hence 2k≤d.

If 2k<d, (C) follows. Suppose 2k=d. Since d≥3, k≥2. Every generic T(θ) then has exactly two eigenvalues, each of multiplicity k. Center B by tr(B)/d. Its centered support pencil T_c(θ) has eigenvalues ±s(θ), and thus T_c(θ)² is scalar. By continuity this identity holds in every direction. Write the centered B=H_c+iK_c. Evaluating at 0, π/2, π/4 yields

    H_c²=αI, K_c²=βI,
    H_cK_c+K_cH_c=2cI,

where α,β≥0 and c is real. If H_c=0, B is normal and reducible. Otherwise α>0, and H_c=√α diag(I_k,-I_k) in a unitary basis. Set K'=K_c-(c/α)H_c. Then H_cK'+K'H_c=0 and (K')²=δI with δ=β-c²/α≥0. Thus

    K'=[[0,C],[C*,0]],       CC*=C*C=δI_k.

For δ=0, K'=0 and the pair is commuting. For δ>0, C/√δ is unitary. Separate unitary changes on the two H_c eigenspaces make C=√δI_k, and pairing corresponding coordinates gives k common two-dimensional reducing subspaces. Since k≥2 this contradicts irreducibility. Therefore 2k=d is impossible, proving (C). ∎

This is an explicit elementary block proof; it invokes neither an unspecified spin/tripotent classification nor a characteristic-factor-to-reducibility rule. Its scope is all finite dimensions and **every norming pair of the specified attained polynomial**, rather than minimal rectangular extremals selected over all symbols. It does not assert p=q_0, nor does it classify higher-dimensional numerical ranges.

In particular all irreducible six-dimensional attained finite-polynomial extremizers have p,q_0≤2. R019 realizes p=q_0=2 with unique norming lines, so the ceiling at the first failure dimension is sharp. If a six-dimensional witness has no constant scalar coefficient channel attaining equality, every one of its maximal singular pairs has at least one rank two; a rank-(1,1) pair would give the compression in Section 4. This does not exclude ranks (1,2) or (2,1), which are not classified here.

## 7. Exact dimensional decision and source comparison

E5 excludes failure in every base dimension at most five. R019 gives failure in base dimension six. Thus the minimum dimension for failure of **same-witness constant scalar compression for attained finite matrix-polynomial complete equality** is exactly six. This is stronger than choosing a new parameter in the old family, but its positive half is a technical combination of an old pencil theorem with R016's paid inverse lemma. It is not assigned another accepted count.

The source operations compare as follows:

- **Leake–Lins–Spitkovsky 2014, Theorem 5.7:** already settles the needed irreducible size-five support question. Theorem 5.11 also classifies the possible multiply generated round sets for reducible size-five matrices, including elliptical arcs and a full ellipse. Such reducible examples are handled by selecting an active block; they are not counterexamples to E5.
- **R016/I242 Sections 1–3:** already supplies the essential zero-slack-to-rank bridge and all limiting analysis. I297 does not rename it as a new discovery. The only size-five insertion is the old theorem plus the analytic multiplicity-to-round-arc check.
- **ACV v3 Sections 5, 7, 11:** Section 5 gives orthogonal rectangular supports and r+s≤d, with top singular simplicity in specified minimal cases. Section 7's equality transfer is through dimension three. Section 11's polynomial classification is scalar in arbitrary dimension. These inspected statements do not give (C) for every pair of a specified original-matrix polynomial witness. The simplicity in Proposition 5.4 is singular-value simplicity, not support-pencil simplicity. Replacing P by a globally minimal rectangular extremal would change the same-witness task.
- **Lawrence v2 Section 4 and original LSS:** the six-dimensional base and repeated support geometry are old. Lawrence changes the pencil under quantum tensor quantization; it does not supply a one-variable constant coefficient compression. The original LSS article was not newly obtained; its reproduction and the completed I292 access limitation are the primary comparison used here. No inference of novelty from that access failure is made.
- **Jin and ACV scalar inputs:** disk rigidity and the scalar monomial operation are credited downstream results. They apply only after constant compression has actually been extracted.

The rank ceiling (C) is a broader structural deduction sought after the immediate E5 collision was found. Its ingredients remain the same R016 inverse mechanism and old two-generator block algebra. No nonroutine new construction, classification, or independent contribution worthy of nomination has been established by this bounded investigation. A separate contribution reviewer may assess its scope; this record does not count it as another finding.

## 8. Validation and remaining obligations

The two supplied target hashes match exactly. Pinned raw source files match their expected SHA-256 and exact Git blobs in `sources/preprints-tree.json`. The decisive 2014 PDF was fetched in memory, hashed, and its actual Sections 1–5 read; no full external paper or section was saved. The R016 residual normalization, projection derivative identity (G), inertia bound (R), Clifford block reduction, tensor conjugation convention, and outer-summand argument were checked algebraically as displayed. No numerical parameter scan or floating-point proof was performed.

There is **no remaining mathematical operation for E5 within the stated dependencies**. Independent proof review of this I297 deduction and contribution review are still required before any acceptance. Worldwide novelty is not claimed. Beyond E5, disk rigidity for general attained complete polynomial equality in dimension six, unequal-rank possibilities (1,2)/(2,1), and classification of all rank-two witnesses remain open in this record. A strict scalar-supremum gap for R019 is not proved or assumed.

Detached output hashes are returned after writing the authentication record; that record does not include a self-hash. Only the assigned I297 paths were written. No shared-index edit, staging, commit, publication, subagent, live sibling read, or history replay was performed.
