# Contractive approximation after the strongest compatible transfer

This notebook continues the prefreeze calculations; it is not a frozen theorem or an author-proof nominee. It is useful to retain the exact norm improvement because stopping at the obvious norm-five combination misses a compatible operation in the actual Popa–Vaes proof.

## 1. Synchronize a compression with diagonal witnesses without adding colors

Work first with A⊂M in the centralizer of a faithful normal state φ. Fix a finite family x_j=x_j*, ∥x_j∥≤1, with diagonals d_j=E_Ax_j. Fix γ>0. Section 4 of CALCULATIONS supplies one partition P of size

    R=⌈4·10^8 m γ^−2⌉,

and a projection q commuting with all p∈P such that

    ∥q(S_P(x_j)−d_j)q∥≤γ  for every j,

while φ(1−q) can be made arbitrarily small. Crucially d_j is fixed before P,q; this is stronger than an unspecified varying diagonal.

Choose a common finite spectral partition (b_ℓ)_{ℓ=1}^L⊂A and self-adjoint step functions c_j=Σ_ℓ c_{jℓ} b_ℓ with ∥d_j−c_j∥≤γ. Such a finite joint partition exists because the d_j commute and have spectrum in [−1,1]. L can depend on m and γ, even exponentially; we will not multiply the number of paving colors by L.

Set

    τ=γ²/(16L),   B=Σ_ℓ b_ℓ q b_ℓ,   q'=1_(1−τ,1](B).

Take γ<1, so 0<τ<1. Both B and q' commute with all b_ℓ and with P: q commutes with P, and the b_ℓ commute with P. Put q'_ℓ=b_ℓ q'. Spectral calculus gives

    ∥(1−q)q'_ℓ∥²=∥q'_ℓ(1−q)q'_ℓ∥≤τ.

For a vector ξ, the ranges of q'_ℓ are orthogonal. The triangle inequality followed by Cauchy–Schwarz yields

    ∥(1−q)q'ξ∥≤√τ Σ_ℓ∥q'_ℓξ∥≤√(Lτ)∥ξ∥.

Thus ∥(1−q)q'∥≤γ/4. Since b_ℓ belongs to the centralizer,

    φ(1−B)=φ(1−q),   φ(1−q')≤τ^−1 φ(1−q).

We can therefore arrange q' arbitrarily close to 1 strongly, after choosing the joint spectral partition and τ. There is no new quantitative requirement on R: only the allowable lost φ-mass has been reduced.

Let z_j=S_P(x_j)−d_j, so ∥z_j∥≤2. Write

    q'z_jq'−q'q z_j q q'
      =q'(1−q)z_jq'+q'q z_j(1−q)q'.

This gives ∥q'z_jq'∥≤γ+4√(Lτ)=2γ. Also q' commutes with c_j. The off-diagonal part of d_j for q' has norm at most γ:

    ∥q'd_j(1−q')+(1−q')d_jq'∥≤∥d_j−c_j∥≤γ.

To justify the norm bound without a factor error, if u=2q'−1 then this off-diagonal part of t=d_j−c_j is (t−utu)/2; conjugation by u is isometric.

Define

    y_j=q'x_jq'+(1−q')d_j(1−q').

These are self-adjoint contractions: the two terms are in orthogonal q' and 1−q' corners, and each has norm ≤1. They converge strongly to x_j as q'→1. Because q' commutes with every p∈P and d_j∈A,

    S_P(y_j)−d_j
      =q'z_jq'−q'd_j(1−q')−(1−q')d_jq'.

Consequently ∥S_P(y_j)−d_j∥≤3γ, with *the original R colors*. The b_ℓ were used to improve q, not appended to P.

This is the exact compatibility that avoids an artificial extra γ^−1 or γ^−m factor. PV15 Proposition 2.4(2), read through its proof, already regularizes a compression by spectral cuts of pinched q. The present calculation applies that operation to the commuting diagonal witnesses while preserving the existing paving partition. It is not justified by deleting the expectation hypothesis from PV15 Lemma 2.5: that deletion is explicitly false by their Remark 2.6.

## 2. A contractive assembly across noncentral corners

The additive block replacement in AP general.tex preserves off-diagonal entries of x exactly and gives norm at most 3. A completely positive replacement preserves them strongly instead and keeps norm at most 1.

Let A⊂M⊂B(H) be arbitrary. Let e,h=1−e be AP's support decomposition, with faithful normal expectation E_e:eMe→Ae. Fix the finite family of normalized x_j and the requested finite-vector tests. Enlarge the finite tests to include a norming vector ξ_j^0 for each nonzero x_j, and the images of every test vector under each x_j. Let f be the support on Ae of the sum of these restricted vector functionals; put g=e−f. Then f,g,h∈A and g annihilates all these test vectors. The normalized sum on Af, composed with E_e|_{fMf}, is a faithful normal state φ_f central over Af. Empty corners are omitted.

On fMf apply Section 1 to f x_j f, with absolute error 3γ. Compression need not preserve the global normalization; it suffices that ∥f x_j f∥≤1. We use the shared partition of f of size R, the shared projection q'_f, and fixed d_j=E_e(f x_j f). The projection q'_f can approximate f on every prescribed finite set in the original representation, by the faithful-state/normal-functional implication proved in QSP state reduction.

On hMh apply AP lem:no-central-functional with the *same* normal state formed from all h-test vectors and all h x_j-test vectors. It supplies 0≤s≤h and a partition P_h of h into n=⌈1/γ⌉ pieces such that

    s→h strongly on those tests,    p s p≤p/n  (p∈P_h).

For every self-adjoint contraction h x_j h, positivity gives

    −s²≤s x_j s≤s²≤s,
    ∥S_{P_h}(s x_j s)∥≤1/n≤γ.

The same s works for the entire family; its construction in AP depends on the state/tests, not on one operator after those tests have been fixed.

Now put

    Q=q'_f+s   (zero on g),   R_0=(1−Q²)^{1/2},
    Φ(z)=QzQ+R_0 E_e(fzf) R_0,

where the expectation value is extended by zero off f. This is a normal completely positive map. Since f commutes with Q,

    Φ(1)=Q²+R_0 f R_0=f+s²≤1.

Hence Φ is contractive, even completely contractive. Equivalently the two-column contraction (Q,R_0 f)^T gives an isometric-compression proof of the norm bound with a zero auxiliary corner. The elementary CP-compression operation also occurs explicitly in the eligible original history section recorded in private/ORIGINAL-EXTENT.json; it is not claimed as a new primitive.

Set y_j=Φ(x_j). Then y_j=y_j*, ∥y_j∥≤1. On f its diagonal corner is exactly

    q'_f f x_j f q'_f+(f−q'_f)d_j(f−q'_f),

on h it is s x_j s, and on g it is zero. The cross-corner entries are Q x_j Q, not the original entries. This change is harmless in the required strong topology:

    Qx_jQ−x_j=Qx_j(Q−1)+(Q−1)x_j.

Both terms are small on the chosen tests. The expectation term on a test ξ has norm at most ∥(f−q'_f)ξ∥ because ∥d_j∥≤1; it is zero on h and g. Therefore y_j−x_j is arbitrarily small on the original finite F. This argument uses gξ=g x_jξ=0; retaining only the original F in the support construction would not justify the displayed estimate.

Use the f-partition, P_h, and g as disjoint palettes. This is one partition P of size R+n+1. It kills every cross-corner term after pinching, though the corners are not central in M. Extend d_j by zero off f. The f and h estimates give

    ∥S_P(y_j)−d_j∥≤3γ,   ∥d_j∥≤1.

No global conditional expectation onto A has been introduced; E_e is used only on its legitimate support corner.

## 3. Relative normalization and exact retained conclusion

Given 0<ε<1, take γ=ε/16. Choose the norming vectors with ∥x_j ξ_j^0∥>1−γ/2 and make the approximation error there <γ/2. Then ∥y_j∥>1−γ. Clip d_j in the abelian algebra to [−∥y_j∥,∥y_j∥], obtaining a_j. Thus

    ∥a_j∥≤∥y_j∥,
    ∥a_j−d_j∥≤1−∥y_j∥<γ,
    ∥S_P(y_j)−a_j∥<4γ=ε/4≤ε∥y_j∥.

Scale each nonzero x_j back individually; the same map Φ is linear and contractive, so its norm bound survives simultaneous rescaling. Zero x_j have y_j=a_j=0.

The precise retained deduction is: for every m≥1 and 0<ε<1, fix

    N_m(ε)=⌈102400000000 m ε^−2⌉+⌈16/ε⌉+1
          ≤110000000000 m ε^−2.

For every complex represented von Neumann algebra M⊂B(H), every MASA A⊂M, every x_1,…,x_m∈M_sa, every finite F⊂H and δ>0, there exist a single N_m(ε)-partition P⊂A, a single normal completely positive contraction Φ:M→M, y_j=Φ(x_j)=y_j*, and a_j=a_j*∈A with

    ∥y_j∥≤∥x_j∥,
    ∥(y_j−x_j)ξ∥<δ (ξ∈F),
    ∥a_j∥≤∥y_j∥,
    ∥S_P(y_j)−a_j∥≤ε∥y_j∥.

This is stated to retain exact quantifiers, not as a frozen nomination. In particular m=1 gives contractive quadratic approximation paving in the full expectation-free setting. No claim that the source prints this exact conclusion is made. Its construction consists of the RS signed-tuple polynomial, QSP's already-paid measurable transfer, PV15 spectral regularization, AP's no-central-functional contraction, and elementary completely positive corner gluing. The shared Φ is allowed to depend on the finite family and neighborhood; it has no asserted uniform pinching bound on all of M's unit ball. The clipped witnesses a_j need not depend linearly on x_j.

## 4. What this closes, and what it does not

This closes the tempting norm-five/norm-three/near-isometric approximation issues within the integrated reduction. It would be inaccurate to record loss of norm control or absence of a normal expectation as an unpaid barrier for this construction. The gain is not based on falsely refining arbitrary so-pavings, meeting nontracial high-mass projections, or applying a noncommuting clipping formula.

It does not give norm paving of the original operator for every MASA. It does not choose one finite partition for an infinite arbitrary family, or a partition independent of the strong neighborhood. It does not provide the sharp universal constant or the singular-MASA independence from family size in the Cartan case. Those would require other operations. No new-to-literature priority claim, independent correctness verdict, substantial-contribution grade, acceptance, or count is assigned.
