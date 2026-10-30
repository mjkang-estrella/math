# Structural202 — independent contribution review, round 1

**Conditional contribution verdict: TECHNICAL. Correctness of the entire unchanged frozen statement and submitted proof remains explicitly UNDISCHARGED in this role.** This is a contribution comparison, not a correctness grade, adoption, acceptance, or count. No sibling review, sibling brief, task status, parent adoption, or peer result was inspected or used. Parent alone adopts.

The verdict applies to FROZEN-STATEMENT.md, 2443 bytes, SHA256 `fbd2600bdc050aac6e4ab130c3d4a35f88db4fa2af26b5e2b163ee922d760433`, and the complete AUTHOR-PROOF.md, 13488 bytes, SHA256 `121ae56cd4b1444ed373549589c3f53a68fc22e9556c2f959a34084bbcc86b80`, in the admitted author root. Neither was edited, narrowed, renamed, or refrozen. The conditional premise is correctness of that entire submission; the comparison below does not replace it with a different nominee.

The reason for TECHNICAL is a complete compatible reduction using Source326's actual proof operations, ordinary quotient duality, an unrestricted finite-stage schedule, and compact finite-net telescoping. In particular, the source's moment enlargement can be dualized to a restriction-map estimate and then assembled into an **identity** estimate on the annihilator of its weighted-sum kernel. This exposes why the author's collapse is an elementary reorganization of an already-paid construction. The argument accounts for the quantitative and uniform scope; it does not rest on the failure of an unrelated direct sum or on an unbridged map/identity distinction. The primary comparisons below strengthen the baseline but are not needed as missing links in the complete reduction.

## 1. Scope held fixed

The input is arbitrary real Banach X,Y, finite real r>=2, D>=1 with C_r(X*)<=D, compact T:Y->X, and an arbitrary finite-dimensional E subset X. The output is one separable reflexive real G, injective compact J:G->X, compact U:Y->G, and contraction i:E->G, with JU=T, Ji=inclusion, ||J||<=2 and ||U||<=2||T||. The very same four objects must satisfy, for every real s>r,

    C_s(G*) <= 48 D H(r,s),
    H(r,s) = (sum_(k>=1) (1+log_2 k)^s k^(-s/r))^(1/s).

Cotype is measured against the L2 norm of the real Rademacher sum. Nonseparable endpoints and all zero/finite-dimensional cases belong to this scope. AP, BAP, primal cotype, endpoint reflexivity, and K-convexity are not inputs. Endpoint cotype r, AP of G or G*, primal cotype of G, and complex scalars are not conclusions.

## 2. What the full pinned source already pays

I authenticated all ten canonical blobs against the complete, hash-matching 13223-entry preprints tree and read all nine textual bodies, not merely lem:compact-domain's statement. The pin is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`; all its operative proofs are stipulated true and are not audited here. The canonical folder is `preprints/The-cotype-cotype-conjecture-under-the-approximation-property-September-23-2026/`. The wrapper includes introduction, preliminaries, coefficient, walsh, approximation, consequences, then references.

The decisive paid interface is the proof of approximation.tex, lem:compact-domain, eq:finite-level-lift. If c_m(X*)<=Delta_m, then every finite-dimensional F subset X can be enlarged to a finite-dimensional F' subset X so that each tuple z in ell2^m(F) has an exact first-moment lift h with

    E eps_i h = z_i,       ||h||_(L2(F')) <= 3 Delta_m ||z||_ell2.

The operation uses the surjective finite moment map, finite-atomic L2 duality, preliminaries.tex eq:quotient-lift, finitely many sphere-net lifts with slack, and an exact linear correction of the moments. It is a statement about existence of lifts; it does not supply or require a linear selector. Norms are the inherited X norms. Nothing bounds the dimension of F', the number of finite constraints, or the number of prescribed additional vectors. Thus a finite collection of lengths and a finite set of additional vectors can be accommodated by taking a common span, with the **same** constants at each length.

The source also explicitly constructs H=ell2(E_l), j(z)=sum 2^-l z_l, G=H/ker j, and the injective compact J with JQ=j. It gives the coordinate embedding of E, the weighted shift R(z)=(0,2z_0,2z_1,...) with QR=Q, and the L2 assembly followed by duality. The source does not assert cotype passes to an arbitrary quotient. Its choice of finite-dimensional blocks already makes H, and hence G, separable and reflexive; these properties require no additional factorization theorem or AP.

The remaining source proof is also paid. The bounded moment lifts in preliminaries use the explicit moment constant 24. The coefficient lemma works with binary Fourier-index rank; the Walsh growth argument applies to general operators, and the uniform decay theorem applies to finite-rank maps and their norm closure under fixed-length domain-dual and range cotype bounds. Its final AP transfer approximates the compact image J(B_G), so only S_j J converges in norm; no uniform bound on S_j is introduced. With a compact-open approximable A:V->W, cotype of V* and W gives the analogous transfer by approximating A on that same compact image. The uniform K-constant/entropy and tensor-pair consequences are already in the source. None is an additional contribution of this submission. They do not supply a missing primal-cotype or AP hypothesis for the present target.

## 3. Complete compatible reduction of the unchanged target

This section is a contribution-reduction calculation. It explains the full available composition, including constants, rather than assigning correctness to the submitted proof.

### 3.1 One finite hierarchy and the source quotient

Put Delta_m=D m^(1/2-1/r); the source's finite-length convention gives c_m(X*)<=Delta_m. If T is nonzero set K=closure(T(B_Y)/||T||); otherwise set K={0}. This is a compact subset of B_X. Choose finite eta_l-nets N_l in K with eta_l=2^(-2l-4), and put M_l=2^(2^l).

Start E_0=span(E union N_0). Given E_l, use the paid enlargement for the finitely many m<=M_l and adjoin N_(l+1). All resulting spans remain finite-dimensional subspaces of X. Every m eventually occurs at all later levels. These choices depend on r,D,T,E and the countable length schedule, never on s.

Use exactly the source's weighted quotient. Cauchy–Schwarz gives ||j||<=sqrt(4/3), and its tails have operator norm at most (sum_(l>L)4^-l)^(1/2). Thus j is compact. Its closed kernel gives separable reflexive G=H/ker j, and J is injective, compact, and has norm <=sqrt(4/3)<2. To see compactness of J without descending truncations, representatives of B_G can be chosen in 2B_H. The map i(x)=Q(x,0,...) is a contraction and Ji=x. These are the same paid operations as in the source, unaffected by the additional finite constraints.

### 3.2 A direct dual calculation supplies an intermediate IDENTITY estimate

Here is an independent formulation of the compatibility step, avoiding a bare claim that an operator estimate becomes an identity estimate. Identify G* isometrically with (ker j)^perp in H*=ell2(E_l*). Write Q*theta=(theta_l). The finite vector with x in coordinate l and -2x in coordinate l+1 is in ker j, for x in E_l. Therefore

    theta_l = 2 theta_(l+1)|E_l,
    ||theta||_G*^2 = sum_l ||theta_l||_E_l*^2.                  (A)

For L>=0 put beta_L^2=sum_(h=0)^L 4^(L-h). Nesting and (A) imply

    sum_(l<L)||theta_l||^2 <= (beta_L^2-1)||theta_L||^2,
    ||theta||^2 <= beta_L^2 sum_(l>=L)||theta_l||^2.           (B)

Next dualize the paid finite-level lift. For any phi_1,...,phi_m in E_(l+1)*, and any z_i in E_l, its exact moments give

    |sum_i phi_i(z_i)|
      <= 3 Delta_m (sum_i||z_i||^2)^(1/2)
           (E||sum_i eps_i phi_i||_E_(l+1)*^2)^(1/2).

Taking the supremum over the ell2 unit ball yields a cotype estimate for the restriction map E_(l+1)*->E_l*. Apply this with phi_i=theta_(l+1)^i and use (A). For m<=M_l,

    sum_i ||theta_l^i||^2
      <= 36 Delta_m^2 E||sum_i eps_i theta_(l+1)^i||^2.       (C)

Let L be the least level with m<=M_L. Sum (C) over l>=L and combine with (B). Nonnegative sums and the finite sign probability space justify the interchange, and the right-hand side is a tail of the norm in H*. Since Q* is isometric, the resulting bound is on the actual identity of G*:

    (sum_i||theta^i||_G*^2)^(1/2)
      <= 6 beta_L Delta_m (E||sum_i eps_i theta^i||_G*^2)^(1/2).

Thus c_m(G*)<=6 beta_L Delta_m. For m=1,2 we have L=0. For m>2, minimality gives 2^L<2 log_2 m, while beta_L<=2^(L+1). Consequently

    c_m(G*) <= 24 D(1+log_2 m)m^(1/2-1/r)
             <= 48 D(1+log_2 m)m^(1/2-1/r).                 (D)

The factor 24 is numerical slack in a comparison derivation, not a replacement statement or proposed strengthened nominee. It shows explicitly that the frozen factor 48 is fully covered. In the author's primal formulation the choice of quotient representatives contributes an extra factor two, giving the displayed 12 Delta_m beta_L and then 48. Both formulations use the same source operation and the same coherent weighted quotient.

This is the substantive reason I do not identify a surviving nonroutine operation in P_L. Its identity QP_L=Q is the primal form of (A)–(B): earlier coordinates can be represented at level L because the source's blocks are nested and the weights are known. Its norm loss is just the geometric sum beta_L. The finite-dimensional dimension is unconstrained, so increasing M_l doubly exponentially costs no hypothesis or constant. The logarithm is the inversion of this freely chosen schedule, not an additional geometric or interpolation theorem. This assessment uses a fully demonstrated identity estimate, rather than equating map cotype with identity cotype by terminology.

### 3.3 All real exponents on that same space

For a finite tuple in G*, rearrange a_k=||theta_k|| decreasingly, and let A be its full L2 Rademacher norm. Conditional Jensen says the Rademacher norm of any first k terms is <=A. Apply (D), using the frozen larger constant:

    sqrt(k)a_k <= 48 D(1+log_2 k)k^(1/2-1/r) A.

Hence a_k<=48D(1+log_2 k)k^(-1/r)A. Summing its s-th powers gives exactly 48D H(r,s) for every real s>r. The series converges because s/r>1. No countability restriction on s is introduced: a single pointwise bound in k implies each real-s inequality after the space has been fixed. No endpoint s=r assertion is substituted.

### 3.4 Both factors compact, unique lifts, and the frozen operator bounds

For x in K choose v_l(x) in N_l within eta_l of x. Define

    z_0(x)=v_0(x),
    z_l(x)=2^l(v_l(x)-v_(l-1)(x))   (l>=1).

The coordinate belongs to E_l. Since ||v_0||<=1 and ||z_l||<=(5/16)2^-l,

    ||z(x)||_H^2 <= 1+(25/256)sum_(l>=1)4^-l = 793/768.

The j-series telescopes to x. Each coordinate takes only finitely many values, and the square-sum tails vanish uniformly, so closure{z(x):x in K} is compact in H. This is finite-net compactness, not approximation by finite-rank linear operators on Y or X.

The set of quotient lifts is compact as well. More explicitly, any convergent subsequence of representatives has image x in the closed set K; injectivity of J identifies its quotient with the unique lift of x. Equivalently Q(closure Z)={J^-1 x:x in K}. This does not assume the chosen net selections are continuous. Injectivity is already paid by the source quotient and removes their ambiguity.

For T nonzero, range(T) lies in range(J) by homogeneity of K. The unique inverse on that range makes U=J^-1 T linear; U(B_Y) is contained in ||T|| times the compact lift set. Therefore U is compact and

    ||U|| <= sqrt(793/768)||T|| < 2||T||.

For T=0 take U=0. For X=0 use G=0 and zero maps. The construction permits E=0, zero initial blocks, and finite-dimensional endpoints. Separability comes from countably many finite-dimensional blocks, even if X,Y are nonseparable. Reflexivity comes from their ell2 sum and its quotient. At no point is AP, BAP, primal cotype, or reflexivity of an endpoint used. The prescribed E is retained in the zeroth coordinate throughout.

The telescope is compatible with the cotype construction precisely because all its requirements are finite vector inclusions at each stage. It adds no competing norm constraint and changes no moment constant. Ordinary telescoping plus finite-coordinate compactness completes the source construction at the full frozen scope.

## 4. Actual primary comparisons and the strongest combinations tested

### Figiel 1973

I visually read the original publisher scan, PDF pages 1–9 (the article's printed pages 191–207, through Section 7; the neighboring article and Section 8 opening are not used). Empty pdftotext output was not counted as reading. In Proposition 3.1 the target is embedded isometrically in C(S); the compact operator into C(S) is approximable, is factored through the universal C_p, and the intermediate space is restricted to the inverse image of the original target. Corollary 3.3 takes 1<p<infinity to obtain reflexivity. Sections 4–6 supply the disjoint finite-dimensional projections and weighted difference-series construction behind the universal factorization, including norm-convergent compact factors. Section 7 explains a stronger L_p-compatible restriction when the target embeds into L_p.

These are actual proofs of compact factorization, not just a headline credit. C_p uses a sequence representing every finite-dimensional geometry, and its reflexivity for p=2 does not make it Hilbert or give a finite cotype constant for its dual. The L_p refinement requires a target representation not present in the frozen hypotheses. Nevertheless, reflexive factorization, both compact factors, restriction to the target, and weighted telescoping are paid operations. The reduction in Section 3 supplies the required controlled blocks directly, so it does not need to force universal C_p into an unjustified geometric class.

### Pisier 1980 and 1980–81

In the original ENS paper, read text PDF pages 3–15 with image recovery of 14–15, Proposition 2.2 and Lemma 2.3 use exactly the finite-moment quotient-duality principle and a bounded Rademacher projection. The Riesz-product estimate of Lemma 2.4 is absorbed into the Hilbert factorization bound. Theorem 2.15 iterates a nuclear tensor part plus a smaller remainder; its dual Corollary 2.16 assumes compact-open approximation, not BAP. It proves the stronger Hilbert factorization when the **domain dual and range** both have cotype two. This is fully paid where compatible. The frozen T:Y->X provides cotype of X*, not cotype of Y* and X, so that Hilbert theorem cannot be invoked on T. Applying it to T* instead would require cotype of X** and Y*, also not given. Compactness alone is not the missing compact-open approximation hypothesis in arbitrary endpoints.

I also read the actual K-convexity duality in exposé II, Proposition 1.4, and the supplied semigroup proof operations, and all nine mathematical pages of exposé VII visually. Exposé VII combines the type/cotype Walsh estimate, the commuting-projection noise argument, a holomorphic-sector bound, and three-lines interpolation to absorb K(X)^theta. Its finite-dimensional-to-infinite-dimensional passage uses uniformly complemented blocks; Remark 9 supplies the operator version and BAP extension under its exponent constraint. The reverse cotype-to-type duality requires K-convexity; merely having cotype of X* does not supply it. No historical statement that a question was open is asserted to be current. These stronger operations are compatible under their actual additional inputs, but do not remove a cost from Section 3 that has not already been paid.

### Pisier 1983

I read text PDF pages 2–21, with scan recovery for the critical quotient estimate and the Section 3 construction. This paper is stronger than an AP counterexample citation. Theorem 2.2 takes the graph quotient (B plus_1 E)/{(s,-u(s))}, preserves E isometrically, and uses a Rademacher lifting property for B/S to obtain a cotype bound of the form max{c_q(E),2Kc_q(B)}. Corollary 2.3 assembles families; Theorem 2.4 iterates without accumulating that maximum. Proposition 1.8 and the subsequent extension characterization relate dual cotype to first-moment extensions. Theorem 3.2 applies these operations to obtain primal and dual cotype two; the printed page 200 remark also gives an extension of a cotype-q space with dual cotype two. These identity estimates and nonaccumulating extensions are paid, not ignored.

For the frozen input, applying such an extension to X* gives an embedding into a larger cotype space, rather than the required compact injection into X with a prescribed lift of T. Dualizing gives a quotient onto X**, not unique lifts of T into X. No arbitrary compact linear lifting through that quotient, compact compatible extension of T*, reflexive intermediate space, or numerical 48D bound follows from that change of direction alone. The original construction contains L1-type extension pieces and is not a reflexive compact factorization with the frozen normalization. This tests an actual stronger identity-level comparison. Section 3 above avoids these extra demands by using the stipulated source's local moment lifts inside X itself. Pisier's AP obstruction is relevant to interpreting the source's different main theorem; it is not evidence of substantiality here.

### Jarchow–Matter 1988, including interpolation and duality

I visually read **all twelve pages** of the original publisher scan, printed 45–56, including (1)–(13), their supplied proofs and references. The proof of (10) forms the interpolation couple (domain/ker T, range), uses an intermediate space of both J- and K-type theta, and applies the injective and surjective hull relations. It is stronger than merely separating one type and one cotype factor in (13). The duality statement (6), hull relation (7), and reiteration (11) were also read and tested.

Here is a compatible application, with K denoting the compact ideal and C_r the operator-cotype ideal. T*:X*->Y* is compact and has operator cotype r with bound D||T||. Take A=K and B=K intersect C_r in (10). Compactness is a closed injective/surjective ideal, while C_r is injective. For every 0<theta<1 the result yields T*=R_theta S_theta with both maps compact and S_theta of cotype r/theta. Indeed (5)(c) gives K^theta=K and K_(1-theta)=K. The cotype conclusion follows from (12)(a).

I checked the supplied DERIVATIONS Hölder calculation against the original definitions. If

    ||Sz|| <= c ||Az||^theta ||Bz||^(1-theta),

A has operator cotype r and B is bounded, then

    (sum_i||Sz_i||^(r/theta))^(theta/r)
      <= c (sum_i||Az_i||^r)^(theta/r) (max_i||Bz_i||)^(1-theta)
      <= c C_r(A)^theta ||B||^(1-theta) Rad_2(z_i).

The last inequality uses max_i||z_i||<=Rad_2(z_i), obtained by taking the i-th moment of the Rademacher sum. This supplies the omitted proof in (12)(a) for the relevant endpoint case without importing an abstract.

The combination can be pushed further: factor the compact R_theta through a separable reflexive space using Figiel. Composing its first factor with S_theta retains operator cotype, since postcomposition is bounded. Thus both compact factors and a separable reflexive middle space can coexist with that map estimate. Dualize, restrict the middle dual to the inverse image of the canonical X in X**, and quotient the kernel of the output map. This also recovers a qualitative injective compact factorization of T with unique lifts. A finite-dimensional summand for E can be inserted at the start. These are legitimate compatible operations; stopping before them would understate the paid comparison.

What this route alone does not quantitatively identify is the identity cotype of the final middle dual. In (10) applied to T*, its first interpolation endpoint is X*/ker T*, a quotient whose identity cotype cannot be assumed from X*. A map bound for S_theta is measured against Rad_2 of preimages in X*, not against Rad_2 in its image with the interpolation norm. Neither the hull duality nor reiteration proves the necessary uniform Rademacher lifting of those preimages. A compact surjection onto an infinite-dimensional middle space could not supply a bounded inverse lift. Replacing the quotient norm by an arbitrary range/interpolation norm does not resolve that issue. Each fixed-theta construction also varies with theta; (11) manipulates membership of operator ideals and does not assert one middle space with all theta estimates and the frozen numbers.

These observations are limits of this standalone classical route, **not a novelty argument or an essential unresolved bridge in this verdict**. Section 3.2 explicitly supplies the bridge with paid source finite-level restriction estimates and coherent quotient coordinates. It proves the middle identity estimate, and Section 3.3 then gives one-space/all-real-exponent control. The verdict therefore does not require resolving whether some other interpolation presentation could prove the same statement independently.

## 5. Contribution assessment and remaining limits

The author has written a useful explicit consequence. The complete comparison, however, leaves only finite simultaneous closure of an already available operation, a freely chosen length schedule, a geometric-series estimate on coherent coordinates, a decreasing-rearrangement summation, and finite-net telescoping compatible with that same closure. The dual derivation (A)–(D) exhibits why these fit together: no new selection theorem, quotient-stability theorem, interpolation identity, approximation hypothesis removal, or dimension-free geometric estimate is required beyond the source's paid moment enlargement. The frozen constants have substantial slack after those elementary operations.

This is why the conditional contribution verdict is TECHNICAL rather than SUBSTANTIAL. It is not a claim that the exact headline or constant 48 occurs in an old paper, nor that every elementary argument is automatically technical. Here the full frozen scope follows by a demonstrated reorganization of the paid construction, and its apparent compatibility difficulty is resolved by that construction's existing nesting and annihilator relation. No essential comparison is left open in the reduction supporting this verdict.

Literature and history remain scoped. No exhaustive or worldwide-priority clearance is claimed. The author-reported DFJP and Hinrichs access failures supply no mathematical or novelty premise; I do not infer the absence of another reduction. Only the three authorized original I88/I90 byte spans were read, directly by binary seek before decoding. Their cotype discussions correctly distinguish binary rank from operator rank and warn that quotient truncations need not descend; they do not alter the reduction above. Other original scopes and excluded archives remain untouched. Broad guards can omit relevant originals and opaque aliases can escape prompt-level classification, so those exclusions are not evidence of distinctness.

The actual Lean documentation and comparator were read. The comparator contains `sorry`; it supplies no completed formal proof, and no formalization was performed. This fact is an evidence limit, not a contribution or correctness grade.

Detailed read extents, output-recovery limits, author integrity baselines and packet limitations are recorded in the outside REPORT.md and private/READING-LOG.md. Correctness of the full unchanged submission remains UNDISCHARGED in this role, regardless of any separate review's existence or result.
