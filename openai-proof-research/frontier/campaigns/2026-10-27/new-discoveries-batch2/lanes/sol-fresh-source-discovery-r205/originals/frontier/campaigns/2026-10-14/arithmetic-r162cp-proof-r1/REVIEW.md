# R162CP independent correctness review

**Verdict: PASS.** The unchanged proof establishes every conclusion of the unchanged frozen statement, relative to the stipulated Source177 truth, including its operative proofs. I found no unresolved essential mathematical dependency. This verdict concerns correctness only. It is not a contribution grade, an acceptance decision, or an assessment of any earlier scope.

I independently reconstructed the argument rather than treating the author's conclusion or sanity computations as evidence of validity. The full durable calculation is in `private/DERIVATION.md`; actual reading and verification limits are in `private/READING.md`. No author input was edited or executed. In particular I did not execute the bundled verifier or follow its historical paths.

## Hypotheses and source payment

For each fixed integer d>=3, fix an odd prime q satisfying every largeness requirement of the pinned source, not merely its two explicitly displayed lower bounds. Set N=2d+1. The source construction is exactly the statement's common-intersection coset complex for U/Gamma_N(m), using the images of the specified H_i, with tagged vertex types and the d-skeleton, for every integer m>=2. The proof does not substitute irreducible-polynomial quotients, different coefficients, a subdivision, or a cover.

Reading the complete operative source confirms the following interface. The local-pattern lemma preserves all relevant subgroup intersections under reduction modulo t^m for m>=2. For each nonempty type set A, the corresponding stabilizer has order c_A=|U_(S\A)| between 1 and M=q^(N choose 2), independent of m. All faces of that type form one G_m orbit of size |G_m|/c_A. The source supplies finiteness, purity, connectivity, the precise degree bound D=M*(N-1 choose d), and V=N|G_m|/M>=Nq^m/M. Its homology result and final intrinsic-weight expansion theorem give

  ker(delta_1)=im(delta_0),
  ||delta_0 h||_1 >= epsilon min(||h||_0,1-||h||_0),
  ||delta_1 f||_2 >= epsilon dist_1(f,im(delta_0)).

These statements apply for every m>=2. The source's skeleton normalization is already part of the stipulated input; the new proof uses the X_m intrinsic weights throughout. I did not audit the truth of the source's building, homology, pro-stability, transfer, or KMS arguments. Those are source-paid, as required by the assignment.

## Exact metric and incidence calculations

Let F be the number of d-faces. Each vertex is in at least one and at most D such faces, so V<=(d+1)F<=DV. This gives 1/(DV)<=w_0(v)<=D/V. Each neighbor occurs in a containing top face, so the simple graph has maximum degree at most Delta=dD.

The two incidence factors in the proof are exact: summing w_1 over the edges through a vertex gives 2w_0(v), and summing w_2 over the triangles through an edge gives 3w_1(e). These follow by counting respectively d and d-1 lower incidences inside each top face. The support union bound therefore gives ||delta_1 f||_2<=3||f||_1. Summing ||delta_1 1_e||_2 over edge coordinates, without an extra edge weight, gives exactly 3. This unweighted coordinate sum is the one later used in the Fourier calculation.

Every primitive fiber is a coset of the cut space B=im(delta_0). For any z,z', the difference of any pair in their fibers is a primitive of z+z', so its cost is at least Q(z+z'). Conversely, translation by a minimum primitive maps the uniform law on one fiber bijectively to the uniform law on the other and has constant cost Q. Thus W1(mu_z,mu_z')=Q(z+z') exactly. Expansion gives Q(w)<=epsilon^-1||w||_2, and the factor-three bound gives Q(w)>=||w||_2/3. This proof includes w=0.

The only primary citation invoked in the new deduction is Khot--Naor's coset-transport lemma, for which I read the actual proof. Its finite additive specialization is also proved directly here, so no optimal-transport duality or unverified transport theorem is needed. I read the accompanying Walsh and invariant-code arguments to distinguish them from the affine support argument below.

## Universal lower bound, reconstructed

For any section s whatsoever, set P(f)=f+s(delta_1 f). Since P(f) is a cut, connectivity gives a unique root-zero vertex potential g(f). If h is any vertex cochain, the section condition yields

  g(f+delta_0 h)=g(f)+h+h(o)1.

Neither linearity nor s(0)=0 is used. Consequently chi_uv(f)=(-1)^(g(f)(u)+g(f)(v)) transforms under cut translation by the endpoint sign (-1)^(h(u)+h(v)). Translating the finite Walsh coefficient sum shows that a coefficient indexed by an edge set A can be nonzero only if partial A=1_u+1_v. For distinct u,v, component parity forces A to contain a u-v path, so |A|>=d_H(u,v). This is an affine boundary class. Replacing it with the invariant dual-code support would give Eulerian edge sets and would not justify this distance bound.

The derivative identity and Parseval give

  sum_e Pr_f[chi_uv(f+1_e)!=chi_uv(f)] >= d_H(u,v).

For h_fe=g(f)+g(f+1_e) and t=||h_fe||_0, independently sampled intrinsic-weight vertices disagree with probability 2t(1-t). The source inequality bounds this by 2||delta_0 h_fe||_1/epsilon. Also

  delta_0 h_fe=1_e+s(delta_1 f)+s(delta_1 f+delta_1 1_e).

Average the Fourier inequality with weights w_0(u)w_0(v), sum edge coordinates and use the norm triangle inequality. The first terms sum to sum_e w_1(e)=1. Uniform f pushes forward to uniform z because delta_1 is a surjective linear map onto its image and has equal-sized fibers. This proves

  Dbar <= (2/epsilon)[1+sum_e E_z ||s(z+delta_1 1_e)+s(z)||_1],

where Dbar is the intrinsic-weight average graph distance. Every step holds separately for every s, so it remains valid after averaging over an arbitrary law P on all sections. Bounding each fixed z,e term by L(P)||delta_1 1_e||_2 and using the exact sum 3 gives

  L(P) >= epsilon Dbar/6 - 1/3.

This proves the required order of quantifiers. The pair is chosen after the law P is fixed, not after the sampled section is observed. There is no interchange of maximum and expectation. Neither marginal uniformity nor linearity is needed.

For B_0=Delta+1, every radius-r graph ball has w_0 mass at most D B_0^(r+1)/V. Taking r=floor(log(V/(2D))/log B_0)-1 makes this at most 1/2. If log V>=2log(2D)+4log B_0, then r>=log V/(2log B_0), hence Dbar>=log V/(4log B_0). If also log V>=16log B_0/epsilon, the subtractive 1/3 is absorbed and

  L(P) >= epsilon log V/(48log B_0).

I checked both inequalities including the floor. The source growth bound supplies a single m_0 after which these inequalities hold for every m, not just for a subsequence. This establishes the lower bound for S_m and therefore for U_m.

## Matching law and every exact marginal

For a vertex set S of mass at most 1/2, source expansion supplies crossing-edge mass at least epsilon w_0(S). The factor-two incidence identity bounds that mass by twice the mass of its outside neighbors. Thus balls grow by at least 1+epsilon/2 until they exceed mass 1/2. Starting from mass at least 1/(DV), radius

  k=ceil(log(DV)/log(1+epsilon/2))+1

suffices. Any two radius-k balls intersect. The graph diameter is at most 2k, and a BFS spanning tree has root radius R<=2k.

For that tree define h_T by root-path sums and Q_T f=f+delta_0 h_T(f). This is linear, preserves delta_1, kills every cut, and vanishes on tree edges. It therefore defines one linear section on the entire syndrome space. Uniqueness of the gauge follows because a cut vanishing on the connected tree is zero.

At an output edge b=uv, the row of Q_T is the parity vector of {b} symmetric-difference path_T(u,v), of length at most 2R+1; for a tree edge it is empty. Consequently

  sum_e ||Q_T 1_e||_1 <= 2R+1.

This is a total column budget, not an individual-column assertion. The proof correctly obtains the individual expected bound by conjugating with uniform gamma in the actual source group. For an edge type A, its orbit mass is

  alpha_A = [sum_(B contains A, |B|=d+1) 1/c_B]
            /[(d+1 choose 2) sum_(|B|=d+1) 1/c_B].

The count c_A/c_B of containing faces proves this formula. It gives alpha_A>=1/[M*(d+1 choose 2)*(N choose d+1)], uniformly in m. The action preserves intrinsic weights and is transitive on each type orbit, so

  E_gamma ||Q_gamma 1_e||_1 <= ((2R+1)/alpha) w_1(e),

with alpha=min_A alpha_A. Linearity and the support union bound extend this to every cochain. Applying it to a minimum primitive of z+z' estimates the already constructed common section; it does not choose a different section for each pair. With K_m=(2R+1)/alpha=O_(d,q)(log V), the pair cost is at most K_m Q(z+z'), hence at most K_m epsilon^-1||z+z'||_2.

One independent uniform cut b, added to ALL section values simultaneously, makes each value uniform on its complete primitive fiber conditional on gamma. It leaves all pair differences unchanged pointwise. This proves the asserted affine support and the exact marginal on every syndrome, including zero. It supplies both U_m<=C log V and R_m<=C log V, while the unshifted law supplies the linear witness for S_m.

For each feasible uniform-marginal law, epsilon L(P)<=r(P)<=3L(P), by the two-sided comparison between Q and the syndrome norm. Thus epsilon U_m<=R_m<=3U_m; in particular the universal lower bound gives the claimed lower bound for R_m. The proof's common lower constant epsilon^2/(48log B_0) is sufficient. To ensure constants depend only on d,q even if the displayed epsilon is chosen arbitrarily smaller, the proof explicitly fixes epsilon_*=min(1,eta/M) for the asymptotic argument and separately proves the two-law inequalities for any permitted epsilon. This resolves the apparent quantifier issue without changing the statement.

## Boundaries, scope, and objections resolved

Purity gives a triangle containing every edge, so delta_1 1_e is nonzero. Duplicate directions, if present, are counted with their edge multiplicities in both sums. The complex has at least N tagged vertices and a triangle, so V>=2 and the syndrome family has distinct members; the maxima are not over an empty set. Positive intrinsic weights make every distinct-syndrome denominator positive. At u=v the Fourier lower bound is zero; at equal syndromes the transport identity is zero, and no division by zero occurs. The all-m exact assertions hold already at m=2; only the positive logarithmic lower bounds require m>=m_0.

The upper law is genuinely a single law on sections. Its finite support bounds follow from the uniform group element and, for affine sections, the 2^(V-1) cuts. The claim about linear sections is an upper-bound witness, not a claim that a linear law minimizes S_m exactly. All infima are over nonempty finite-dimensional probability simplices; finite feasibility and the explicit witnesses suffice.

The computational remarks stay within their stated scope. Explicit incidence/action input allows BFS, Boolean elimination, tree evaluation, and permutation application with polynomial bit cost in that input and its explicit outputs. With d,q fixed, relevant face counts and |G| are O(V), making the stated matrix lists polynomial in V. This does not enumerate every syndrome output for free. Rooted vertex bits give a uniform cut. Rejection sampling gives an exact uniform listed group element with fewer than two trials in expectation, without a deterministic trial bound. The proof asserts no source generator runtime or algorithmic lower bound.

The concerns examined above were resolved within the unchanged proof and its stipulated source interface. There is no proposed repair, restricted substitute, or silent added hypothesis. No essential unstipulated mathematical fact remains unverified. Broader contribution comparisons and transitive ancestry not needed for this deduction were not independently validated, and this correctness verdict makes no claim about them.
