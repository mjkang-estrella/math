# Prefreeze feasibility: exact state evaluation and adaptive extraction

These are integrated paid calculations, not a frozen theorem or author-proof nominee. No correctness, contribution, acceptance or count is assigned. The operation tested is efficient evaluation/extraction of the actual Source180 paired-state sum, after classical planar-dimer and BKN completion mechanisms. It is not a restricted retry of the old full affine-span/counting scopes.

## 1. Exact domain and integer weights

Let T be the source simple sphere triangulation with properly black/white colored faces, a chosen outer black triangle t0, and NO separating triangle. Let A be its other black triangles, X its nonroot vertices, and m=|A|=|X|. T has m+3 vertices; its cubic bipartite planar dual G has N=2m+2 vertices. Use the actual source states r,s:A→X, bijective and incident, with r(t)≠s(t) for every t. The source flow proves a pair exists in this domain.

Construct H0 exactly as source lem:circulation: all three spokes of each t∈A, including spokes to roots. It has 3m edges. Let B be the TOTAL number of bounded faces of its connected components in their inherited plane embeddings. Thus B≤3m. For each such face take a simple path in that component's plane dual to its unbounded face. Each path contributes +1 or -1 to every crossed spoke, at most once. Summing yields INTEGERS a(t,v), with |a(t,v)|≤B. The source signed-boundary argument gives positive circulation on every counterclockwise simple spoke cycle. This is the same source construction with its elementary size bound, not a new positivity lemma.

Set w(t,v)=a(t,v)+B, so 0≤w(t,v)≤2B. For a state s put W(s)=sum_t w(t,s(t)). Its exponent lies in [0,d], where

    d=2mB ≤ 6m².

The shift is the same mB for every state; it changes neither orientation-weight differences nor source cancellation. The source existence of a pair entails a nontrivial spoke cycle, hence B≥1 here.

## 2. A nonzero polynomial over Gaussian integers

For every pair use EXACTLY the source disk phase

    J(r,s)=(1/3) sum_t δ(r(t),s(t)) ∈ Z,
    P(z)=sum_pairs i^{J(r,s)} z^{W(s)} ∈ Z[i][z].       (1)

Degree(P)≤d. Source Z(x) and (1) satisfy

    P(exp x)=exp(mB x) Z(x).

Thus P is not identically zero: the source common-phase minimum-cycle coefficient proves Z nonzero. In fact its order at z=1 equals the source c_min, since exp(x)-1 has a simple zero, but that observation and its Vandermonde counting use already occur in i164 and are not proposed again.

For a partial assignment σ of specified triangles to nonroot vertices, let P_σ be the same sum restricted to s extending σ. Repeated vertices or nonincidences simply give zero. This is a restriction of the original paired-state sum, not an assertion that the graph after deleting incidences meets the original triangulation hypotheses.

Source lem:cancel continues to apply to EACH fixed cyclic s: its partner involution changes r only. Hence

    P_σ(z)=sum_{s extends σ, Q_s forest, s partnered}
                  α_s z^{W(s)},                       (2)
    α_s=i^{J(r_s,s)} ∈ {1,-1,i,-i}.

Here a partnered forest state has a unique partner r_s. Source root-components puts one root in each Q_s tree. Its orientation with outdegree one at each nonroot and zero at roots must point toward the root; this uniquely recovers the r(t) tail. This uniqueness was already proved in the actual i164 original read here; it is credited accordingly. No arbitrary marked sum is asserted nonzero.

There are at most 6^m ordered facewise choices before imposing bijections. Therefore every coefficient of P_σ has absolute value≤6^m. For integer j≥2,

    |P_σ(j)| ≤ 6^m j^d.

Both real and imaginary parts are integers and use at most a constant plus m log2 6+d log2 j bits. These bounds concern representation, not efficient computation.

## 3. Pay the full adaptive restriction step

Suppose, solely to specify the unpaid computational interface, an exact evaluator E(T,w,σ,j) returns P_σ(j). Since a nonzero degree-d polynomial has at most d distinct roots, at least one of the d+1 integers

    j=2,3,...,d+2

has P(j)≠0. Retain such a j. At a triangle t not yet assigned, partition the pairs according to s(t). There are at most three incident choices v∈X, and exactly

    P_σ(j)=sum_v P_{σ union {t→v}}(j).                (3)

A nonzero parent value forces at least one nonzero child value. Choose it and repeat. After m steps a complete second state s remains with nonzero value. Equation (2) forces it to be partnered and Q_s to be a forest; uniqueness gives value α_s j^{W(s)}. Construct Q_s, orient it toward the three roots to recover r_s, and run the actual source white-tree/selected-edge recovery for the prescribed e0.

The extraction uses at most d+1+3m exact evaluations, always at the original graph and the SAME retained integer j after initialization. It does not require positive coefficients, nonvanishing of all restrictions, a fresh source invocation on damaged graphs, or a surjectivity claim about all Hamiltonian cycles. This pays the strongest elementary self-reduction compatibility; merely saying 'restricted source nonvanishing is unknown' would miss (3).

The conclusion here is a reduction to E, NOT a polynomial-time Hamiltonian-cycle algorithm. A single oracle output has polynomial bit length; no polynomial running-time implementation is yet supplied. For general source triangulations one could apply the source separating-triangle recursion and the facial prescription at each piece. The algebra above is only for each no-separating-triangle piece; it does not silently apply to arbitrary triangulations, and it does not use a sphere dual for nonplanar Pfaffian graphs.

## 4. Exact local rank-two factorization

We now actually evaluate E by the strongest elementary planar-dimer composition, rather than stop at an unnamed oracle. Put ζ=exp(iπ/6), so ζ³=i and ζ³+ζ^{-3}=0. Index the three corners of each bounded black triangle in counterclockwise order. The local ordered-pair kernel is

             [ 0       ζ       ζ^{-1} ]
    K =      [ ζ^{-1}  0       ζ      ].              (4)
             [ ζ       ζ^{-1}  0      ]

The factor z^{w(t,v)} and the condition σ apply to the COLUMN v (the second state), not the first. Source δ=+1 in the counterclockwise direction, so the product of these phases over faces is ζ^{sum δ}=i^J. Although individual factors live in Q(ζ), the paired sum lies in Z[i] by the actual source disk integrality.

K has rank exactly two. Its determinant is ζ³+ζ^{-3}=0, while the upper-left 2×2 minor is -1. More explicitly, if u_i∈Q(ζ)^2 and v_j∈Q(ζ)^2 are rows

    u1=(1,0),   u2=(0,1),   u3=(ζ^{-2},ζ²),
    v1=(0,ζ^{-1}), v2=(ζ,0), v3=(ζ^{-1},ζ),

then K_ij=u_i1 v_j1+u_i2 v_j2. The (3,3) entry is ζ^{-3}+ζ³=0. Root corners simply have no corresponding column in the incidence matrices below. The factorization holds before that restriction.

Let I be the planar bipartite incidence graph on A and X, obtained by deleting roots from the actual black-spoke graph. It has m vertices on each side and a perfect matching. Fix one planar Kasteleyn signing κ of its incidence edges. For each ε:A→{1,2} form two m×m matrices, with rows t∈A and columns x∈X:

    R_ε(t,x)=κ(t,x) u_{index_t(x), ε(t)},
    S_{ε,σ}(t,x)=κ(t,x) v_{index_t(x), ε(t)}
                    z^{w(t,x)} 1[x allowed by σ at t],       (5)

and zero for nonincidences. Then the exact identity is

    P_σ(z) = sum_{ε∈{1,2}^A} det R_ε · det S_{ε,σ}.    (6)

Proof: expand the product of the two-term decompositions (4) over faces. For each ε, the sums over independent bijections r and s factor into the two weighted incidence permanents in (5) without κ. Importantly, allow r(t)=s(t) in this expansion: those terms vanish after summing ε because K_ii=0. Each planar signed determinant equals its corresponding permanent times the SAME fixed sign η∈{±1}, independent of weights, including zeros and complex weights. Multiplying gives η²=1. This proves (6) as a polynomial identity, including all partial assignments σ. No unsupported deletion-contraction identity for the source is used.

For clarity, the standard determinant sign step can be checked directly. On each bounded facial walk of I, choose sign product (-1)^{length/2+1}; these mod-two equations are realizable by paths in the connected component's dual to its unbounded face. Bridges appear twice and do not affect the equations. For a simple alternating cycle of length 2h with V_int vertices strictly inside, multiplying face equations and using disk Euler gives product of signs (-1)^{h+V_int+1}. An alternating cycle of two perfect matchings has a perfectly matchable interior, so V_int is even. Thus the edge-sign ratio is (-1)^{h+1}, cancelling its determinant-permutation ratio (-1)^{h-1}. Symmetric differences of matchings split into such cycles, so η is common. In disconnected I perform this per component; existence of a matching balances each component. This is the classical matching sign operation, also present in the original i190/i191 overlap sections, not a new topological selector.

Equation (6) gives a 2^m times polynomial arithmetic procedure for E. Entries lie in the fixed degree-four number field Q(ζ), with ζ satisfying ζ^4−ζ²+1=0. At the bounded integer evaluation points all exponents and bit lengths are polynomial in m; summation and determinant arithmetic introduce no unbounded precision assertion. Combining with §3 still has the 2^m factor. It is a correct candidate REDUCTION, not a claim of a better algorithm or a mathematical discovery nomination.

## 5. Why the immediate single-determinant shortcut is not paid

Kenyon's actual scalar double-dimer formula is a product of two independently weighted matching sums. At a face such a term gives a rank-one local kernel p_i q_j. It cannot equal (4), even after the nonzero column weights at j≥2: (4) has rank two. More basically, setting all diagonal p_i q_i to zero while keeping all six offdiagonal values nonzero is impossible. This is a narrow obstruction to direct scalar factorization at unchanged incidences, not a lower bound for all algorithms or all gadgets.

The SL2 connection formula read in Kenyon does not automatically remove shared incidence edges either. A doubled edge in that formula has scalar weight ν(e)^2, independent of the connection; its backtracking monodromy is the identity. The source instead requires r and s to be edge-disjoint. One cannot merely identify the source orientation product with the SL2 double-dimer partition and discard the doubled terms. Singular matrix weights, cancellations between auxiliary gadgets, or a different exact identity would require a complete compatibility argument. No such argument is supplied or ruled out here. Equation (6) handles the diagonal zeros exactly, at the explicit exponential cost.

Compressing the 2^m coupled rank-two choices, or obtaining a polynomial exact evaluator for the restricted P_σ values by another method, is the concrete unpaid operation for this route. We do NOT claim such an evaluator is necessary for every conceivable first-cycle algorithm, impossible, new as a problem, or computationally hard on this promised input class.

## 5a. Stronger compression attempt: one determinant, exact squarefree filter

The rank-one obstruction does not end the analysis. Introduce one formal variable q_t for every t∈A. Define an m×m matrix L(q,z) on X by

    L_uv = q_t ζ^{−δ(u,v)} z^{w(t,v)} 1[v allowed by σ at t]

when u≠v are joined by the side of black triangle t∈A, and zero otherwise. Each edge has exactly one black owner, so this is unambiguous. Let [q_A] mean coefficient of product_{t∈A}q_t. Then

    P_σ(z)=(-1)^m [q_A] det L(q,z).                  (7)

To prove (7), a squarefree determinant term chooses each vertex once as tail and head AND each black face exactly once. Consequently it specifies exactly one source pair (r,s), with s respecting σ; conversely every pair yields one term. If its permutation has c cycles, its determinant sign is (-1)^{m-c}. The disk identity gives J as the sum of c numbers each +1 or -1, so J≡c mod2. The reversed local phase in L is i^{−J}=(-1)^J i^J. Multiplying both signs gives (-1)^m i^J, exactly (7). This is why the phase in L is conjugated; using the original phase without the permutation-sign correction would be an error.

The determinant is homogeneous of total degree m in the q variables. Hence ordinary inclusion–exclusion gives the FULL exact formula

    P_σ(z)=(-1)^m sum_{S⊆A} (-1)^{m−|S|} det L(1_S,z).   (8)

Indeed the signed evaluation sum kills any monomial missing a variable. A degree-m monomial using all m variables must be squarefree. This pays the evaluator using 2^m SINGLE determinants, rather than the products in (6); it does not remove the exponential factor. Restricting σ only changes the local column masks, so (7)–(8) remain valid throughout the adaptive extraction.

Setting every q_t=1 without extracting the squarefree coefficient is actually wrong, including for weights built by the source circulation algorithm. Here is an explicit bounded check with enough data to reproduce the arithmetic. Use the sphere bipyramid on rim 0,...,5, top apex6, bottom apex7, outer black face (6,0,1). Its remaining counterclockwise black faces in order are

    (6,2,3), (6,4,5), (7,2,1), (7,4,3), (7,0,5).

There are m=5 nonroots X=(2,3,4,5,7) and B=3 bounded H0 faces. The shifted incidence weights in those respective corner orders are

    (3,3,3), (4,3,3), (3,2,3), (3,3,3), (2,3,3).

Subtract B=3 to recover a. The combinatorial white-face rotation calculation in artifact/exact_calculation.py verifies boundary circulation +1 at each bounded face and -3 at the unbounded face, so these are actual permitted source weights. There are three states and two ordered disjoint pairs. Direct expansion gives

    P(z)=i(z^13−z^15),
    [q_A]det L(q,z)=i(z^15−z^13),
    det L(1,z)−[q_A]det L(q,z)=2i(z^14−z^15),
    det L(1,z)=−i z^13(z−1)^2.

At z=2 the squarefree coefficient is 24576i, but the raw determinant is -8192i; the repeated-face remainder is -32768i. The cube's corresponding remainder happens to vanish, so testing only that base would miss the defect. This is not a claim that every raw determinant is zero or that its nonzero values are useless: it is the precise failure of replacing the needed coefficient by unfiltered evaluation. Determinant additivity also does not justify the adaptive identity (3) for this unfiltered object, since it can use a face zero or multiple times.

A polynomial way of performing or bypassing this specific squarefree filter with all needed partial-state conditions is still unpaid. The source nonzero leading coefficient and the classical planar matching determinants do not themselves supply that operation. No general lower bound, impossibility theorem, or alternate target is asserted.

## 6. Strongest primary composition and comparison

BKN §§2.2–2.5 provide a distinct fully paid completion method. For a FIXED Pfaffian orientation and anchor edge e=st of a bipartite graph, assign λ:L→{0,1}, λ(s)=0. Their graph F_λ has vertex set V(G)×{0,1} and explicitly prescribed port/parity incidences. Lemmas14–15 give

    PM(F_λ) nonempty  iff  λ extends to a good anchored coloring.

A matching produces the Hamiltonian cycle in linear time. Trying all 2^{N/2−1} half-colorings with ordinary bipartite matching is already an exact exponential first-cycle method. In the full finite simple cubic 3-connected bipartite Pfaffian source class, any anchor lies in a three-edge path (choose another neighbor at each endpoint; bipartiteness makes the four vertices distinct), and the source P4 corollary guarantees a successful λ. This guarantee is the routine specialization already excluded as a nominee by the brief.

For the planar no-separator piece, N/2−1=m, so (6) does not improve even this elementary half-coloring enumeration exponent. BKN §4 further uses four-state dynamic programming over path/branch decompositions and planar width bounds to obtain subexponential planar algorithms. The actual §4 proof was read, not inferred from an abstract; its planar separator/decomposition antecedents were not separately acquired, and no independent derivation of those complexity constants is claimed here. Their existence also prevents advertising (6) as algorithmic progress.

BKN's linear-time second-cycle proof and Corollaries4–5 already pay four cycles through each realizable edge and at least six in the cubic Hamiltonian case. Its switching needs H to construct the good half-coloring and matching. Source existence plus switching does not generate the initial H in polynomial time. A matching on the source incidence graph gives a pair by flow, but that pair need not have Q_s forest; simply using it to seed BKN would assume the missing first cycle. The source white-tree recovery requires precisely the forest condition.

## 7. Prescriptions are not silently enlarged

No assertion about arbitrary two prescribed paths, robustness under deleted vertices/edges, or arbitrary longer paths follows from the above. A universal four-edge-path extension is already false even in the cube Q3. In binary labels take

    100–110–010–011–001.

The unused vertices are 000,101,111; the last two have an edge between them, while 000 has no neighbor among them. In any Hamiltonian cycle containing the displayed path, 000 must use both endpoints 100 and001, since its other neighbor010 is internal to the fixed path and already has degree two. Those forced edges close a six-cycle on the displayed five vertices and000, excluding101 and111. Hence no Hamiltonian cycle contains that path. Q3 is finite simple cubic bipartite planar and 3-vertex-connected. This small check is a diagnostic already consistent with GSW's explicit non-P5 discussion, not a nominated result or a claim of priority.

The old affine-span/counting U_C4 obligation is not approached by weakening it to any statement above. Source restricted-state nonvanishing already studied in i188–i195 is not renamed as a new theorem. Here adaptive restriction is paid by additivity AFTER exact evaluation; it provides no new survivor-population inequality, quotient-sign result or moment/channel operation.

## 8. Outcome

PREFREEZE / no nominee. The sustained calculation closes integer normalization, polynomial degree/bit bounds, exact adaptive restriction/recovery, the full rank-two-to-2^m-determinants identity, and the stronger single-determinant squarefree-coefficient/inclusion–exclusion identity. These are source operations plus elementary linear algebra, classical planar matching signs and standard self-reduction. There is no isolated additional nonroutine operation after the strongest compatible source/primary composition. Polynomial exact restricted evaluation remains unpaid; it is not submitted as a conditional finding. No exhaustion, priority, independent gate or count is claimed.
