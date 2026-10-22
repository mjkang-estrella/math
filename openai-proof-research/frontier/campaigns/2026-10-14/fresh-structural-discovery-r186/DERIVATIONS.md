# Structural r186 — prefreeze derivations

Provenance: Codex / GPT-6 Astra / high / default service tier. These are discovery calculations, not a frozen nominee, author-proof submission, or a mathematical self-grade. All homology below is augmented reduced homology over Q, including degree −1. The pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb and all its operative proofs are stipulated true.

The complete source text and the operative primary interfaces recorded in private/READING-LIMITS.md were read before this document was drafted. The additional Díaz Ramos 2018 v1 coefficient calculation was a late primary read, after the direction and test group had been considered but before this extended drafting. It already contains the test group below. No theorem was frozen.

## 1. The operation investigated

Retain actual spaces of frame coefficients through restriction, faithful-component propagation, and overlap of conjugate component configurations. The ambition was an explicit multiplicity operation valid across the complete source construction, not merely a second proof of nonvanishing or a top-degree claim. Three different maps have to be distinguished:

1. an injective map from frame/decorations parameters to actual cycles;
2. fixed-complement residue maps into an inner extension;
3. the map from local cycles, multiplied by centralizer homology, into the ambient group.

The source pays (1), existential detection in (2), and single-class detection in (3). Linearizing (3) is successful. Linearizing all residues in (2) is also successful, but does not make a single residue injective. None of those observations supplies the ranks of overlap/attachment maps across distinct configurations. The calculations below retain all these interfaces explicitly.

## 2. Simultaneous propagation at a fixed extension

Fix a finite group G, prime p, and nonabelian simple component L. Let S be a nonempty collection of faithful configurations A, all of rank r, such that LA is the same subgroup H for every A in S. Put K=C_G(H). Require for every A in S the two exact source conditions:

(i) every order-p element in C_L(A) belongs to A;
(ii) there is no elementary D>A with C_LD(L)=1 and O_p(C_G(LD))=1.

Let W be any finite-dimensional space of cycles of degree r−1 in A_p(H). It is enough that the coefficient map e:W→Q^I be injective, where I is any collection of saturated flags of ranks 1,…,r ending at members of S. W need not be supported exclusively on those flags. In particular, for an arbitrary W one can choose a vector-space complement to ker(e); the dimension actually retained is rank(e), not automatically dim(W).

Define D to be the UNION, over A in S, of {D>A:C_D(L)=1}. Delete D in descending order. At a deletion D, choose A contained in D. The source faithfulness-upgrade lemma makes LD faithful; (ii) makes O_p(C_G(LD)) nontrivial. Every remaining E>D has C_E(L) nontrivial, since otherwise it lies in the same union and has already been removed. Thus the exact source maps

q_D(E)=C_E(L),   j_D(P)=DP

identify the remaining upper interval up to homotopy with A_p(C_G(LD)), which is contractible. The maps obey q_D j_D=id and j_D q_D≤id. Hence the final X has the homotopy type of A_p(G).

Crucially this union deletion does not remove any pure vertex U of A_p(H). If it did, U>A for some A in S, and LU=H would contradict (ii), since H is faithful and O_p(K)=1. Every product UV with V≤K nontrivial survives because C_UV(L) contains V. The whole product construction, including chains used to change representatives in K, therefore lies in X.

For each σ in I ending at A, all E in X_{>A} have nontrivial C_E(L). The maps q_A(E)=C_E(L) and j_A(P)=AP are the same retraction as in the source. For α∈W and a cycle β of degree b in A_p(K), the source shuffle identity gives

q_A R_σ(α ⊠ β) = e_σ(α) β.                     (2.1)

There is no hidden mixed term here: all r vertices of σ lie in H; uniqueness of the product coordinates and the fact that α has exactly r vertices force the shuffle to take every H step first. Its sign is +1. Also R_σ ∂ = (−1)^r ∂R_σ, so boundaries remain boundaries under this detector.

For a sum z=Σ_i α_i⊠β_i, if z bounds in X, equation (2.1) gives Σ_i e_σ(α_i)[β_i]=0 for every σ. Since e is injective, e⊗id is injective over Q, and the original tensor is zero. Changing β by a boundary changes z by a boundary, by the shuffle differential. Consequently the actual shuffle map induces an injection

W ⊗ H_b(A_p(K);Q) → H_{r+b}(A_p(G);Q).         (2.2)

Degree bookkeeping: (r−1)+b+1=r+b. The argument also handles b=−1. In that case A_p(K) is empty when its augmented H_{−1} is nonzero; the upper intervals in (2.1) are empty too. No assertion about top degree of G is made.

If a finite subgroup of N_G(L)∩N_G(H) preserves S and W, this construction is equivariant for that subgroup: the deletion union, shuffle and collection of residues are equivariant (individual residues are permuted). The resulting rational submodule has a complement by averaging. This does not assert projectivity over F_p, a G-module induced-summand statement, or anything about orbit-space homology.

Payment comparison: this is the simultaneous coefficient version of Source310 §3 and Piterman 2021 Lemma 3.14, with the Z-left compatibility supplied more generally by Piterman–Smith 2025 Theorem 5.10. It is not being offered as a substantial new theorem. The successful union deletion is important: it rules out an artificial gap claiming that different supported flags at the SAME H necessarily require incompatible deletions.

## 3. Quantitative symplectic application, with its exact scope

Let O_2(G)=1 and let L be a nonabelian simple component isomorphic to PSp_{2n}(q), n≥3, characteristic(q)≥5. Use exactly the source §7 family of faithful configurations containing a plane-sign/quaternion seed. It is nonempty by component-core and closed under qualifying elementary enlargements. Choose its maximum rank r. The source centralizer and cyclic outer-field calculations give r=n+1+ε, ε∈{0,1}; H=L when ε=0 and H/L=C_2 when ε=1. In the latter case q=u², u≥5. In the former use u=q.

The source's local §7 construction uses only these conditions, maximality, and the displayed linear/semilinear calculations. Its invocation of minimal-counterexample induction occurs at ambient propagation, which (2.2) replaces. Thus this application does not assume that G itself is a minimal counterexample. It also does NOT export the source's global minimal-counterexample classification to an arbitrary G.

Let N be the number of full data in the actual source family inside this H. This is a finite subgroup/decoration count, not a freely variable parameter. The actual chain map is injective because the commutator radical recovers the sign group, its eigenspaces recover the plane frame, and flags through all three quaternion lines (and the field axis when present) recover the local coefficients. There is no restriction from an overgroup in this case. Set

f_3=3/8,   f_n=(17/25)^n for n≥4,
k_T=(u−χ_u(−1))^n/4,   k_B=2^{n−1}.

The source frame and quaternion-decoration estimates give a space V of actual cycles, every supported top group in the same maximal family and generating H, with

dim(V) ≥ 2N(n−1)![ f_n − 3/(2k_T) − ε/k_B ].  (3.1)

All full-flag coefficient evaluations detect V. Applying (2.2), for every integer b≥−1,

β_{n+1+ε+b}(G) ≥ ceil(2N(n−1)![ f_n − 3/(2k_T) − ε/k_B ]) β_b(K),
K=C_G(H).                                                  (3.2)

The source headline supplies some nonzero β_b(K), since O_2(K)=1, but it does not identify b. Formula (3.2) is a concrete local-data bound, not an explicit formula for all Betti numbers of G. The bracket is positive by the source's inequalities. At n=3,u=5,ε=1 it is at least 3/8−3/32−1/4=1/32, so the integer factor is at least ceil(N/8). This is the actual two-dimensional quaternion coefficient gain; replacing it by one scalar would give the wrong estimate.

This is a fully compatible quantitative consequence of the stipulated source and the classical full-chain mechanism. Merely retaining a dimension estimate already present in the source is not the requested nonroutine bridge. It is retained here as strongest payment, not as a fallback nominee.

## 4. Restriction as a jointly injective family

Let M be finite, H≤M, m≥1, and 0<c<m. Let Z be a space of cycles in degree m−1 on saturated flags ending at rank-m elementary groups E, all satisfying [E:E∩H]≤p^c. Neither m=m_p(M) nor normality of H is required. Let Z_{<c} consist of cycles with zero coefficients at every top E of index p^c.

For every saturated rank-c flag σ ending at R with R∩H=1, take its residue and intersect the suffix vertices with H. Restrict to the finite collection T of flags occurring in the support universe of Z; others give zero. Call this linear map J_σ. On every contributing suffix vertex B, the source index sandwich gives

p^c=|R|≤[B:B∩H]≤[E:E∩H]≤p^c,
so B=R×(B∩H).                                      (4.1)

Thus intersection is an injective simplicial map on the entire suffix-support subcomplex for this fixed R, with inverse U↦RU. The residue is a cycle; its image is a cycle of degree m−c−1 on full flags in H. A cycle supported at lower-index E cannot contain R, hence J_σ vanishes on Z_{<c}.

Conversely, take z outside Z_{<c} and a nonzero coefficient at a top E of index p^c. Deleting the top E from its incident full flags gives a nonzero building cycle. The source opposite-chamber lemma, applied to E∩H, gives a supported full flag passing through a rank-c complement R. Its initial σ has J_σ(z)≠0 by (4.1). Therefore

ker( ⊕_{σ∈T} J_σ ) = Z_{<c}.                      (4.2)

In particular, putting d=dim(Z/Z_{<c}), t=|T| and W=Σ_σ im(J_σ),

d≤Σ_σ rank(J_σ)≤t dim(W),
so dim(W)≥ceil(d/t).                                (4.3)

The stronger computable object is the rank of the stacked actual matrices J_σ, not the coarse divisor t. If c=0, restriction is simply the identity on Z inside H. No nonzero homology conclusion for W follows without an additional top-rank or propagation detector.

For source linear/unitary constructions with constant maximal index, all top intersections have the stated rank and generate the same H; the source's good-configuration verification makes full coefficient evaluations available in §2. For orthogonal q=5 the admissible-color selection matters: after taking all residues, restrict coefficient evaluation to flags ending at admissible maximal-family groups. Write e_good for that map. Only rank(e_good|W), not dim(W), can be inserted into (2.2). The source states existence of a nonzero admissible coefficient, but its actual exclusion proof supplies a quantitative kernel bound, as developed next. A complement to the good-evaluation kernel may still contain other top groups in its support; §2 deliberately allows this. No lossless restriction is asserted.

## 4.1. The actual orthogonal exclusion proof also pays a rank bound

It would be premature to leave the good-flag detector as a named gap. Reapply the already-read Source310 Lemma orthogonal-five-colors to the SUBSPACE of assignments vanishing at all admissible frames. The two-minority comb argument is linear and applies to each such assignment; its dimension estimate bounds that kernel, not only the whole-space contradiction used in the source's statement.

Use N for the natural orthogonal dimension, M for the number of all line frames, and C for the source space of actual sign-cycle coefficients. For odd N≥5 or even N≥8, square determinant over F_5, put

f_N=(17/25)^N,
g_5=5/36,
g_N=N/[4(N−2)!] for odd N≥7,
g_N=N/[2(N−2)!] for even N≥8.

The actual source proof yields

dim(C)≥f_N M(N−1)!,
dim(ker(e_admissible|C))≤g_N M(N−1)!.

For N=5 the factor 5/36 includes the three-term mixed-plane relations, whose row supports cover all formal coordinates and have size at most three; omitting this would fail to give the needed positive gap. Thus the rank of admissible full-flag evaluation is at least

d_adm = M(N−1)!(f_N−g_N)>0.                      (4.4)

Fix the same H and quotient B=H/L as in the source. Every admissible sign group E has index [P:B]=2^c and all sign groups have index at most 2^c, with 0≤c≤2. Hence one c works simultaneously for the whole coefficient space. Here m=N−1 and r=m−c is the selected maximal faithful-family rank. Every admissible E∩H belongs to that family and generates H with L; these are the exact source checks, not assumed for arbitrary frames.

Let e_good evaluate output cycles on all full flags whose top belongs to these admissible-intersection configurations. Form W=Σ_σ J_σ(C), using all rank-c complement flags in the actual sign support universe (for c=0 use one identity map). If every e_good J_σ(z) vanishes, then z has zero coefficient at EVERY admissible top E: otherwise the local opposite-chamber argument at that E gives a complement flag σ and a surviving full coefficient ending at E∩H, contradicting the assumption. Consequently the kernel of the stacked maps e_good J_σ is contained in ker(e_admissible), so their joint rank is at least d_adm. If there are t residues, their common target e_good(W) therefore has dimension at least ceil(d_adm/t).

Choose V⊂W complementary to ker(e_good). Apply §2 at this SAME H to obtain, for every b≥−1,

β_{r+b}(G) ≥ ceil(M(N−1)!(f_N−g_N)/t) β_b(C_G(H)).       (4.5)

For c=0, t=1. For c>0, an explicit upper bound eliminates even the enumeration of distinct complement flags. A rank-m sign group of index 2^c has 2^{c(m−c)} complements to E∩H, and each rank-c complement has ∏_{i=1}^c(2^i−1) full flags. Groups of smaller index have none. Counting with repetition over all frames is an upper bound, so

t≤M 2^{c(m−c)}∏_{i=1}^c(2^i−1).

One may replace the integer factor in (4.5) by

ceil((N−1)!(f_N−g_N) / [2^{c(m−c)}∏_{i=1}^c(2^i−1)]),   (4.6)

with empty product one and the same bound valid when c=0 (then (4.5) is stronger by M). The number of complements follows by writing each as the graph of a linear map from one fixed complement to E∩H; the flag count follows by successive one-dimensional quotients. These are explicit positive local-data bounds. No global degree of nonvanishing is inferred, since b remains the centralizer degree. No top-degree claim about G is used.

The calculation pays the admissible-color interface quantitatively, with all representatives still inside the source's exact selected family. It is another direct linearization of a paid dimension argument; it is not the sought cross-extension independence operation. In particular, leaving orthogonal good-flag EXISTENCE as an unpaid step would understate the strongest available source proof.

## 5. Explicit simultaneous-residue calculation

Take p=2, M=S_3×S_3 and H=C_3×S_3 (normal of index two). Label the three transpositions in each factor t_1,t_2,t_3 and s_1,s_2,s_3. Write x_i=<(t_i,1)>, y_j=<(1,s_j)>, z_ij=<(t_i,s_j)> and E_ij=x_i y_j. The elementary abelian poset has 15 rank-one vertices and nine rank-two vertices, with exactly the 27 incidences x_i<E_ij, y_j<E_ij, z_ij<E_ij. Each z_ij is a leaf. Removing these leaves and suppressing the E_ij subdivisions leaves K_{3,3}, so H_1 has dimension 9−6+1=4 and reduced H_0 is zero. There are no rank-three groups because a 2-Sylow has order four.

A_2(H) consists of y_1,y_2,y_3, so its reduced H_0 has dimension two. All E_ij have index [E_ij:E_ij∩H]=2, with m=2,c=1. Define a_i=[x_i]−[x_3], b_j=[y_j]−[y_3] for i,j∈{1,2}. In the product shuffle α_ij=a_i⊠b_j the elementary two-step term is

[x<E_xy]−[y<E_xy].

These four cycles are independent and form H_1. For residues at the three x_k, in the bases a_1,a_2 and b_1,b_2, the stacked map is

J = [[1,0],[0,1],[-1,-1]] ⊗ I_2.                   (5.1)

Its rank is four, whereas each individual two-row block has rank two. Residues at z_ij vanish on the entire cycle space: their incident leaf-edge coefficients are zero. Thus no single complement residue can preserve the four-dimensional space. All residues together do detect it. This is a statement about this precise operator, not a counterexample to the classical-component hypotheses, nor an impossibility result about all alternative constructions.

Díaz Ramos 2018 v1 Example 4.9 already uses the isomorphic group (C_3×C_3)⋊(C_2×C_2). His equations (14) are the row and column sums of the 3×3 coefficient matrix c_ij. Their rank is five (one row/column dependency), and their kernel dimension is four. The source's vector-valued decoration count explicitly cites his equation (17). This model is therefore classical payment, not a new finding. The exact script in private/model_calculation.py enumerates the 36-element group and verifies the stated chain/residue matrices over Q; the preceding graph proof supplies the mathematics independently of that calculation.

## 6. Relative attachments pay more than a formal spectral-sequence name

For a finite group G with N normal, put Q={B∈A_p(G):B∩N≠1}. Intersection with N retracts Q up to homotopy onto A_p(N): B∩N≤B and the inclusion is a section. Filter the rest by exterior rank:

X_0=Q,   X_r=Q ∪ {E:E∩N=1, rank(E)≤r}.

For each newly attached rank-r E, its link in X_{r−1} is the join of the proper nonzero subspace building B(E) with Q_{>E}. Indeed all proper subgroups of E are exterior and already present; any upper vertex already present lies in Q. Distinct newly attached rank-r vertices are incomparable, so the relative chain groups split over E. The maps B↦B∩N and P↦EP give Q_{>E}≃A_p(C_N(E)); the comparison EP≤B when P=B∩N verifies this on actual posets. Empty upper intervals are handled by augmented joins.

Attaching the cone on that link shifts homology once, so the rank-r relative group in total degree r+s is

H_{r+s}(X_r,X_{r−1};Q)
 ≅ ⊕_{rank(E)=r, E∩N=1} St(E) ⊗ H_s(A_p(C_N(E));Q),       (6.1)

where St(E)=H_{r−2}(B(E);Q), dimension p^{r(r−1)/2}. For r=1 this is the empty building, St(E)=Q in degree −1. Formula (6.1) is about relative groups. It is not a direct-sum decomposition of H_*(G).

The resulting finite homological spectral sequence has column zero H_s(A_p(N)) and columns r≥1 as in (6.1), total degree r+s. Its first differential takes panel residues of a building cycle along each rank-(r−1) F<E and applies the actual inclusion C_N(E)≤C_N(F) to the centralizer homology. The signs are those of deleting the appropriate vertex in the oriented full flag. For r=1 the endpoint map is the sum of inclusions into N. Compatibility follows from the common intersection map B↦B∩N; the comparison EP↦FP makes the local retractions commute up to the poset comparison. Higher differentials have bidegree (−k,k−1). This supplies an identifiable chain construction and differential, but no assertion that all higher differentials vanish.

When every exterior elementary subgroup has rank one, there are only columns zero and one. The entire operation is the Segev–Webb main theorem: if

u_s: ⊕_{E exterior, rank(E)=1} H_s(A_p(C_N(E))) → H_s(A_p(N))

is the sum of actual inclusions, the long exact sequence gives, for n≥0,

β_n(G)=β_n(N)−rank(u_n)
       + Σ_E β_{n−1}(C_N(E))−rank(u_{n−1}).         (6.2)

All terms are reduced/augmented. This formula makes the unpaid quantity explicit rather than hiding it behind an undefined differential. The primary theorem and its complete author-version proof were read; the published statement's inclusion formula was also checked visually. The published wreath-product sphere count was read with the author's correction. The induced modules in Segev–Webb belong first to the cofiber/relative group. Passing directly from those induced modules to an ambient direct summand is unjustified.

In the model of §5 take N=H. There are 12 exterior cyclic groups: three x_i and nine z_ij. For x_i, C_N(x_i)=1×S_3, and inclusion induces the identity on Q² in reduced degree zero. For z_ij, C_N(z_ij)=1×<s_j> and the complex is contractible. Therefore

u_0=[ I_2  I_2  I_2 ]: Q^6→Q²,
rank(u_0)=2,   ker(u_0)=im(J), dim=4.             (6.3)

No other reduced homology contributes. Equation (6.2) gives β_1(G)=6−2=4 and β_0(G)=2−2=0. Thus the actual classical attachment relation is exactly the relation among the three complement residues: their sum is zero. This integrates the restriction mechanism with the primary relative extension operation, rather than merely listing them side by side.

## 7. Attempted global assembly and precise unpaid operation

For distinct conjugate extensions H_j=L_j A_j with centralizers K_j, construct the actual map

Φ: ⊕_j V_j⊗H_{b_j}(A_p(K_j)) → H_d(A_p(G)),
Φ((v_j⊗β_j)_j)=Σ_j [v_j⊠β_j],   r_j+b_j=d.

Each individual summand can inject by §2. This alone says nothing about injectivity of their sum. A common deletion union used for several different H_j need not preserve every other summand's pure H_i vertices; the fixed-H proof used LA=H at exactly that point. Even without deletions, residues from one configuration can read mixed contributions from another product subgroup. The actual overlap entries are R_σ(v_j⊠β_j), followed by a centralizer retraction only on those suffixes for which that map is defined. They cannot be set to zero merely because the top-group labels differ.

The strongest assembly available here is therefore the actual filtered chain system of §6 (and, for the source exceptional case, its already-paid equivalent-poset/prejoin construction), together with the explicit detector quotient of §4. A uniform explicit multiplicity conclusion across all the source configurations would require a bound on the rank of these attaching/overlap maps, after the fixed-H restriction/detection bounds of §§4–4.1 have already been paid, and control of any higher filtration differentials. It would have to handle the actual compatibility of representatives, not an abstract vector-space choice pretending to be a common chain model.

The rank-one example pays the entire inclusion map rather than leaving it named: it is surjective of rank two and produces exactly the four-dimensional simultaneous residue space. It also demonstrates why erasing inclusion maps gives the wrong answer (six instead of four). The source's exceptional prejoin removes some comparisons precisely to solve its stated existence problem, and Piterman 2026's equivalent-complex proof verifies support inside its replacement complex; neither gives a general zero-overlap assertion for Φ. Source classical reductions concern hypothetical acyclic counterexamples. Reusing them for an arbitrary group with small but nonzero homology would be a further unsupported step.

No nonroutine full-scope rank/control operation was closed. The compatible fixed-H injection, symplectic numerical bound, quantitative orthogonal detector bound, joint-residue kernel calculation and classical attachment filtration above are retained as paid reductions. They are not substituted for a failed older frozen target, nor offered as a restricted nominee. Disposition: PREFREEZE/no nominee, without any claim of exhaustion or global impossibility.
