# Author-side antecedent: ω-stability already supplies the full qualitative profile cover

Status: complete author derivation from the cited classical primary theorem, not an independent contribution review. The conclusion is the entire local profile theorem used in the094 construction. There is no remaining qualitative hypothesis to be supplied by the new Fourier/feature proof. No stronger quantitative replacement is proposed.

## Exact primary input

Ben Yaacov–Berenstein–Henson, *Model-theoretic independence in the Banach lattices Lp(μ)*, 14 August2009 version, supplies:

* Fact3.2: the atomless real Lp Banach lattices, for a fixed p, share one theory T_p.
* Fact3.3 and the universal-domain discussion: models of this theory are atomless real Lp lattices; sufficiently saturated universal domains exist. The introduction identifies the equivalence with continuous first-order logic, so its compactness theorem applies.
* Definition3.13 and Theorem3.15: over every countable parameter set A, the space of one-types is separable for the metric obtained by taking the infimum of ||u−v|| over realizations of the two types. In particular, it cannot contain uncountably many types separated by one fixed positive distance.

We only use that metric ω-stability, ordinary compactness, and a finite combinatorial argument below. Remark3.16 separately treats atoms, but we do not need its theory-by-theory constants. All uniformity comes from the single atomless theory.

The continuous-NIP assertion in Hrushovski§2.16 is **not** needed. RandomVC Theorem2.11 gives finite fixed-margin shattering dimension, but this note does not infer a polynomial supremum-metric cover from that statement alone. The stronger ω-stability input has a direct route.

## 1. Uniform finite binary splitting depth

Fix p>1, an integer B≥1 and an integer m≥2. On bounded variables define

    φ(u,a)=||u−a||/(B+1),       ||u||≤1, ||a||≤B.

Its values lie in [0,1]. A binary splitting tree of depth d consists of a center a_s and an integer k_s∈{0,…,m−1} at each node s∈{0,1}^{<d}, and a unit-ball witness u_σ for every leaf σ∈{0,1}^d. For every node s along σ, require

    φ(u_σ,a_s)≤k_s/m          if the next bit is0,
    φ(u_σ,a_s)≥(k_s+1)/m      if the next bit is1.             (1)

There is a finite bound d_*=d_*(p,B,m) on such depths, uniformly over all atomless Lp spaces.

Proof. Suppose depths were unbounded. The possible integer labels k_s at a fixed finite depth form a finite set. Call a labeling admissible if its finite tree can be witnessed in a model of T_p. Restriction preserves admissibility. The tree of admissible labelings has finite branching and arbitrarily large depths. König's lemma gives an infinite coherent labeling, every finite initial tree of which is admissible.

Use compactness to realize centers a_s for all finite binary strings, and witnesses for every finite path, in one model of T_p. This is legitimate: any finite subset of the requirements is witnessed by a sufficiently deep admissible finite tree; a shorter-path witness may be chosen from a leaf extending it. The center bounds and query bounds are included. The thresholds and normalization are rational, so these are bounded continuous norm conditions without an extra real-parameter sort.

Let A be the countable set of these centers. For each infinite branch β, its path conditions(1) are finitely satisfiable. In a sufficiently saturated elementary extension they determine at least one complete one-type q_β over A, realized by a unit-ball element. If β and β′ first split at s, any realizations u,v of their respective complete types satisfy

    | ||u−a_s||−||v−a_s|| |≥(B+1)/m.

The reverse triangle inequality therefore gives ||u−v||≥(B+1)/m, for every pair of realizations preserving their types over A. Hence

    dist_type(q_β,q_β′)≥(B+1)/m.                             (2)

There are continuum many branches, so(2) contradicts the separability asserted by Theorem3.15. Thus d_* is finite. This is a qualitative bound depending only on the fixed theory, B and m, not the model or any finite center set.

## 2. Arbitrary measure spaces have the same finite-tree bound

The preceding argument is uniform for all real Lp(μ), including measures without a global σ-finiteness hypothesis.

Indeed, any finite tree involves only finitely many centers and witnesses. Each of these integrable functions is supported, up to a null set, on a countable union of sets {|f|≥1/k} of finite measure, since μ{|f|≥1/k}≤k^p||f||_p^p. The union S of the finitely many supports is σ-finite. Restricting to S preserves every norm and distance of this configuration. The map

    f(s) ↦ f(s)  on S×[0,1]

is a linear lattice isometry into the product Lp space with Lebesgue probability on[0,1]. This product is atomless: a finite-positive-measure set can be split continuously by the second coordinate, by Fubini; σ-finiteness supplies such subsets when needed. A harmless extra standard atomless summand can be included if S is null. Thus any finite tree in any original Lp would give the same tree in a model of T_p, contradicting its bound d_*.

No common σ-finite support for an arbitrary uncountable U is required. The reduction is only for the finite witness configurations defining splitting depth. No global product construction for a non-σ-finite original measure is assumed.

## 3. Finite splitting rank gives a polynomial profile cover

This step is purely combinatorial. Let S be any subset of [0,1]^N. Suppose all splitting trees using its coordinates and thresholds k/m as in(1) have depth≤d_*. For a nonempty subset C⊂S define rank(C) to be its largest such depth, an integer in{0,…,d_*}. A depth-zero tree is just one witness, so every nonempty class has rank≥0. Put rank(∅)=−1.

Partition [0,1] into m+1 bins:

    I_j=[j/m,(j+1)/m), j=0,…,m−1;       I_m={1}.

For each coordinate i and nonempty current class C, let C_{i,j}={z∈C:z_i∈I_j}. Choose j_i(C) to be the least index among the nonempty bins with maximal rank. Predict the i-th value by j_i(C)/m.

If z∈C is an unknown target profile and its actual bin j at coordinate i has |j−j_i(C)|≥2, replace C by C_{i,j}. Then

    rank(C_{i,j})<rank(C).                                  (3)

To prove(3), suppose rank(C_{i,j})=rank(C)=r. Maximality forces the predicted bin also to have rank r. The two bins are separated by a gap at least1/m. If their lower index is l, the lower bin lies in {z_i≤(l+1)/m}, and the upper bin in {z_i≥(l+2)/m}. A new root split at k=l+1 joins their depth-r trees to a depth-(r+1) tree in C, contradiction. The chosen threshold belongs to{0,…,m−1}, including when the upper bin is I_m.

Start with C=S. Whenever any coordinate has actual and predicted bins differing by at least2, record that coordinate i and actual bin j, and perform the restriction. Each update retains z and lowers rank, so there are at most d_* updates. At termination every coordinate's actual bin differs by at most1 from the predicted bin. Thus the prediction vector v(C) satisfies

    ||z−v(C)||_∞≤2/m.                                      (4)

The current class and its prediction depend only on the recorded word of pairs(i,j), not otherwise on z. There are at most

    Σ_{l=0}^{d_*}[N(m+1)]^l
       ≤[N(m+1)+1]^{d_*+1}                                 (5)

possible words. Predictions from nonempty classes associated to those words therefore cover S at radius2/m. The class may be infinite, nonclosed, nonmeasurable and specified by arbitrary constraints. Ranks and choices are existential; no efficient algorithm or definability is needed.

## 4. Exact original local theorem, with actual representatives

Fix p>1, R≥1 and η>0. Let B=ceil R and choose

    m=max{2,ceil(8(B+1)/η)}.

For any real Lp(μ), bounded centers a_1,…,a_N with ||a_i||≤R and any U⊂{||u||≤1}, take

    S={ (||u−a_i||/(B+1))_{i=1}^N : u∈U }.

If U is empty, select U_0 empty. Otherwise §2 bounds its splitting rank by d_*(p,B,m). Apply §3. For each external radius-2/m ball meeting S, choose one actual u_v∈U whose profile is in that ball. For any u assigned to that ball, the two profiles differ by at most4/m. Therefore

    max_i | ||u−a_i||−||u_v−a_i|| |
       ≤4(B+1)/m≤η.                                       (6)

There are only finitely many balls, so these choices require no measurable selector. With L=ceil(log_2(m+1)), (5) gives

    |U_0|≤[N(m+1)+1]^{d_*+1}
          ≤(2N+2)^A,    A=(L+1)(d_*+1).                    (7)

For the last inequality use N(m+1)+1≤(N+1)(m+1), N+1≤2N+2 and m+1≤(2N+2)^L. This is exactly the structural author's local theorem, including all p, all measures, all bounded centers, arbitrary constrained U and actual representatives in U. The exponent is a finite function only of p,R,η. No effective bound was requested, and none is supplied.

## Paid/unpaid assessment

The qualitative local input is paid by the older ω-stability theorem and the elementary finite-rank encoding above. Hrushovski's statement is consistent with the desired conclusion, but its general NIP route is unnecessary here and is not certified by this note. We do not claim that RandomVC2.11 alone contains the required polynomial L∞ packing bound, nor claim a counterexample to Hrushovski's general assertion.

The all-p Fourier/feature construction can remain an alternative author proof, but is not indispensable to the unchanged target. The sealed r36 global construction still applies verbatim to(6)–(7). Together with its credited Elkin–Neiman enrichment operations and pinned094 finite-set theorem, the full terminal conclusion is a qualitative application of existing inputs. This is an author-side TECHNICAL assessment, subject to the parent's disposition, not an independent gate or a claim that the exact terminal statement was previously published. No strengthened-rate side theorem is substituted for the full target. r36 remains immutable.
