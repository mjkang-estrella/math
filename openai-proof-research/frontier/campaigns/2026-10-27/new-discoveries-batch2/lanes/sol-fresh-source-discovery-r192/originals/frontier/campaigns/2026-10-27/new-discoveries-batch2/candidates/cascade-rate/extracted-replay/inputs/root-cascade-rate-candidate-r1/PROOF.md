# A fixed cascade series without a geometric rate

Ordinary proof candidate, 29 October 2026 UTC. No acceptance or literature-priority authority is claimed.

## Exact source and conclusion

Cénac–Chauvin–Noûs–Paccaut–Pouyanne, *Variable Length Memory Chains: Characterization of stationary probability measures*, Bernoulli 27(3) (2021), 2011–2039, DOI https://doi.org/10.3150/20-BEJ1299, Conjecture 4.2, printed p.2037, asserts geometric convergence of every cascade series for every non-null probabilised context tree having no infinite shift-stable subtree. The same assertion is Conjecture 5.2 in arXiv:2004.07893v1, p.39. Both actual bodies were read. The author-hosted typeset published PDF is https://pouyanne.perso.math.cnrs.fr/ccnppBernoulli.pdf . Definitions 2.5–2.12, equation (5), Proposition 3.1 and Definition 3.2 fix the conventions.

We construct ONE tree and ONE uniformly positive assignment q, satisfying every source hypothesis, for which the literal series indexed by alpha-LIS 1 is summable but has NO geometric rate in length. In fact limsup κ_1(n)^(1/n)=1. This refutes the full source conjunction by its rate clause; bare convergence under the source hypothesis is not refuted or resolved in general. The source leaves “geometrical rates” unformalized; the construction fails both the standard term bound κ_1(n)≤Cr^n and the stronger tail bound Σ_{m≥n}κ_1(m)≤Cr^n, for every C<∞ and 0<r<1. Ordering the countable family arbitrarily is not the length convention used in source equation (5).

## 1. Explicit saturated tree

Use alphabet {0,1}. Let b=(01)^∞. Write p_m for its length-m prefix (p_0 is empty). Define integers

    n_0=0,     n_k=k²(n_{k-1}+k+10),   k≥1,
    a_k=(01)^k00,                     k≥1.

Thus n_1=11,n_2=92,n_3=945,n_4=15344. The n_k strictly increase, n_k>|a_k|=2k+2, and n_{k-1}/n_k≤1/k². The anchors a_k are prefix-incomparable: if j<k, at position 2j+2 the word a_j has 0 whereas a_k has 1. Each a_k is the off-spine child of p_{2k+1}=(01)^k0.

Specify the internal nodes, and then saturate:

    I={p_m:m≥0} ∪ ⋃_{k≥1}{a_k v:v a binary finite word, |a_k v|<n_k},
    T=I ∪ {w0,w1:w∈I}.

I is prefix-closed: prefixes of an anchored word either remain in that bush or are spine prefixes. Every node of I has exactly two children in T; every node of T\I has none. Indeed if a child of a node outside I were in T, that node would be a prefix of an internal word, contradicting prefix closure. Consequently this is a saturated rooted context tree. The finite leaves at the bottom of bush k are exactly all a_k v with |a_k v|=n_k. Other off-spine children not selected for bushes are ordinary leaves.

The only infinite branch is b. Any branch different from b first deviates at some finite position; either it immediately reaches an ordinary leaf or enters one fixed finite bush, where it stops at depth n_k. Thus there is precisely one infinite context, and countably many contexts in all, as the source requires.

There is no infinite shift-stable subtree S contained in T. An infinite finitely branching rooted tree has an infinite branch: starting at the root choose successively a child with infinitely many descendants. Its branch would have to be b. If S is shift-stable on finite nodes, then for every m, p_{m+1}∈S implies σ(p_{m+1})∈S. Hence every prefix of σ(b)=(10)^∞ belongs to S, so σ(b) would also be an infinite branch of T, contradiction. This argument also covers a subtree not separately assumed saturated. At the simplest level, 1 is already a leaf of T, so T cannot contain the shifted branch.

Put q_c(0)=q_c(1)=1/2 for every finite AND infinite context c. Non-nullness holds uniformly; the associated VLMC is an ordinary fair iid letter process. No issue about existence of a stochastic process or continuity of q arises.

## 2. A large leaf family with the SAME alpha-LIS

Fix k≥3. Set

    H=n_{k-1}+3,   R=n_k-(2k+2)-H,
    B=floor(R/k),  r=R-kB,  0≤r<k.

R≥0 follows directly from the recurrence. For every independent choice of B binary words u_i of length k−2, form

    w=a_k (11u_1)(11u_2)···(11u_B) 1^(r+H).

Each w has length n_k and is a bottom leaf of bush k. Distinct choices give distinct leaves, so there are exactly 2^((k−2)B) such w.

We prove EVERY nonempty proper suffix of w is non-internal. This is the essential fixed-alpha-LIS bridge, not a count over varying series.

First, the terminal run has at least H≥3 ones. A nonempty spine prefix beginning with 0 cannot end with this run; an internal suffix of length 1 or 2 also cannot occur, because these suffixes are 1 and 11 and all spine prefixes start with 0. Thus no nonempty suffix is a spine internal word.

Second, consider a suffix starting at an anchor a_j and internal in bush j. If j<k, its length would be <n_j≤n_{k-1}. The last H letters of w are all 1. Every suffix of length at most n_{k-1} therefore starts with 1, whereas every anchor starts with 0. This is impossible.

If j≥k, no such anchor can start in the tail after a_k. Any anchor a_j begins with an alternating substring (01)^k of length 2k. The tail is a concatenation of length-k blocks beginning 11, followed by at least three ones. It contains no alternating substring of length 2k: consecutive forced equal pairs 11 have starting positions separated by exactly k; after the last such pair only a block of length at most k followed by ones remains; before the first pair nothing precedes the tail. More explicitly, an interval of 2k letters starting anywhere in the tail either includes a whole forced 11 pair or lies partly/in the final run and includes a terminal equal pair. Thus no required alternating prefix occurs there.

There is also no proper occurrence of a_j, j≥k, starting within the initial a_k. A start at a letter 1 is impossible. An even shift 2h with 1≤h≤k leaves an initial alternating run of only 2(k−h) letters before the two zeros at the end of a_k; this is too short for (01)^k. A start at either terminal zero of a_k is followed by 0 or by the initial 11 of the tail, so its alternating run is of length at most 2. The tail is nonempty because H≥3. The sole occurrence permitted at position zero is the original a_k, corresponding to w itself, not a proper suffix.

These cases exhaust I. Every nonempty proper suffix of w is non-internal, and the empty suffix IS internal. The longest internal strict suffix is therefore empty, and its preceding letter is the final 1. Hence the source alpha-LIS is exactly 1 for every member of this family. The word 1 itself is a finite context, so 1 belongs to the source set S of context alpha-LIS as well.

## 3. Literal cascade weights and absence of exponential decay

Definition 2.10 multiplies one q factor for each letter preceding the alpha-LIS. All proper suffixes involved are non-internal and therefore have a well-defined context prefix; their q factors equal 1/2. Consequently

    casc(w)=2^(-(n_k−1)).

For alpha-LIS 1, source equation (5) indexes length exactly n, because |1|=1. Thus the constructed family gives the exact lower bound

    κ_1(n_k) ≥ 2^((k−2)B−n_k+1) = 2^(-D_k),
    D_k=n_k−1−(k−2)B.

Since B≥(n_k−(2k+2)−H)/k−1,

    D_k/n_k ≤ 2/k + ((2k+2)+H+k)/n_k
             = 2/k + n_{k-1}/n_k + (3k+5)/n_k
             ≤ 2/k + 1/k² + (3k+5)/n_k  → 0.

Here n_k≥k²(k+10), so the last term tends to zero; n_k also tends to infinity. D_k is nonnegative because (k−2)B≤n_k−1. It follows that limsup κ_1(n)^(1/n)≥1. Conversely κ_1(n)≤1, since there are at most 2^(n−1) binary words of length n ending in 1, and every such context with alpha-LIS 1 has cascade 2^(-(n−1)). Thus the limsup equals 1.

If κ_1(n)≤Cr^n eventually for some C>0 and 0<r<1, its nth-root limsup would be at most r, contradiction. An exponential bound on the nonnegative series tails implies the same term bound and is also impossible. This proves the claimed source refutation at all orders by exact counting, not by finite diagnostics.

## 4. Summability, scope and novelty limits

For any prefix-free family of binary leaves, Σ_c 2^(-|c|)≤1: for a finite subfamily the corresponding fair iid cylinder events are disjoint; pass to increasing finite subfamilies. The leaves with alpha-LIS 1 form such a family and have cascade 2·2^(-|c|). Hence Σ_n κ_1(n)≤2. The refutation isolates a real failure of the rate assertion despite convergence. This is neither a boundary/domain change nor a fixed-parameter partial verification: a single fully specified admissible tree negates the universal geometric conclusion. No claim is made that the weaker convergence-only conjecture fails.

The construction uses classical prefix codes and elementary counting. Those tools and the fair iid process are not novel. The substantive proposed content is their simultaneous realization with exactly one unpaired alternating branch, no infinite shift-stable subtree, and one fixed literal alpha-LIS series with root limsup 1. A closest prior theorem or counterexample yielding that bridge would defeat discovery credit. None was located in the bounded primary/registry screen; no worldwide priority assertion is made. Independent adversarial mathematical/source/eligibility review remains REQUIRED. No Lean endpoint, publication, accepted result or count increase is asserted here.
