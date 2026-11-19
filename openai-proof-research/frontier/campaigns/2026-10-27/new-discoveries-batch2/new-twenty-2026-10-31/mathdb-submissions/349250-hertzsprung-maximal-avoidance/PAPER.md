# The monotone pattern maximizes Hertzsprung avoidance

## Abstract

For consecutive-position, consecutive-value pattern occurrences in permutations, the increasing pattern has the largest avoidance count among patterns of its length. This proves Claesson's Conjecture 3.13, which extends Bóna's comparison for non-self-overlapping patterns. When the ambient permutation is longer than the pattern, the inequality is strict for every pattern other than the increasing and decreasing patterns. The proof compares marked occurrence counts using adjacent pairs for the increasing pattern and all pairs for the other patterns.

## Source statement

Let \(S_n\) consist of the permutations of \([n]=\{1,\ldots,n\}\). For \(\tau\in S_k\) and \(\pi\in S_n\), a Hertzsprung occurrence at start \(s\) is a factor \(\pi_{s+1}\cdots\pi_{s+k}\) with \(0\le s\), \(s+k\le n\), and \(\pi_{s+i}=\tau_i+c\) for all \(1\le i\le k\) and a single integer \(c\). Its values form an interval. Write \(S_n(\tau)\) for the permutations in \(S_n\) without any such factor and \(\mathrm{id}_k\) for the increasing pattern.

Claesson's Conjecture 3.13 states \(|S_n(\tau)|\le |S_n(\mathrm{id}_k)|\) for all Hertzsprung patterns \(\tau\in S_k\) and all natural numbers \(n\). There is no restriction on self-overlap or on the relative lengths. We allow the empty pattern at every boundary when \(k=0\). Lean uses zero-based indices for both position sets and both value sets. Subtracting one from both values preserves the same translation equation. [Claesson, Conjecture 3.13](https://arxiv.org/abs/2012.15309)

## What was known

Bóna proved the comparison for non-condensible patterns, which admit no proper overlap of two copies. The statement line in his preprint is broad, but its proof relies on a lemma requiring non-condensibility, and Claesson credits the comparison for non-self-overlapping patterns. For example, as Bóna observes, \(2143\) is condensible: it has two intersecting copies in \(214365\). The present proof retains Bóna's common first moment and uses the intersecting-block count to cover patterns of this kind. [Bóna, §2](https://arxiv.org/abs/0704.1489)

## Theorem

For every \(k,n\) and every \(\tau\in S_k\), \(|S_n(\tau)|\le |S_n(\mathrm{id}_k)|\). For \(n\ge k+1\), the inequality is strict whenever \(\tau\) is neither increasing nor decreasing.

## Proof

For \(k=0\) every permutation has an occurrence at the initial boundary, including the empty permutation. For \(k=1\) every nonempty permutation has an occurrence. If \(k>n\) there are no starts, so all permutations avoid, including the empty ambient permutation for \(k=1\). If \(k=n>0\) the start must be at the beginning. The full value interval forces shift zero, so \(\tau\) itself is the only permutation containing the pattern, and every \(\tau\in S_n\) has \(n!-1\) avoiders. In each of these boundary cases the avoidance count does not depend on \(\tau\), so the inequality holds with equality.

Complementing the ambient values by \(x\mapsto n+1-x\) is an involution. A decreasing occurrence has entries \(k+1-i+c\) at indices \(1\le i\le k\). The complementary values are \(i+n-k-c\), giving increasing occurrences at the same starts, and the same involution reverses the correspondence. Thus the increasing and decreasing avoidance counts agree. These cases account for \(k\le 2\), since there is one ordering on at most one element and two on two elements. Assume henceforth that \(k\ge3\), \(n\ge k+1\) and \(\tau\) is neither increasing nor decreasing.

Any consistent injective assignment on \(m\) specified positions has \((n-m)!\) completions. A completion restricts to a bijection between the remaining positions and values, and each such bijection gives one completion. Both complements have \(n-m\) elements. Ordering them identifies these bijections with permutations, which have \((n-m)!\) choices by successively choosing the images.

For a permutation \(\pi\), write \(t_\tau(\pi)\) for its number of starting positions of \(\tau\). For \(1\le k\le n\), the total \(T=\sum_{\pi\in S_n}t_\tau(\pi)\) equals \((n-k+1)^2(n-k)!\), and in particular is independent of \(\tau\). There are \(n-k+1\) choices of start and \(n-k+1\) choices of the minimum value in the block. Once those are fixed, the \(k\) prescribed entries are distinct, giving \((n-k)!\) completions. The minimum determines the translation, and for a positive-length pattern the start and the permutation determine this minimum, so each marked occurrence is counted once.

For the identity pattern, the set of starting positions in any \(\pi\) is a union of maximal runs of consecutive starting positions. Let \(a(\pi)\) count pairs of adjacent starts. Each nonempty run contributes one fewer adjacent pair than it has starts. Consequently \(t_{\mathrm{id}}(\pi)-a(\pi)\) counts the runs, and is at least one if \(\pi\) contains the identity. Equivalently, the least start together with the second start of each adjacent pair gives distinct starts. A pair of adjacent identity occurrences is exactly an increasing block of \(k+1\) consecutive values. The blocks share \(k-1\) entries, and comparing a common entry forces the second translation to be one larger. The first block supplies the first \(k\) entries and the second supplies the last. Conversely the length-\(k\) prefix and suffix give the two occurrences. Applying the first-moment count to \(\mathrm{id}_{k+1}\), which has length \(k+1\le n\), the total number of adjacent pairs is
\[
 O_1=(n-k)^2(n-k-1)!>0 .
\]
Writing \(C_\sigma=|\{\pi\in S_n:t_\sigma(\pi)>0\}|\), we get \(C_{\mathrm{id}}\le T-O_1\).

For any \(\pi\) with at least one occurrence, pair its least start with each of its other starts. These are all distinct pairs, so \(t_\tau(\pi)\) is at most one plus the number of its pairs. For \(\pi\) with no occurrences both counts are zero. Let \(P_\tau\) count all unordered pairs of distinct \(\tau\)-occurrences over all \(\pi\). Summing gives \(C_\tau\ge T-P_\tau\). We bound \(P_\tau\) by counting overlaps and disjoint pairs separately.

Take two starts \(i,i+d\) with \(1\le d<k\). In their common positions, equality of entries forces the translation offsets of the second copy minus the first to be \(\tau_{d+1}-\tau_1\), and all their values in the common positions are distinct. The two value intervals intersect in exactly \(k-d\) values, since every common value must arise in a common position by injectivity of \(\pi\). Thus their minima differ by \(d\) in absolute value and their union is an interval of \(k+d\) values. If \(d=1\), then every consecutive difference of entries of \(\tau\) must be the same, by comparing all common positions, and that difference is \(1\) or \(-1\). A sequence of \(k\) values in \([k]\) with step \(1\) starts at \(1\), and one with step \(-1\) starts at \(k\). These are exactly the two excluded patterns.

For \(2\le d<k\) with \(k+d\le n\), each minimum of the union interval determines at most one pair of value blocks, because the *signed* offset difference \(\tau_{d+1}-\tau_1\) is fixed. The first start and the union interval minimum each have \(n-k-d+1\) possibilities. For each such choice there is at most one assignment on the \(k+d\) covered positions, leaving at most \((n-k-d)!\) completions. The total at distance \(d\) is therefore at most
\[
 O_d=(n-k-d+1)^2(n-k-d)! .
\]
For the feasible successive values \(d,d+1\), with \(M=n-k-d\ge1\), \(O_{d+1}/O_d=M/(M+1)^2\le1/4\) by \((M-1)^2\ge0\). The sum of the overlapping contributions for \(d\ge2\) is at most \(O_1/3\), since the finite geometric sum with first term \(1/4\) and ratio \(1/4\) is at most \(1/3\). Indeed, when the last feasible distance is \(D\ge2\), summing \(3O_d\le O_{d-1}-O_d\) from \(2\) to \(D\) gives \(3\sum_{d=2}^D O_d\le O_1-O_D\le O_1\). If \(D<2\), the sum is zero.

If \(n<2k\) there are no disjoint pairs. Otherwise, put \(L=n-2k\). In this paragraph index each occurrence by the position \(s+1\) of its first entry. Two such positions \(i<j\) with disjoint blocks satisfy \(1\le i,\ i+k\le j\le n-k+1\). The map \((i,j)\mapsto(i,j-k+1)\) bijects these choices with ordered-increasing pairs from \([L+2]\). Adding \(k-1\) to the second coordinate is the inverse, since a strict increase in the compressed coordinates gives a gap of at least \(k\). There are \(\binom{L+2}{2}=(L+2)(L+1)/2\) increasing pairs, because swapping coordinates pairs the increasing and decreasing halves of the ordered pairs of distinct indices. The same count holds for pairs of disjoint value intervals ordered by their minima, since disjoint positions must have disjoint values. There are two choices of assignment of the intervals to the two starts. Each assignment prescribes the block entries and leaves \(L!\) completions. The total disjoint contribution is exactly
\[
 D_{\mathrm{disj}}=2\binom{L+2}{2}^{\!2}L!
                  =\tfrac12(L+2)^2(L+1)^2 L! .
\]
Here \(O_1=(L+k)^2(L+k-1)!\). Since \(k\ge3\), the factors of \((L+k-1)!/L!\) include \(L+1,L+2\), and \((L+k)^2\ge(L+1)(L+2)\). Thus \(D_{\mathrm{disj}}\le O_1/2\).

Combining both types, \(P_\tau\le (1/3+1/2)O_1=5O_1/6<O_1\). Therefore \(C_\tau\ge T-P_\tau>T-O_1\ge C_{\mathrm{id}}\). Complementing the counts within \(S_n\) gives the strict avoidance inequality and proves the full theorem.

## Lean correspondence

The occurrence, avoidance count and source proposition are defined by HOcc, avoidCount and ClaessonConjecture313 in namespace Hertzsprung. The following declarations track the proof.

| Step | Lean declarations |
| --- | --- |
| Translation and interval image | hOcc_iff_at, at_unique, at_mem_iff |
| Completions and first moment | card_completions, card_at, first_moment |
| Least-start inequalities and their sums | lower_local, upper_local, lower_global, upper_global |
| Adjacent identity pairs | at_adj_id_iff, adjacent_equiv |
| Overlap rigidity and count | card_union_at, union_overlap, overlap_data, adj_monotone, overlap_bound |
| Disjoint descriptors and completions | offsets_disjoint, card_both, ordered_card, separated_bound |
| Numerical comparison | weight_step, overlap_sum, separated_weight, overlap_total, separated_total, pairs_total |
| Value complement and boundary counts | rev_hOcc, rev_avoid, short_pattern, avoid_empty, avoid_singleton, avoid_too_short, avoid_same_length |
| Convert to avoiders and finish | avoid_add_contains, strict_avoidance, claesson_conj_3_13, claesson_source |

For the disjoint count, Lean proves the required upper bound by injecting into the descriptors of the proof, with at most \(L!\) completions per descriptor.

The endpoint checks and axiom audit from the clean compilation follow.

```text
Hertzsprung.claesson_conj_3_13 (k n : ℕ) (τ : Equiv.Perm (Fin k)) :
  avoidCount n k τ ≤ avoidCount n k (Equiv.refl (Fin k))
Hertzsprung.claesson_source : ClaessonConjecture313
Hertzsprung.strict_avoidance {k n : ℕ} (hn : k < n) (τ : Perm k) (hinc : τ ≠ Equiv.refl (Fin k))
  (hdec : τ ≠ Fin.revPerm) : avoidCount n k τ < avoidCount n k (Equiv.refl (Fin k))
Hertzsprung.avoid_empty (n : ℕ) (τ : Perm 0) : avoidCount n 0 τ = 0
Hertzsprung.avoid_singleton {n : ℕ} (hn : 0 < n) (τ : Perm 1) : avoidCount n 1 τ = 0
Hertzsprung.avoid_too_short {n k : ℕ} (h : n < k) (τ : Perm k) : avoidCount n k τ = Fintype.card (Perm n)
Hertzsprung.avoid_same_length {n : ℕ} (hn : 0 < n) (τ : Perm n) : avoidCount n n τ + 1 = Fintype.card (Perm n)
Hertzsprung.rev_avoid (n k : ℕ) : avoidCount n k Fin.revPerm = avoidCount n k (Equiv.refl (Fin k))
'Hertzsprung.claesson_conj_3_13' depends on axioms: [propext, Classical.choice, Quot.sound]
'Hertzsprung.claesson_source' depends on axioms: [propext, Classical.choice, Quot.sound]
'Hertzsprung.strict_avoidance' depends on axioms: [propext, Classical.choice, Quot.sound]
'Hertzsprung.avoid_empty' depends on axioms: [propext, Classical.choice, Quot.sound]
'Hertzsprung.avoid_singleton' depends on axioms: [propext, Classical.choice, Quot.sound]
'Hertzsprung.avoid_too_short' depends on axioms: [propext, Classical.choice, Quot.sound]
'Hertzsprung.avoid_same_length' depends on axioms: [propext, Classical.choice, Quot.sound]
'Hertzsprung.rev_avoid' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Scope of the literature review

The supplied independent AI review checked Claesson's arXiv v2, Bóna's preprint and the relevant section of Bóna's survey, with a bounded search for later work on maximal avoidance, condensible patterns and self-overlap. It reported no general resolution. It read abstracts or snippets of the work on self-overlap and on involutions and the work associated with Claesson's Conjecture 3.14. It did not read Bóna's paywalled journal version. This manuscript uses the supplied audit. The manuscript, formalization and independent review were AI-produced. No human peer review has taken place.

## References

- Anders Claesson, *From Hertzsprung's problem to pattern-rewriting systems*, Conjecture 3.13. [arXiv:2012.15309](https://arxiv.org/abs/2012.15309) · [Algebraic Combinatorics](https://doi.org/10.5802/alco.202)
- Miklós Bóna, *Where the monotone pattern (mostly) rules*, §2. [arXiv:0704.1489](https://arxiv.org/abs/0704.1489)
- Miklós Bóna, *On three different notions of monotone subsequences*, §4.2. [Survey](https://people.clas.ufl.edu/bona/files/monsurvey.pdf)
- Sergey Kirgizov and Khaydar Nurligareev, *Asymptotics of self-overlapping permutations*. [arXiv:2311.11677](https://arxiv.org/abs/2311.11677)
- Marilena Barnabei, Niccolò Castronuovo and Matteo Silimbani, *Hertzsprung patterns on involutions*. [DMTCS](https://dmtcs.episciences.org/16492)
