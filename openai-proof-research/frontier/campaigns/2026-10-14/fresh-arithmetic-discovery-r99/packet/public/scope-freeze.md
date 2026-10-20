# r99 frozen scope (family 164, positive characteristic)

Frozen before proof development. Notation: [r] = {1,...,r}; for a field K,
K^x = K \ {0}; for x_1,...,x_n in K and nonempty J ⊆ [n],
FS_J = sum_{i in J} x_i and FP_J = prod_{i in J} x_i.

## Theorem F

Let K be an infinite field (of any characteristic; the case of positive
characteristic is the case not covered by the sources read). Let r >= 1 and
n >= 1 be integers and let chi: K^x -> [r] be any map. Then there exist
pairwise distinct x_1,...,x_n in K^x such that

1. FS_J != 0 for every nonempty J ⊆ [n], and
2. chi is constant on {FS_J : ∅ != J ⊆ [n]} ∪ {FP_J : ∅ != J ⊆ [n]}.

## Corollary G

For every prime p and all integers r, n >= 1 there is an integer d >= 1 such
that for every positive integer m divisible by d and every map
chi: F_{p^m}^x -> [r] there exist pairwise distinct x_1,...,x_n in F_{p^m}^x
satisfying conclusions 1 and 2 of Theorem F (with K = F_{p^m}).

## Not claimed

- No bound on d or on the size of the configuration.
- No claim for all sufficiently large m in Corollary G.
- No infinite (IP-set) version; no density version; no read-once or
  sums-of-disjoint-products extension; no growth/separation conditions.
- Characteristic 0 is known (Alweiss over Q, restriction to the prime field,
  Hunter's distinctness remark) and is included only because the proof is
  uniform.

Allowed inputs: Bergelson–Leibman (Annals 150, 1999) Corollary 7.11; finite
Ramsey theorem; Folkman's finite sums theorem; Tychonoff compactness for
countable products of finite sets. Alweiss's Proposition 4.1 mechanism is
re-derived, not cited as a black box.
