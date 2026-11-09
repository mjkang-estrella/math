# Statement correspondence

Primary source, read from the cached arXiv:2002.07144v4 text, Section 2.3:
"Then s(π) = s(L)s(R)m." The largest entry is m. The unchanged round-1 `s_split`
and the new `sort_rootWord` formalize this convention. The source example is
s(416352)=143256, also checked in the frozen packet.

Definition 1.1 defines deg(f) as the average of |f^{-1}(f(x))| over x in X.
Frozen `P`, `deg`, `deg_eq_average` and `fibre_square_identity` formalize this
quantity, using all permutation words of [0,n), with cardinality n!.
The proved order-equivariance justifies the shift from [1,n].

Conjecture 4.4 (v3/v4; journal Conjecture 23) places the limit of the nth root
of this average in (1.68,1.73). Frozen `Conj` is its existential limit formulation.
Frozen `mathdb_345545`, `limit_ge` and `nonvacuity` remain conditional on Doubling
and Lower130. This lane does not discharge either proposition.

MathDB 345545's maximum-fibre paraphrase is the separate frozen `ConjMax`.
Frozen `mathdb_345545_max` and its companion are unconditional. This gives no
credit by itself; no new claim about that reading is made here.

The present target is exactly the frozen ExactSeeds20:
∀ n : Nat, 1 ≤ n → n ≤ 20 → P n = seed20[n]!.
The final theorem currently has the explicit hypothesis AdditiveRecursion.
The unconditional target `exactSeeds20_proved` is absent. Table values alone are
not presented as values of P beyond the previously proved small cases.

The tuple domain consists of ordered decompositions of arbitrary permutation
words into nonempty words; it is not a restricted set of special sorting fibres.
XI is its literal finite collision count. II additionally requires irreducibility.
The index bound min(M,21-M) is an evaluation pruning bound; the unpruned counts
and clipped functions are explicitly distinct definitions.
