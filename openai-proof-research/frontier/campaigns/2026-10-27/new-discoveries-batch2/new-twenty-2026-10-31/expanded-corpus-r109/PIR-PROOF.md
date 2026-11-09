# MathDB 338214: sufficiency of the generalized Hamming weight condition

Status: complete ordinary proof of the literal conjecture. It is a short bridge from two classical facts:
Wei's support/rank duality, and Edmonds' matroid base covering (equivalently, the base polytope) theorem.
We therefore classify it as a **routine classical consequence**, with zero credit expected. No Lean
endpoint was attempted: mathlib has no matroid covering or base-polytope theorem, and the route is
likely to be excluded under the campaign's routine-bridge rule (compare 334207, 369221 and 371637).

## Source definitions (arXiv 1801.04923v2, Definitions 1, 3, 6 and 9; Theorem 2; Conjecture 1)

* C is an [n,k] linear code over GF(q), with generator matrix G. An information set is a k-set of
  coordinates on which G is invertible.
* d_s is the smallest support size of an s-dimensional subcode.
* A PIR achievable rate matrix Λ_{κ,ν} is a ν × n binary matrix in which every column has weight κ and
  the support of every row contains an information set. It is MDS-PIR capacity-achieving if κ/ν = k/n.
* Theorem 2 (source): if such a matrix exists, then d_s ≥ (n/k) s for all s in {1,…,k}. This is (5).
* Conjecture 1: the matrix exists **iff** (5) holds.

## Proof of sufficiency

Let M be the column matroid of G on E = {1,…,n}, with rank function r and r(E) = k.

1. **(5) ⇒ r(Z) ≥ (k/n)|Z| for every Z ⊆ E.** If r(Z) = k, this holds because |Z| ≤ n. Otherwise
   s := k − r(Z) ≥ 1. The subcode D = {c ∈ C : c_j = 0 for all j ∈ Z} is the image of the kernel of
   G|_Z, so dim D = k − r(Z) = s and χ(D) ⊆ E \ Z. Hence d_s ≤ n − |Z|. Combined with (5), this gives
   n − |Z| ≥ n s / k = n (k − r(Z)) / k, that is, |Z| ≤ (n/k) r(Z).
2. **Uniform covering.** Write k/n = κ0/ν0 in lowest terms. Let M' be the matroid on E × {1,…,κ0} in
   which the κ0 copies of each element are parallel. For X ⊆ E × [κ0], let π(X) be its projection to E.
   Then r'(X) = r(π(X)) and |X| ≤ κ0 |π(X)| ≤ κ0 (n/k) r(π(X)) = ν0 r'(X). By Edmonds' matroid covering
   theorem (Edmonds 1965; Nash-Williams 1966), E × [κ0] is a union of ν0 independent sets of M'.
   Their total size is at least κ0 n = ν0 k, and each has size at most k. So they are ν0 pairwise
   disjoint bases of M'. Distinct copies of one element are parallel, so each such basis projects to
   k distinct coordinates, which form an information set of C.
3. Let Λ be the ν0 × n binary matrix whose rows are the indicator vectors of these ν0 information sets.
   Every coordinate occurs exactly κ0 times, because the bases partition E × [κ0]. Every row support is
   an information set, and κ0/ν0 = k/n. So Λ = Λ_{κ0,ν0}(C) is MDS-PIR capacity-achieving.

Together with the source's Theorem 2 (necessity), this proves Conjecture 1 for all linear codes over
all finite fields. The argument also works for any representable matroid.

## Checks and limits

* `scripts/pir_check.py` → `outputs/pir-check.json`: 275 random [n,k] codes over GF(2) and GF(3) with
  n ≤ 8. Condition (5) was computed by brute force over coordinate sets, and uniform base-cover
  feasibility by HiGHS LP. In all 275 cases the two agree: 65 satisfy (5), 210 violate it. This is a
  floating-point diagnostic only.
* Prior art (bounded): arXiv 1712.03898v4 (11 Feb 2019) and 1801.04923v2 (31 May 2018) still state
  the conjecture as open. One web search (2026-11-02) found no published resolution and no paper
  linking it to matroid base polytopes. The IEEE journal versions were not read (paywalled), so a
  published remark there cannot be excluded.
* Significance: the proof needs only the classical covering theorem. Root review should treat it as a
  routine-bridge exclusion unless it judges otherwise.
