# Ordinary proofs (r49) — two counterexample candidates

Zero credit claimed; root review/acceptance required. Lean endpoints: `lean/Yip355956.lean`, `lean/V3Config355701.lean`.

## 1. MathDB 355956 — Yip's maximal subfield clique conjecture is false

**Literal statement** (MathDB = arXiv:2209.00864 Conj. 1.1 = ALCO 6(4) 2023 Conj. 1.1 = Yip, arXiv:2101.09652, Conj. 1.4):
let d>1, let q ≡ 1 (mod 2d) be a power of a prime p, and let r be the largest integer with d | (q−1)/(p^r−1).
Then the subfield F_{p^r} is a maximal clique in GP(q,d) = Cay(F_q^+, (F_q^*)^d).

**Theorem.** For q = 5^8 = 390625, d = 3 (so p = 5) one has r = 1, and in every field K with 5^8 elements the
prime field F_5 is a clique of GP(5^8,3) but is not a maximal clique.

*Proof.* (i) 5^8 − 1 = 390624 = 6·65104, so q ≡ 1 (mod 6). For r ≥ 1 with (5^r−1) | 390624 we need 5^r − 1 ≤ 390624, so r ≤ 8;
checking r = 1,…,8: r = 1 gives 390624/4 = 97656 = 3·32552; r = 2 gives 16276 (not divisible by 3); r = 4 gives 626 (not
divisible by 3); r = 8 gives 1; r = 3,5,6,7 do not give integer quotients. Hence r = 1.

(ii) Let K be any field with 5^8 elements; then 5·1 = 0 in K (additive order divides |K| = 5^8, and K is a field).
Put f = X^8 + X^7 + 2X^6 + 2. Over any ring with 5 = 0 and f(t) = 0, define P_0 = t and P_{k+1} = P_k^5 reduced modulo f;
the eight explicit identities P_k(T)^5 − P_{k+1}(T) = Q_k(T) f(T) + 5 R_k(T) in Z[T] (certificates in
`lean/certificates.json`/the Lean file) give t^{5^8} = P_8 = t. Applied to t = root of f in K[X]/(f), this shows
f | X^{5^8} − X in K[X]. Since X^{|K|} − X = ∏_{a∈K}(X − a) splits over K and is nonzero, f splits over K, so there is
θ ∈ K with f(θ) = 0. (Irreducibility of f is not needed.)

(iii) Let x = 2θ + 4θ^2 + θ^3. For each a ∈ {0,1,2,3,4} the Lean file gives explicit polynomials y_a, h_a of degree ≤ 7
with integer identities y_a(T)^3 − (x(T) − a) ∈ (f, 5) and (x(T) − a) h_a(T) − 1 ∈ (f, 5); hence in K,
x − a = y_a(θ)^3 and x − a is invertible (so x ≠ a and y_a(θ) ≠ 0). Thus x − a and a − x = (−y_a)^3 are nonzero cubes.

(iv) In characteristic 5, z^5 − z = z(z−1)(z−2)(z−3)(z−4) + 5(…), so the subfield {z : z^5 = z} is {0,1,2,3,4}. Every nonzero
w with w^5 = w satisfies w^4 = 1 and w = (w^3)^3, so differences of distinct elements of F_5 are nonzero cubes: F_5 is a
clique. By (iii) F_5 ∪ {x} is a clique, and x ∉ F_5. Hence F_5 is not maximal. ∎

Remarks (diagnostics, not part of the Lean endpoint): the exhaustive exact search (`logs/yip-sweep-all.jsonl`) finds
960 extension vertices x for this (q,d); F_25 and F_625 are not cliques in GP(5^8,3) (a generator of F_25^* has discrete
log 16276 ≡ 1 mod 3, of F_625^* has log 626 ≡ 2 mod 3, relative to a primitive root), so F_5 is also a *maximal subfield
clique* that is not a maximal clique; this also contradicts the remark-conjecture in arXiv:2209.00864 / ALCO 2023 that
the hypothesis q > (n−1)^2 of its Theorem 1.2 can be dropped (here q = 5, n = 8). Theorem 1.2 itself is not contradicted
(5 ≤ 49). Across all 219 admissible open-range (p^r ≤ (n−1)^2) cases with q ≤ 5·10^6, this was the only failure.

## 2. MathDB 355701 — the "partial converse" for v_3 configurations is false

**Literal statement** (Bishop–Kuss–Peet, arXiv:2208.06912 = EJGTA 11(2) 2023, Conjecture 1; configurations purely
combinatorial, source §2.2): suppose a symmetric v_3 configuration contains a maximal set of mutually intersecting lines
of size i. If the minimum number of monochromatic triangles over line 2-colorings is non-zero, then i > 4.

**Theorem.** The 9_3 configuration on points 0..8 with lines
{0,2,3},{2,4,5},{3,5,8},{2,7,8},{1,3,6},{0,6,8},{0,1,4},{4,6,7},{1,5,7}
has no 5 pairwise-intersecting lines, has the inclusion-maximal (indeed maximum) intersecting set of lines 0–3 of size 4,
and every 2-coloring of its lines has a monochromatic triangle. Hence the conjecture fails under either reading of
"maximal" (inclusion-maximal or maximum).

*Proof.* Incidence checks (each line 3 points, each point on 3 lines, two points share ≤ 1 line, 9 points = 9 lines) are
finite. Exhaustion over all 512 subsets of lines shows every pairwise-intersecting set has ≤ 4 lines; lines {0,2,3},
{2,4,5},{3,5,8},{2,7,8} pairwise meet. The source triangle definition (points p1p2p3 with lines l1 ∋ p1,p2 ∌ p3, etc.)
yields 21 triangles (listed in the Lean file); exhaustion over all 512 line colorings shows each coloring makes one of
them monochromatic (the minimum is exactly 1 by `scripts/v3_verify.py`). ∎ The configuration has an automorphism group
of order 9 (diagnostic), unlike Pappus (order 108), which the source checked (Pappus: max 3 intersecting lines, min 0).
