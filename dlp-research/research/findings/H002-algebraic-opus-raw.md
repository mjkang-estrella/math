# Unaccepted H002 delegated report: algebraic-opus

Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h002-algebraic-opus-20261008-r1`.
Provider/model: `claudeAgent/claude-opus-5-5`; status completed.

This report is retained for process evidence, not automatically adopted. Primary
formula checks, cost assumptions and universal claims require coordinator
qualification. In particular the EDS index1 identity is under active correction;
no experiment should rely on it before resolution. See the coordinator disposition.

I came up with four mechanisms in my lens (coordinate/algebraic relation extraction and structured polynomial algorithms). None of them is a credible exponent improvement. I ran a paper-level falsifier on each while drafting. All four lose on the specific setup I worked out, though each leaves a narrower open question that a cheap test could settle. I read only STATE.md and the primary sources below, not the H001/H002 proposal reports. Repo edits: none. Experiments: none. Children: none.

---

### Card 1: Using a lattice to find decompositions into small x-coordinates

**Mechanism.** Use a factor base of points whose x-coordinate is a small integer, x < X. To decompose a target R into m factor-base points, take functions f in L((m+1)O) that vanish at −R. The norm N_f = A² − B²(x³+ax+b) is a polynomial whose roots are the x-coordinates of the other zeros of f. Its coefficients are quadratic in the parameters of f.

"All roots small" implies that the coefficients of N_f/(x−x_R), reduced mod p, equal small integers: e₁ ≤ mX, e₂ ≤ C·X², …, e_m ≤ X^m. That turns relation search into finding small points on a quadratic image mod p, which lattice or Coppersmith methods might do, instead of solving a Semaev system.

For m=2 I derived the exact reduction. Let s = x₁+x₂ and t = x₁x₂. Then the line slope is affine in (s,t):

- λ = (t − a − 2x_R² − x_R·s)/(2y_R)

The decomposition condition becomes a single conic congruence:

- λ(s,t)² ≡ s + x_R (mod p), with 0 ≤ s < 2X and 0 ≤ t < X²
- plus the integer filter that s² − 4t is a perfect square.

**Where a gain would come from.** Polynomial-time lattice enumeration of the box points, so that relation search stops depending on 2^{m−1}-degree Semaev polynomials.

**Costs and scope.** Lattice dimension is polynomial in m. Memory is that of the factor base, O(X), plus sparse linear algebra costing X².

**Prior art.** Semaev's small-x factor base, with the open problem of solving S_{m+1}. Diem notes that an algorithm for small-coordinate solutions would be needed, and the PKM slides say "no algorithm to solve S_{m+1}". I found nothing that formulates this via the norm coefficients plus a box condition. Novelty: unknown, plausibly unpublished because it fails.

**Falsifier, run on paper (rejects this setup).** Even with a perfect oracle that enumerates box points at polynomial cost each:

- The box has volume X^{m(m+1)/2}, but only about X^m of those points actually split into small roots.
- Balancing that against the number of targets gives a minimum total cost of p^{(m(m−1)/2+1)/(m(m+1)/2)}.
- That is p^{2/3} for m = 2 and 3, and p^{0.7} for m = 4. It is never below p^{1/2}.

**Strongest unsupported assumption.** That a lattice can capture *complete splitting* (multiplicative structure in Z[x]), not just the coefficient box. To beat rho, the loss factor X^{m(m−1)/2} has to be avoided.

**Cheapest decisive test of what's left.** For m=3 at p ≈ 2³⁰, write down any lattice/Coppersmith formulation that encodes splitting. Measure how many candidates it examines per true relation. If that number is ≥ X^{m(m−1)/2}/polylog, reject.

---

### Card 2: A dedicated solver for the PKM isogeny-tower systems via correspondence push-forward

**Mechanism.** PKM16 already define a factor-base set V as the fibre of an x-map composed from a chain of small-degree maps. The chain comes either from a smooth-order subgroup of F_p^* or from isogeny kernels on an auxiliary curve E′ whose group order has a smooth factor S. Their stated open problem is a dedicated solver for the resulting block-triangular system.

My proposed exploitation is level-by-level pruning. Push the Semaev correspondence S₃(·,·,x_R) ⊂ P¹×P¹ forward through each tower level (L_j × L_j). Then prune the 2-ary tree of fibre choices at level j whenever the partial pair is not on the pushed-forward curve. This is analogous to Hensel lifting, or to bit-by-bit Weil descent in the binary case.

**Where a gain would come from.** If the pushed-forward correspondences keep bounded bidegree, the cost is poly(n) per level instead of |V| enumeration. That would give subexponential relation search.

**Costs and scope.** Precomputing the tower costs about |F| random-curve trials (PKM's estimate). Memory is O(|V|) plus linear algebra. Applies to any prime p, because the auxiliary curve E′ can be chosen freely.

**Prior art.** [PKM16](https://christophe.petit.web.ulb.be/files/16PKC_primeECDLP.pdf) ([slides](https://troll.iis.sinica.edu.tw/pkc16/slides/6-1--Algebraic_approaches_for_the_Elliptic_Curve_Discrete_Logarithm_Problem_over_Prime_Fields.pdf)) cover both the p−1 and isogeny-kernel towers. They report experimental degrees of regularity below semi-generic and say the asymptotics are open. [Euler–Petit 2021](https://doaj.org/article/75a4ced306114d568b832c4b20d00fd7) and [Huang et al. 2020](https://arxiv.org/pdf/1909.11326) limit quasi-subfield variants. The [ePrint 2024/1923 survey](https://eprint.iacr.org/2024/1923) finds no subexponential method. The pruning-by-push-forward framing is my distinction.

**Structural obstacle found while drafting.** Exact pruning requires the tower maps to respect E's addition law. That means they must be x-maps of isogenies *from E* with F_p-rational kernels. On a curve of prime order q that is impossible, so their fibres contain at most 2 rational points. Therefore any tower with large fibres is incompatible with E's group law, and the Semaev condition does not descend to intermediate levels exactly. Only approximate or non-homomorphic pruning is left.

**Strongest unsupported assumption.** That push-forward bidegrees stay bounded. The generic expectation is doubling per level, reaching (2^{n+1}, 2^{n+1}).

**Cheapest decisive falsifier.** For m=2 at p ≈ 2²⁴, with random E and E′ and tower depth n = 1..8, compute the bidegree of the image of S₃ under each (L_j × L_j). If it grows geometrically, reject pruning. As a second test, measure the msolve solving degree against n. If it grows linearly in n (cost ≥ |V|^c), reject this setup. The asymptotic question stays open.

---

### Card 3: Reading the dlog's parity off the EDS residue bit

**Mechanism.** [Lauter–Stange](https://arxiv.org/abs/0803.0728) show the following, for P with χ(φ(P)) = −1:

- From Q alone you can compute the residue window χ(W(k+n)/W(k)).
- An oracle for the single bit χ(W(k)) gives the parity of k.
- Repeated halving then recovers k in O(log q) oracle calls.

Here W is the elliptic divisibility sequence of P, χ the quadratic character and φ their normalising map. I asked whether that bit, or the parity of the dlog directly, equals χ(G(Q)) for some explicit low-degree rational function G on E.

**Where a gain would come from.** It would give a polynomial-time ECDLP algorithm.

**Falsifier, run on paper.** Suppose χ(G([k]P)) = (−1)^k except at B points.

- Let H(Q) = G(Q)·G(Q+P). Then χ(H) = −1 almost everywhere.
- If H is not a constant times a square, the Weil bound requires deg G ≳ (q − 2B)/(4√p), i.e. about √q/4.
- If H is a constant times a square, then G's odd-multiplicity divisor support is invariant under translation by P. That forces it to contain whole ⟨P⟩-cosets, so deg G ≥ q/2, or else χ(G) is constant.

So no rational function of degree o(√q) agrees with dlog parity on noticeably more than half of the points. [Shparlinski–Stange 2012](https://www.cambridge.org/core/journals/canadian-mathematical-bulletin/article/character-sums-with-division-polynomials/6D1DC44634CB19BEF784CE153323C084) already exclude statistical bias. The Lange–Winterhof interpolation lower bounds are probably the closest prior art (not re-fetched).

**What's left.** Only a compact straight-line program of degree about √q or higher remains. That is essentially ECDLP itself. Rank this low.

**Test if anyone proposes a concrete G.** Exhaustive check on curves with p of 100–2000.

---

### Card 4: A Pollard–Strassen analogue using Riemann–Roch on E

**Mechanism.** Let F(S) = ∏_{j<M} (x(Q) − x(S+[j]G)). It is a function on E of degree 2M whose numerators have the form A_j(x) + 2y_j·y. Build it in Õ(M) with a product tree in F_p[x,y]/(y²−f). Then evaluate it at the giant steps [iM]G in Õ(M). A zero shows that ±k lies in [0, M²).

**Where a gain would come from.** It would need to beat √q the way Pollard–Strassen does for factoring.

**Falsifier, run on paper (rejects this setup).** The cost is exactly Õ(√q) time and Õ(√q) memory, matching BSGS; this is BSGS done with multipoint evaluation. Recursing does not help: a function on E or E² needs degree at least the number of its zeros, so three-level grids cost ≥ L^{2/3}. Harvey's N^{1/5} factoring speed-up relies on the multiplicative order being unknown, which has no analogue when q is a known prime.

**What's left.** An extra hidden structure, like the one in Harvey's method, that I could not identify. Rank last.

---

### Ranking

There are no surviving exponent candidates. Ranked by test value per unit cost:

1. **Card 2** — a published open problem with a cheap falsifier based on bidegree growth.
2. **Card 1** — needs a lattice encoding of splitting.
3. **Card 3** — the low-degree route is ruled out.
4. **Card 4** — ties BSGS.

### Dropped without a card

- **Torsion and special-model symmetrisation** (Faugère–Gaudry–Huot–Renault style, Edwards/Hessian models): these need rational 2-, 3- or 4-torsion, which a prime-order curve doesn't have.
- **Base change to F_{p^n} with x in F_p, or a genus-2 cover:** costs at least p, worse than √p.
- **Batch decomposition over an unstructured factor base:** costs at least p^{2/3} by counting.
- **Twist-based factor bases:** the sums land in the wrong component of the group.

Other sources: [Lauter–Stange PDF](https://arxiv.org/pdf/0803.0728), [McGuire–Mueller 2017/1262](https://eprint.iacr.org/2017/1262), [Pintore 2018](https://ricerca.uniba.it/handle/11586/431821).
