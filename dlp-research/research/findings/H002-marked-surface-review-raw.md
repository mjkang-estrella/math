# Unaccepted raw marked-surface review

Retained for provenance; H002-marked-surface-disposition.md qualifies major
overclaims about equivalence, isotropy, map representations and oracle inputs.

# V1 review: the marked quotient and the short quadratic relation

**Verdict:** V1 does not give a new way to attack ECDLP. Computing a non-scalar marked endomorphism costs the same as ECDLP, up to polylog conversions in both directions. The card's "~q^(1/3) total" therefore needs an ECDLP algorithm that already runs in q^(1/3). No ECDLP improvement is supported (still **NONE**).

This is not a proof that the idea is impossible. It shows the reformulation adds no new leverage. Generic lower bounds play no part in this argument. I made no edits, ran no experiments and started no child agents.

## 1. Algebra check

**The kernel quadratic is correct.** Write Q = dG and M = [[a,b],[c,e]]. Then M(tG, tdG) = ((a+bd)tG, (c+ed)tG). This lies in K exactly when b·d² + (a−e)·d − c ≡ 0 (mod q).

**The lattice claim is correct.** The condition is linear in (a,b,c,e) and the coefficient of c is −1. So the solutions form an index-q sublattice of Z⁴ that contains the scalar matrices. Factoring out scalars leaves the lattice {(u,b,c) : b·d² + u·d − c ≡ 0}, with u = a−e, which has rank 3 and index q. A box argument gives a nonzero vector with all entries at most about q^(1/3).

**Degenerate polynomials only matter in the integer case if you allow large entries.** If the vector is nonzero with all entries below q, the polynomial cannot vanish identically. If b = u = 0, then c ≡ 0, so c = 0. If b = 0, the relation is linear and gives one value of d. If b ≠ 0, it gives at most two roots, and the discriminant is automatically a square because d is a root.

**The decisive problem is that the lattice is only known once d is known.** Its basis is {(1,0,d), (0,1,d²), (0,0,q)}. A candidate triple (u,b,c) can be tested cheaply: solve the quadratic mod q, then check root·G = Q. But each triple only covers at most 2 values of d. Searching the q^(1/3) box is brute force over d, two values per test.

Shortness alone gives no advantage. Every residue mod q is a root of some small quadratic; this is an elementary fact and should be cited as such, not presented as new.

**The "dense q^(2/3)-degree map" cost objection is misplaced.** Integer matrices of any size up to q are evaluated in polylog time by double-and-add. Their degree does not matter. The real obstacle is finding the right triple, not evaluating the map.

## 2. Ordinary End(E) > Z

No elliptic curve over F_p has End(E) = Z, since Frobenius π is always an endomorphism. The card should be restated over O = End(E) ⊇ Z[π]. Doing so exposes three things the card misses.

- **Reduction to F_q.** π fixes G. Elements of O act on ⟨G⟩ through a reduction map O → O/𝔭 ≅ F_q, where 𝔭 is the prime of O above q containing π−1. For a matrix over O, the descent condition is the same quadratic with entries replaced by their reductions mod 𝔭. Any informative content passes through F_q³, so the extra rank does not add new relations about d.
- **Short degenerate vectors.** Any matrix with all entries in 𝔭, for example (π−1)·E_ij, kills K and descends trivially. In the Z[π] basis, π−1 has coefficient vector (−1, 1). So lattice reduction over O tends to output useless matrices whose polynomial is identically zero. Non-degeneracy must be stated as **M not congruent to a scalar mod 𝔭**, not as "nonzero vector".
- **The quotient is isomorphic to E² when q = #E(F_p).** In that case π−1 has kernel exactly ⟨G⟩, so E/⟨G⟩ ≅ E. Then N = [[π−1, 0], [−d, 1]] has kernel exactly K, so E²/K ≅ E².

The last point gives the full equivalence. Every endomorphism of E² with kernel K has the form V·N with V ∈ GL₂(O). Mod 𝔭, V·N has rank 1 with right kernel spanned by (1, d), which reads off d. In the other direction, d gives M = [[1,0],[d,0]], which is non-scalar mod 𝔭.

This applies to any of:
- a kernel-K map,
- an explicit isomorphism from the quotient to E²,
- a non-scalar descending matrix over O.

Each converts to d in polylog time and back. If the cofactor h is greater than 1, the conclusion stays the same: π−1 factors through E/⟨G⟩ with an extra degree-h piece. I have not written that case out in full.

## 3. Unpolarized vs. polarized invariants

**Unpolarized invariants carry no information about d.** For q = #E(F_p), the quotient is abstractly E² for every d. The card's shear point holds and is stronger than stated.

**The induced (1,q)-polarized class probably determines d, up to the small unitary automorphism group of (E², product polarization).** This is my unverified assessment and needs a check before anyone relies on it. Even if true, using it needs two steps that have no known cheap method:
- **Computing it from (G,Q):** this needs a cyclic, non-isotropic degree-q isogeny from E². I know of no Vélu-type formula for that, and a square-root Vélu analogue would at best cost Õ(√q), which only ties with rho.
- **Inverting the class back to d:** this means choosing among the q+1 order-q subgroups of ker λ, which is another search.

The map from d ∈ F_q to a moduli point over F_p has no known algebraic structure, so it behaves like the map d ↦ dG.

## 4. Primary sources

- **[Anni–Bisson–Iezzi–Lorenzo García–Wesolowski 2025](https://arxiv.org/abs/2503.08925)**
  - Inputs are **principally polarized** surfaces: a genus-2 Jacobian, a product of the two curves, or a pair (φ, Jac C) with φ an explicit isogeny. Isogenies of non-simple surfaces are explicit maps or kernels, and coprime-degree isogenies must come with good representations (Prop. 5.1).
  - Our quotient is (1,q)-polarized. A "marking" for it would be an explicit degree-q map whose description already contains d.
  - The paper says the abstract ring of E×E is easy, while "the computational difficulty here is to find an explicit isomorphism or isogeny from A to E×E". That is exactly V1's missing step, which the paper treats as hard.
  - In Theorem 5.7 the endomorphism ring of E×E/(i,j)(α_p) is written in terms of the kernel parameter i/j, which is **given as input**, not extracted.
  - Robert's polynomial-time test checks candidate endomorphisms. It does not search for them, and the paper notes it does not give polynomial-time ring computation.
  - Conclusion: no input representation available here below √q is accepted.
- **[Square-root Vélu (Bernstein–De Feo–Leroux–Smith)](https://arxiv.org/abs/2003.10118)**
  - It needs a kernel generator of prime order ℓ on an elliptic curve and costs Õ(√ℓ) field operations.
  - It provides no abelian-surface version and no cyclic-kernel version, and nothing below √ℓ.

## 5. Conditional bridge, dependency and falsifier

**Precise bridge:** a time-T procedure that takes (E,G,Q) and outputs M ∈ M₂(O) with M not congruent to a scalar mod 𝔭 and M(G,Q) ∈ ⟨(G,Q)⟩ yields d in time T + polylog. The converse also holds. So the bridge is an equivalence, and the open assumption is simply "ECDLP in q^(1/3)".

**Concrete dependency:** any step producing a marked quotient, a ring with its marking, or a polarized class must be checked for whether its output already contains d. By the equivalence above, any output that can be transported back to E² does.

**Cheapest falsifier:** no wall-clock run is needed, because the algebra above settles it. If a confirming check is wanted, a tiny exact script over small primes with q = #E could verify:
1. ker(π−1) = ⟨G⟩;
2. LLL over the Z[π] lattice returns 𝔭-degenerate matrices;
3. each informative triple covers at most 2 values of d;
4. the right kernel of V·N mod 𝔭 is (1, d).

Results 1 and 4 would confirm the equivalence.

## 6. More explicit route worth testing

None found below √q. Two related routes that are already known:
- **With d²G given for free,** the quadratic relation b·(d²G) + u·Q = c·G can be found by meet-in-the-middle in about q^(2/3), which is worse than rho. Producing d²G from (G,Q) is the Diffie–Hellman problem. Using extra points like d^k·G is Cheon's 2006 auxiliary-input attack (citation from memory, not re-checked here), which assumes those points are supplied.
- **The polarized-class question in §3** is mathematically interesting. It is an equivalence or uniqueness question, though, not an attack.

## Scoped verdict

V1 should be recorded as a **polylog-equivalent reformulation of ECDLP**. It should not be cited as an obstacle proof or as a discovery, and its novelty is unknown. The card needs five corrections:
1. Restate it over O = End(E) rather than integer matrices.
2. Define non-degeneracy as "not a scalar mod 𝔭".
3. Note that the quotient is E² when q = #E(F_p).
4. Drop the dense-degree cost objection.
5. Reject any free quotient or ring oracle with a marking as one that already contains d.

Recommendation: keep the polarized-class question in §3 as a high-risk, low-priority note, and stop spending effort on V1.
