# r119 mathematical notes

## 353203: uniqueness of the power-domination TAR graph of K_{s,t}

**Setting.** H is a graph on V = A ⊔ B with |A| = s and |B| = t, where s, t ≥ 3 and (s,t) ≠ (3,3). H has no isolated vertices, and the PD sets of H are exactly those of K_{A,B}:

- every set meeting both A and B;
- every set of at least s − 1 vertices of A;
- every set of at least t − 1 vertices of B.

By the survey arXiv:2406.05509, Theorem t:main (Bong, Carlson, Curtis, Haas and Hogben, Graphs Combin. 2023), this is equivalent to PD-TAR(H) ≅ PD-TAR(K_{s,t}).

**Forts.** A fort is a nonempty set F such that every vertex outside F has 0 or at least 2 neighbours in F. A set S is PD exactly when N[S] meets every fort, that is, when S meets N[F] for every fort F.

**Blocker step (proved).** The PD family is the family of transversals of {N[F] : F a fort}. The minimal PD sets are:

- the pairs {a,b} with a ∈ A and b ∈ B;
- the (s − 1)-subsets of A;
- the (t − 1)-subsets of B.

Their blocker is {A ∪ {u,v}} ∪ {B ∪ {x,y}}. Hence the inclusion-minimal sets N[F] are exactly these sets. In particular, for each pair {x,y} ⊂ A there is an inclusion-minimal fort Ψ_xy with N[Ψ_xy] = B ∪ {x,y}. Any fort inside it has the same closed neighbourhood, since A \ {x,y} is nonempty. The same holds on the B side for forts Φ_uv.

**Case Q = ∅ for every pair (proved).** Suppose Ψ_xy ∩ B = ∅ for every pair {x,y}.

1. Then Ψ_xy = {x,y}, so every b ∈ B is adjacent to both x and y, and N(x) ⊆ B ∪ {y}.
2. Using two different partners y and z of x (possible because s ≥ 3), we get N(x) ⊆ B, so A is independent and A–B is complete.
3. For a pair {u,v} ⊂ B, the set B \ {u,v} is non-PD. A fort avoiding N[B \ {u,v}] must lie inside {u,v}, so it is {u,v}, and no vertex of B \ {u,v} is adjacent to u or v.
4. Since t ≥ 3, this makes B independent, so H = K_{s,t}.

**Remaining case.** Some minimal Ψ_xy contains q ∈ B. Then N_A(q) ⊆ {x,y}.

- For every b′ ≠ q, the fort Φ_qb′ cannot be {q,b′}, because that would force A ⊆ N(q). So there is a "poor" p ∈ A with N_B(p) ⊆ {q,b′}.
- Symmetrically, every pair {p,z} ⊂ A has a poor B-vertex.

The missing lemma is that this mutual-poverty configuration contradicts the blocker structure. SAT found no such graph for any s + t ≤ 11, nor for (3,8), (3,9) or (4,7). Ablation shows that dropping any one constraint group makes the instance satisfiable.

## 361213: alternative proof of d⊥ = q − p (already published, zero credit)

Notation: U = U_{q+1}, ω ∈ F_{q²} \ F_q, and M(t) = (t − ω)/(t − ω^q). M maps F_q ∪ {∞} onto U, and the points of M(F_p ∪ {∞}) are exactly the roots of the polynomial below, which has degree p + 1 and the self-conjugate-reciprocal shape b x^{p+1} + a x^p + a^q x + b^q.

**Explicit codeword.** Expanding (ω^q x − ω)^p (x − 1) − (ω^q x − ω)(x − 1)^p gives

- b = ω^{pq} − ω^q,
- a = ω − ω^{pq}.

The trace codeword c_(a,b) therefore vanishes at exactly p + 1 points of U, so it has weight q − p.

**Bounds.** The source (Theorem sec3 thm4) gives the lower bound d⊥ ≥ q − p. Together with this codeword, d⊥ = q − p for every s.

**Prior art.** This is already published as arXiv:2410.15070, Theorem 3.4 with i = 1.
