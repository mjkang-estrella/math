# Uniqueness of PD-TAR(K_{s,t}): proof (MathDB 353203)

Lane pdtar-proof-r1, 2026-11-02. This is a hypothesis-lane write-up. It is not accepted, and root decides.

## 0. Statement and definitions

**MathDB 353203, verbatim.** "Let K_{s,t} be the complete bipartite graph with part sizes s and t, and let PD^TAR(K_{s,t}) denote its power domination reconfiguration graph under token addition/removal reconfiguration. **Uniqueness conjecture.** PD^TAR(K_{s,t}) is unique if and only if s ≠ 2 and t ≠ 2."

- Source: arXiv:2201.01798 (Bjorkman, Bozeman, Ferrero, Flagg, Grood, Hogben, Jacob and Reinhart).
- The conjecture is the `conj` environment right after Proposition `p:K33` in the arXiv TeX. A search-engine excerpt numbers it 3.24 (arXiv) and 3.25 (La Matematica 5 (2026), article 8).
- The raw MathDB line (chunk-0008, line 2515) has sha256 fb3b4a73e92d8196e75e36cb9ee60ad6ad119a70c59be6cb44744734c24f3935, re-verified in this lane.

All graphs are finite and simple. N(v) is the open neighbourhood, N[v] = N(v) ∪ {v}, and for a set X, N[X] = ∪_{x∈X} N[x].

**Power domination** (the source's definition, §1 of arXiv:2201.01798). For S ⊆ V(G), set P⁰[S] = S and P¹[S] = N[S]. For i ≥ 2,

P^i[S] = P^{i−1}[S] ∪ {u : N(v) \ P^{i−1}[S] = {u} for some v ∈ P^{i−1}[S]}.

S is a *power dominating (PD) set* if P^i[S] = V(G) for some i. The PD sets form an up-closed family: P^i[S] is monotone in S, by induction on i.

**TAR graph** (source Definition in §3). PD^TAR(G) has the PD sets of G as its vertices. Two of them, S₁ and S₂, are adjacent iff |S₁ ⊖ S₂| = 1.

**Unique** (source §3.3, verbatim). "For a graph G with no isolated vertices, we say PD^TAR(G) is unique if for any graph H with no isolated vertices, PD^TAR(G) ≅ PD^TAR(H) implies H ≅ G."

**Range.** s and t are positive integers. K_{s,0} has isolated vertices, so it is outside the definition.

**Fort.** A nonempty F ⊆ V(G) is a fort if |N(v) ∩ F| ≠ 1 for every v ∉ F. This is the survey's definition (arXiv:2406.05509, line 411).

## 1. The reduction (published)

**Theorem R** (Bong, Carlson, Curtis, Haas and Hogben, *Graphs Combin.* 39 (2023) Paper 86, Thm 1.1; restated as Theorem t:main of arXiv:2406.05509v2).

> Let X be a robust X-set parameter and let G, G′ be base graphs with X^TAR(G) ≅ X^TAR(G′). If X(K₁) = 0 or G and G′ have no isolated vertices, then there is a relabeling of the vertices of G′ such that G and G′ have exactly the same X-sets.

- Power domination is an original, hence robust, X-set parameter. This is stated in the survey ("power domination is an original X-set parameter, so Theorem t:main applies"). The original axioms are checked in the source (§3, "Observe that power domination satisfies the conditions in Definition 2.1").
- The relabeling is a bijection V(G′) → V(G). Equal orders also follow independently from the source's Corollary labelled `c:pd-iso-props`: |V(G)| = Δ(PD^TAR(G)).
- Applicability: both graphs in the uniqueness definition have no isolated vertices, which is exactly the theorem's hypothesis. No connectedness or order assumption on H is needed; the theorem itself yields the equal order and the bijection.

**Consequence.** Let G = K_{s,t} on V = A ⊔ B with |A| = s and |B| = t, and let H have no isolated vertices with PD^TAR(H) ≅ PD^TAR(G).

- Theorem R gives a bijection ψ : V(H) → V. The graph H′ = ψ(H) on V satisfies PD(H′) = PD(K_{A,B}) and H′ ≅ H.
- Conversely, H′ = K_{A,B} gives H ≅ K_{s,t}.

So uniqueness of PD^TAR(K_{s,t}) for s, t ≥ 3 and (s,t) ≠ (3,3) follows from the following.

> **Core Theorem.** Let s, t ≥ 3 with (s,t) ≠ (3,3). Let H be a graph on V = A ⊔ B (|A| = s, |B| = t) whose PD sets are exactly those of K_{A,B}. Then H = K_{A,B}.

The hypothesis "H has no isolated vertices" is not needed in the Core Theorem; it is derived in Lemma 1(b).

## 2. Fort duality

**Lemma 0.** For every graph G and S ⊆ V(G): S is PD ⇔ F ∩ N[S] ≠ ∅ for every fort F of G.

*Proof.*

(⇐) Suppose S is not PD. The sequence P^i[S] is increasing and stabilises at some O ≠ V. Stability means no v ∈ O has exactly one neighbour outside O. So F = V \ O is nonempty, and every vertex outside F (that is, in O) has 0 or at least 2 neighbours in F. Hence F is a fort, and F ∩ N[S] = ∅ because N[S] = P¹[S] ⊆ O.

(⇒) Let F be a fort with F ∩ N[S] = ∅, and suppose some vertex of F is eventually observed. Let i ≥ 2 be the least round with P^i[S] ∩ F ≠ ∅; then P^{i−1}[S] ∩ F = ∅. Take u ∈ P^i[S] ∩ F, and let v ∈ P^{i−1}[S] with N(v) \ P^{i−1}[S] = {u}.

- v ∉ F, and v has the neighbour u ∈ F. Because F is a fort, v has a second neighbour u′ ∈ F.
- u′ ∉ P^{i−1}[S], so N(v) \ P^{i−1}[S] ⊇ {u,u′}. This is a contradiction.

So F is never observed, and S is not PD. ∎

**Fort facts.** Let F be a fort.

- (F1) If x ∈ F then N[x] ⊆ N[F].
- (F2) If x ∈ N[F] \ F then |N(x) ∩ F| ≥ 2.
- (F3) If {x} is a fort, then x is isolated.

Note also that y ∈ N[x] ⇔ x ∈ N[y]. So F ∩ N[S] = ∅ ⇔ N[F] ∩ S = ∅.

## 3. Setting and the two blocker lemmas

From now on, s, t ≥ 3, and H is a graph on V = A ⊔ B with PD(H) = PD(K_{A,B}). For a ∈ A and b ∈ B write β(a) = N_H(a) ∩ B and α(b) = N_H(b) ∩ A.

**Facts about K = K_{A,B}.**

- (K1) For a ∈ A and b ∈ B, the set {a,b} is PD in K, since N[{a,b}] = V.
- (K2) For x ∈ A, A \ {x} is PD in K: N[A\{x}] ⊇ (A\{x}) ∪ B, and then any b forces x.
- (K3) For distinct x, y ∈ A, A \ {x,y} is not PD in K. The set {x,y} is a fort of K (every b sees both x and y, and every other a sees neither) and it avoids N_K[A\{x,y}] = (A\{x,y}) ∪ B. Then apply Lemma 0.
- The same three facts hold with A and B exchanged.

**Lemma 1.**

- (a) For every fort F of H: either A ⊆ N[F] and |N[F] ∩ B| ≥ 2, or B ⊆ N[F] and |N[F] ∩ A| ≥ 2.
- (b) H has no isolated vertex.

*Proof.*

(a) By (K1) and Lemma 0, N[F] meets {a,b} for all a ∈ A and b ∈ B. So A ⊆ N[F] or B ⊆ N[F]. Suppose B ⊆ N[F]. By (K2) and Lemma 0, N[F] meets A\{x} for every x ∈ A, so N[F] ∩ A is not contained in any singleton, that is, |N[F] ∩ A| ≥ 2. The other case is symmetric.

(b) If v ∈ A were isolated, then {v} would be a fort (vacuously) with N[{v}] = {v}, contradicting (a). The same holds for v ∈ B. ∎

**Lemma 2 (pair forts).**

- For distinct x, y ∈ A there is a fort Ψ = Ψ_{xy} of H with N[Ψ] = B ∪ {x,y}.
- For distinct u, v ∈ B there is a fort Φ = Φ_{uv} of H with N[Φ] = A ∪ {u,v}.

Consequently Ψ_{xy} ⊆ B ∪ {x,y} and Φ_{uv} ⊆ A ∪ {u,v}.

*Proof.* By (K3), A \ {x,y} is not PD in H. Lemma 0 gives a fort Ψ with N[Ψ] ∩ (A\{x,y}) = ∅. Since s ≥ 3, A ⊄ N[Ψ], so Lemma 1(a) gives B ⊆ N[Ψ] and |N[Ψ] ∩ A| ≥ 2. Hence N[Ψ] ∩ A = {x,y}. The B case is symmetric, using t ≥ 3. ∎

The whole problem is symmetric under (A, s) ↔ (B, t), because the PD family of K_{A,B} equals that of K_{B,A}. Every lemma below therefore has a mirror statement.

## 4. Cross-degree lemmas

**Lemma 3.** β(a) ≠ ∅ for every a ∈ A, and α(b) ≠ ∅ for every b ∈ B.

*Proof.* Suppose β(p) = ∅, so N(p) ⊆ A. Let y ∈ A \ {p} and Ψ = Ψ_{py}. Then p ∈ N[Ψ].

- If p ∉ Ψ, then by (F2) p has two neighbours in Ψ. They lie in Ψ ∩ A ⊆ N[Ψ] ∩ A \ {p} = {y}. That is impossible.
- So p ∈ Ψ, and (F1) gives N(p) ⊆ N[Ψ] ∩ A \ {p} = {y}.

Doing this for two distinct y, y′ ∈ A \ {p} (possible since s ≥ 3) gives N(p) = ∅, contradicting Lemma 1(b). The mirror statement uses t ≥ 3. ∎

**Lemma 4.** No a ∈ A has N(a) = {c} with c ∈ B. Mirror: no b ∈ B has N(b) = {a} with a ∈ A.

*Proof.* Take distinct c′, c″ ∈ B \ {c} (t ≥ 3) and Φ = Φ_{c′c″}. Then a ∈ N[Φ]. Since deg a = 1, (F2) forces a ∈ Φ, and (F1) gives c ∈ N[Φ] = A ∪ {c′,c″}. That is a contradiction. ∎

**Lemma 5.** If |β(a)| = 1 for some a ∈ A, or |α(b)| = 1 for some b ∈ B, then s = t = 3.

*Proof.* Let β(a) = {c}.

**Step (i): the structure around a.** By Lemma 4, N_A(a) ≠ ∅. For y ∈ A \ {a}, put Ψ = Ψ_{ay}. Then a ∈ N[Ψ], and there are two cases.

- (α) a ∈ Ψ. Then by (F1), N_A(a) ⊆ {y}.
- (β) a ∉ Ψ. Then by (F2), a has two neighbours in Ψ ⊆ B ∪ {a,y}. They must be c and y. So a ~ y, c ∈ Ψ and y ∈ Ψ.

Now consider the possible y.

- If some y ∈ A \ {a} were not adjacent to a, case (β) is excluded. Case (α) gives N_A(a) ⊆ {y}, but y ∉ N_A(a), so N_A(a) = ∅, which is impossible. Hence N_A(a) = A \ {a}.
- Since s ≥ 3, |N_A(a)| ≥ 2, so case (α) never occurs. Case (β) holds for every y ∈ A \ {a}, so c, y ∈ Ψ_{ay}.
- By (F1), α(c) ⊆ {a,y} and N_A(y) ⊆ {a}. Using two values of y gives α(c) = {a}. Also N_A(y) = {a} for every y ∈ A \ {a}, since y ~ a.

**Step (ii): the mirror structure around c.** Since |α(c)| = 1, the mirror of step (i) applies to c. So c is adjacent to all of B \ {c}, and N_B(b) = {c} for every b ∈ B \ {c}.

**Step (iii): counting.** Let y, y′ ∈ A \ {a} be distinct and Ψ = Ψ_{yy′}.

- Since a ∈ A \ {y,y′}, Ψ ∩ N[a] = ∅. Here N[a] = A ∪ {c}, so Ψ ⊆ B \ {c}.
- Every b ∈ B \ {c} lies in N[Ψ]. If b ∉ Ψ, it would need a neighbour in Ψ ⊆ B \ {c}, but N_B(b) = {c}. So Ψ = B \ {c}.
- Then {y,y′} = N[Ψ] ∩ A = ∪_{b ∈ B\{c}} α(b). The right-hand side does not depend on the pair {y,y′}.
- So A \ {a} has only one pair, that is, s = 3. The mirror argument with Φ_{bb′} for b, b′ ∈ B \ {c} gives t = 3.

The case |α(b)| = 1 is the mirror image. ∎

**Corollary 5′** (Lemmas 3 and 5). **If (s,t) ≠ (3,3), then |β(a)| ≥ 2 for all a ∈ A and |α(b)| ≥ 2 for all b ∈ B.**

(At (s,t) = (3,3) the structure in Lemma 5 really occurs: it is K_{3,3} with its bipartition relabelled, A′ = {a} ∪ (B\{c}) and B′ = {c} ∪ (A\{a}). This explains why (3,3) is "unique" only up to relabelling.)

## 5. Completeness between A and B

**Lemma 6.** Let s, t ≥ 3 with (s,t) ≠ (3,3). Then every a ∈ A is adjacent to every b ∈ B.

*Proof.* By symmetry we may assume t ≥ 4. If s ≥ 4 and t = 3, swap the roles of A and B; all ingredients used below have mirror versions.

Suppose a ≁ b with a ∈ A and b ∈ B. Fix b′ ∈ B \ {b} and let Φ = Φ_{bb′}.

- If Φ ∩ A = ∅, then Φ ⊆ {b,b′}. By (F3) and Lemma 1(b), Φ = {b,b′}. Then a ∈ N[Φ] makes a adjacent to b or b′, hence to both by the fort property. This contradicts a ≁ b.
- So there is p ∈ Φ ∩ A. By (F1), β(p) ⊆ {b,b′}. By Corollary 5′, β(p) = {b,b′}.

Since t ≥ 4, pick distinct c, c′ ∈ B \ {b,b′}, and let Φ′ = Φ_{cc′}.

- p ∉ Φ′, since otherwise β(p) ⊆ {c,c′} by (F1).
- p ∈ N[Φ′], so by (F2) p has two neighbours in Φ′ ⊆ A ∪ {c,c′}. Both lie in A because p ≁ c, c′.
- Hence |N_A(p)| ≥ 2. Pick one such neighbour p′ ∈ Φ′ ∩ A. By (F1) and Corollary 5′, β(p′) = {c,c′}.

Symmetrically, p′ ∉ Φ_{bb′} and p′ ∈ N[Φ_{bb′}], and p′ ≁ b, b′. So |N_A(p′)| ≥ 2.

Now let Ψ = Ψ_{pp′}, which uses s ≥ 3.

- If p ∈ Ψ, then N_A(p) ⊆ {p′} by (F1), which is impossible. Likewise p′ ∉ Ψ. So Ψ ⊆ B.
- p ∈ N[Ψ] \ Ψ, so by (F2) p has two neighbours in Ψ ⊆ B. These lie in β(p) = {b,b′}, so b ∈ Ψ.
- By (F1), α(b) ⊆ N[Ψ] ∩ A = {p,p′}. But p′ ≁ b, because β(p′) = {c,c′}. So α(b) ⊆ {p}.

This contradicts Corollary 5′ (|α(b)| ≥ 2). ∎

## 6. Independence of both sides

**Lemma 7** (as in the r119 notes). If A–B is complete and s, t ≥ 3, then A and B are independent, so H = K_{A,B}.

*Proof.* Let x, y ∈ A be distinct and Ψ = Ψ_{xy}.

- Pick z ∈ A \ {x,y}. Then Ψ ∩ N[z] = ∅ by Lemma 2, and N[z] ⊇ B by completeness. Since Ψ ⊆ B ∪ {x,y}, this gives Ψ ⊆ {x,y}.
- By (F3) and Lemma 1(b), Ψ = {x,y}.
- So no z ∈ A \ {x,y} is adjacent to x (or to y).

As every edge xz inside A has some y ∉ {x,z} (s ≥ 3), A is independent. B is independent symmetrically. ∎

**Core Theorem** follows from Lemmas 6 and 7. ∎

## 7. The full conjecture

**Theorem.** For all positive integers s, t: PD^TAR(K_{s,t}) is unique ⇔ s ≠ 2 and t ≠ 2.

*Proof.* By symmetry, assume s ≤ t.

- **s = 2 (any t ≥ 2).** Source Corollary labelled `mPDS:n-3:K2t`: PD^TAR(K_{2,t}(e)) ≅ PD^TAR(K_{2,t}). The graph K_{2,t}(e) has no isolated vertices and one more edge, so it is not isomorphic to K_{2,t}. Hence the TAR graph is not unique.
- **t = 2, s = 1.** K_{1,2} = P₃. In P₃ and in K₃ every nonempty set is PD: a leaf of P₃ dominates the centre, and the centre then forces the other leaf. On a common 3-element vertex set the two TAR graphs are equal, and K₃ ≇ P₃. So the TAR graph is not unique.
- **s = t = 1.** PD^TAR(K₂) ≅ P₃. If H has no isolated vertices and PD^TAR(H) ≅ P₃, then |V(H)| = Δ(P₃) = 2 by the source Corollary labelled `c:pd-iso-props`. So H = K₂.
- **s = 1, t ≥ 3.** Source Theorem labelled `upperPDn-3` (numbered 3.16 in the journal version, per the search-engine excerpt).
- **s = t = 3.** Source Proposition labelled `p:K33` (3.23 in the arXiv version, 3.24 in the journal version, per the search-engine excerpt).
- **s, t ≥ 3, (s,t) ≠ (3,3).** Theorem R together with the Core Theorem, as in §1. **This is the new part.** ∎

## 8. Relation to existing results (is this a bridge?)

- **Source.** The source proves:
  - K_{1,t} uniqueness, via the upper PD number and Proposition upperpdconnected;
  - K_{2,t} non-uniqueness, via Lemma k2tminimalsets on minimal PD sets;
  - K_{3,3} uniqueness, via degree and regularity arguments specific to six vertices.

  None of these uses forts or applies beyond those orders. The (3,3) proof does not extend: it uses that every 2-set is PD. That fails for max(s,t) ≥ 4.
- **Survey.** The survey arXiv:2406.05509v2 has the domination analogue (Prop. on D^TAR(K_{p,q})). It is proved by domination-specific arguments: minimal dominating sets, with A \ {b_i} dominating. It has nothing for power domination, and it restates the PD conjecture as open in Sept 2025.
- **The new ingredients here** are:
  - the blocker identification of the minimal closed neighbourhoods of forts (Lemmas 1–2);
  - the cross-degree lemmas (Lemmas 3–5), which isolate (3,3) as the only place a degree-one cross neighbourhood can occur;
  - the two-sided pair-fort argument of Lemma 6.

  The argument is short (about two pages), but it is not a one-paragraph consequence of any stated lemma in the source or the survey.
- **Prior resolution.** No 2024–2026 resolution was found; see `results.json` → prior_art. The La Matematica (2026) version still states the conjecture, according to search-engine excerpts of the publisher page; direct access to it was refused. Root should confirm.

## 9. Computational sanity checks (not part of the proof)

All checks were run with `scripts/limited.py`: 2 CPUs, CPU 120 s, wall 140 s, RSS 6 GiB, MALLOC_ARENA_MAX=2. Logs are in `logs/`.

- **`verify_lemmas.py`.** An exhaustive check over all graphs on A ⊔ B for (3,3), (3,4) and (4,3), with each lemma tested under only the hypotheses its proof uses.
  - Zero failures.
  - Non-vacuous counts, for (3,4) / (4,3) / (3,3):
    - L1: 4.8×10⁷ / 4.8×10⁷ / 3.6×10⁵ forts;
    - L2: 4360 / 8 / 38 graphs;
    - L3 (A-leaf version): 8 / 4360 / 38;
    - L4 structure: 912 / 0 / 18.
  - L5 instances occur only at (3,3) (9 instances), as predicted.
  - Theorem check: exactly 1 graph at (3,4) and at (4,3), namely K; at (3,3), exactly the 10 relabelled copies of K_{3,3}.
  - L0 (fort duality) was checked on all 2,097,152 (graph, S) pairs on six vertices.
- **`enum_groups.py`.** All 2²¹ graphs at (3,4): exactly one graph has K_{3,4}'s PD family.
- **`perturb.py`.** K_{s,t} with every single and double edge flip plus 3000 random 3–8-flips, for (s,t) ∈ {(3,4), (4,4), (3,5), (4,5), (5,5), (3,6), (4,6), (5,6), (6,6)}. No perturbation keeps the PD family.
- **r119 SAT logs (copied, read-only).** UNSAT for every s + t ≤ 11 and for (3,8), (3,9), (4,7). These agree with the theorem.
