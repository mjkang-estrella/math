# MathDB 366371: a six-point ordinal space with the majorization property that does not embed in the line

**Status: DRAFT.** Zero accepted credit; the campaign root alone accepts. The campaign count (7/20 beyond 39) is unchanged. AI-assisted (Claude Opus 5.5); no human authorship is asserted. This file is the ordinary (non-Lean) proof. The literal Lean module is `proof/OrdinalLine.lean` (sha256 `da892a4d…cec7703f`, byte-identical to the author lane's `expanded-corpus-r61/formal/OrdinalLine.lean`).

## 1. Source and exact statement

Source: K. Keller and E. Petrov, *Ordinal spaces*, Acta Math. Hungar. 160 (2020) 119–152, doi 10.1007/s10474-019-00972-z (online 5 September 2019); arXiv:2412.17391v1 (submitted 23 December 2024). We read the arXiv v1 HTML (`sources/2412.17391.html`, sha256 `95ac5742…`); the published text was not read (Section 8).

**Ordinal space (Definition 1.1).** A nonempty set X with a map δ : X⁴ → {<, =, >} such that for all x, y, u, v, z, w ∈ X:

- (i) δ(x, y, x, y) = '=';
- (ii) δ(x, y, z, w) = δ(y, x, z, w) = δ(x, y, w, z);
- (iii) δ(x, y, z, w) = −δ(z, w, x, y), where −'<' = '>', −'>' = '<', −'=' = '=';
- (iv) δ(x, y, u, v) = δ(u, v, z, w) = '=' implies δ(x, y, z, w) = '=';
- (v) δ(x, y, u, v) = '<' and δ(u, v, z, w) ∈ {'<', '='} imply δ(x, y, z, w) = '<';
- (vi) δ(x, y, u, v) ∈ {'<', '='} and δ(u, v, z, w) = '<' imply δ(x, y, z, w) = '<';
- (vii) δ(x, x, z, w) = '<' if z ≠ w, and δ(x, x, z, w) = '=' if z = w.

We write δ(x, y) < δ(z, w) for δ(x, y, z, w) = '<', and similarly for = and >.

**Embeddability, (7.1)–(7.3).** X ↪ ℝ¹ if there is Φ : X → ℝ such that for all x, y, z, w ∈ X, δ(x, y) <, =, > δ(z, w) holds iff |Φ(x) − Φ(y)| <, =, > |Φ(z) − Φ(w)|, respectively.

**Chains.** For n ∈ ℕ⁺, 𝓘ₙ is the set of tuples (i₀, i₁, …, i_k) ∈ {1, …, n}^{k+1} with k ∈ ℕ⁺ and i₀ ≤ i₁ ≤ ⋯ ≤ i_k (repeats allowed).

**Definition 7.1.** Let x₁, …, xₙ enumerate X, |X| = n, and let (i₀, …, i_k), (j₀, …, j_k) ∈ 𝓘ₙ (same k). Then (i) ∼ (j), respectively (i) ≺ (j), if there is a permutation π of {1, …, k} with

- (7.4) δ(x_{i_{l−1}}, x_{i_l}) = δ(x_{j_{π(l)−1}}, x_{j_{π(l)}}) for all l ∈ {1, …, k}, respectively
- δ(x_{i_{l−1}}, x_{i_l}) ≤ δ(x_{j_{π(l)−1}}, x_{j_{π(l)}}) for all l, but not (7.4).

The enumeration has the *majorization property* if for all k ∈ ℕ⁺ and all such tuples, (i) ≺ (j) implies δ(x_{i₀}, x_{i_k}) < δ(x_{j₀}, x_{j_k}), and (i) ∼ (j) implies δ(x_{i₀}, x_{i_k}) = δ(x_{j₀}, x_{j_k}).

**Conjecture 7.4.** Let (X, δ) be an ordinal space with |X| = n ∈ ℕ⁺ and let there exist an enumeration x₁, …, xₙ of the points of X satisfying the majorization property. Then X ↪ ℝ¹.

**What the source proves.** Proposition 7.3: X ↪ ℝ¹ implies that some enumeration has the majorization property. Theorem 7.5: for |X| = 4, embeddability is equivalent to the existence of an enumeration with the majorization property (and to a third, explicit condition). The source says: "We are not able to say whether the existence of an enumeration with majorization property is also sufficient for embeddability in ℝ¹ if n > 5, but for n ≤ 4 we have sufficiency."

**Reading of "but not (7.4)".** We (and the Lean module) read it as "not all k equalities hold for this same π". The alternative reading "not (i) ∼ (j)" defines the same relation: if the pieces of (i) are termwise ≤ those of (j) under π and the two piece multisets coincide (which is what ∼ says), then every termwise inequality is an equality, because δ restricted to pairs is a total preorder and can be replaced by integer ranks, whose sums would otherwise differ. The diagnostic checks both readings literally for k ≤ 4.

## 2. Theorem

**Theorem.** Conjecture 7.4 is false. On X = {0, 1, 2, 3, 4, 5} let D be the symmetric function with D(x, x) = 0 and the off-diagonal values

| pair | 23 | 34 | 12 | 24 | 01 | 13 | 14 | 45 | 35 | 02 | 25 | 03 | 04 | 15 | 05 |
|------|----|----|----|----|----|----|----|----|----|----|----|----|----|----|----|
| D    | 1  | 2  | 3  | 4  | 5  | 6  | 7  | 8  | 9  | 10 | 11 | 12 | 13 | 14 | 15 |

and δ(x, y, z, w) := compare(D(x, y), D(z, w)). Then (X, δ) is an ordinal space with n = 6; the enumeration x₁ = 0, x₂ = 1, …, x₆ = 5 has the majorization property; and X does not embed in ℝ¹.

Below, indices are shifted by one: chains are nondecreasing tuples in {0, …, 5} and "point i" means x_{i+1}. For a chain I = (i₀ ≤ ⋯ ≤ i_k) its *pieces* are f_I(l) = D(i_{l−1}, i_l), l = 1, …, k; a piece is degenerate if i_{l−1} = i_l, and then f_I(l) = 0.

## 3. (a) It is an ordinal space

D is symmetric, D(x, x) = 0, and D(x, y) ≥ 1 for x ≠ y. Comparing natural numbers is a total preorder, so (i)–(vi) are the reflexivity, symmetry (from symmetry of D), antisymmetry, and transitivity properties of ≤, < and = on ℕ, and (vii) holds because D(x, x) = 0 < D(z, w) iff z ≠ w. ∎

## 4. (b) The identity enumeration has the majorization property, for every k

For a chain I and a threshold t ∈ ℕ, let c_I(t) = #{l ∈ {1, …, k} : f_I(l) ≥ t}.

**Lemma 1 (counting).** Let I, J be chains of the same length k and π a permutation of {1, …, k} with f_I(l) ≤ f_J(π(l)) for all l. Then c_I(t) ≤ c_J(t) for every t. If moreover f_I(l₀) < f_J(π(l₀)) for some l₀, then c_I(t₀) < c_J(t₀) for t₀ = f_J(π(l₀)).

*Proof.* Let S_I(t) = {l : f_I(l) ≥ t}. If l ∈ S_I(t) then f_J(π(l)) ≥ f_I(l) ≥ t, so π maps S_I(t) injectively into S_J(t), giving the first claim. For t = t₀, the image π(S_I(t₀)) ⊆ S_J(t₀) misses π(l₀) ∈ S_J(t₀): if π(l₀) = π(l) with l ∈ S_I(t₀), then l = l₀ by injectivity, but f_I(l₀) < t₀. Hence the inclusion is proper and the inequality strict. ∎

Applying Lemma 1 to π and to π⁻¹: if I ∼ J then c_I(t) = c_J(t) for every t.

**Lemma 2 (reduction).** For a chain I let red(I) be the list obtained by deleting consecutive repeated entries. Then red(I) is a nonempty strictly increasing list in {0, …, 5}, i.e. a nonempty subset of {0, …, 5} listed increasingly; it begins with i₀ and ends with i_k; and for every t ≥ 1, c_I(t) = adj_t(red(I)), where adj_t(A) is the number of consecutive pairs (a, a′) of A with D(a, a′) ≥ t.

*Proof.* Deleting an entry i_l equal to i_{l−1} removes the degenerate piece (i_{l−1}, i_l), whose value 0 is below t ≥ 1, and leaves every other piece unchanged (the piece (i_l, i_{l+1}) becomes (i_{l−1}, i_{l+1}), the same pair). The first and last entries are never removed (the first entry is kept, and the last entry equals the kept entry of its block). A nondecreasing list without consecutive repeats is strictly increasing. ∎

**Lemma 3 (finite check).** For all nonempty strictly increasing lists A = (a₀ < ⋯ < a_r) and B = (b₀ < ⋯ < b_s) in {0, …, 5} (63 × 63 pairs):

- (a) if adj_t(A) ≤ adj_t(B) for all t ∈ {1, …, 15}, with strict inequality for some such t, then D(a₀, a_r) < D(b₀, b_s);
- (b) if adj_t(A) = adj_t(B) for all t ∈ {1, …, 15}, then D(a₀, a_r) = D(b₀, b_s).

*Proof.* Exhaustive finite verification: 3969 pairs and 15 thresholds. This is the Lean theorem `finite_check`, checked by the kernel with `decide +kernel` (no `native_decide`), and it is recomputed independently by `diagnostic.py`. ∎

**Proposition.** The enumeration x_{i+1} = i has the majorization property.

*Proof.* Let I = (i₀ ≤ ⋯ ≤ i_k), J = (j₀ ≤ ⋯ ≤ j_k), k ≥ 1, A = red(I), B = red(J).

*Case I ≺ J via π.* Then f_I(l) ≤ f_J(π(l)) for all l, and f_I(l₀) ≠ f_J(π(l₀)), hence f_I(l₀) < f_J(π(l₀)), for some l₀. By Lemma 1, c_I ≤ c_J everywhere and c_I(t₀) < c_J(t₀) with t₀ = f_J(π(l₀)). Since t₀ > f_I(l₀) ≥ 0 and every value of D is at most 15, t₀ ∈ {1, …, 15}. By Lemma 2 these relations hold for adj_t(A) and adj_t(B) for t ∈ {1, …, 15}, and A, B have the endpoints of I, J. Lemma 3(a) gives D(i₀, i_k) < D(j₀, j_k), i.e. δ(x_{i₀}, x_{i_k}) < δ(x_{j₀}, x_{j_k}).

*Case I ∼ J.* Then c_I = c_J, so adj_t(A) = adj_t(B) for t ∈ {1, …, 15}, and Lemma 3(b) gives equality of the endpoint values. ∎

Remark. Lemma 3 is a statement about 63 × 63 pairs only; Lemmas 1–2 make it cover all k ∈ ℕ⁺, all repeats and all permutations. Literal checks with explicit repeats and permutations for k ≤ 4 (82,957 chain pairs; 0 violations) were run by the author lane, the independent review and `diagnostic.py`; they corroborate but are not used.

## 5. (c) X does not embed in ℝ¹

Suppose Φ : X → ℝ satisfies (7.1). (Only the direction "δ(x, y) < δ(z, w) ⇒ |Φx − Φy| < |Φz − Φw|" is used, so even this one-sided condition is unsatisfiable.)

1. D(0, 0) = 0 < 15 = D(0, 5) gives 0 < |Φ0 − Φ5|. Replacing Φ by −Φ (which preserves all |Φx − Φy|), assume Φ0 < Φ5.
2. For x ∈ {1, 2, 3, 4}: D(0, x) < D(0, 5) and D(x, 5) < D(0, 5), so Φx − Φ0 ≤ |Φx − Φ0| < Φ5 − Φ0 and Φ5 − Φx ≤ |Φ5 − Φx| < Φ5 − Φ0. Hence Φ0 < Φx < Φ5.
3. Therefore |Φ0 − Φx| = Φx − Φ0 for all x, and D(0, 1) < D(0, 2) < D(0, 3) < D(0, 4) gives Φ0 < Φ1 < Φ2 < Φ3 < Φ4 < Φ5.
4. Put gᵢ = Φi − Φ(i−1) > 0 (i = 1, …, 5); then |Φa − Φb| = g_{a+1} + ⋯ + g_b for a < b. Five comparisons of the table give:

| comparison | values | inequality |
|---|---|---|
| D(2,3) < D(3,4) | 1 < 2 | g₃ < g₄ |
| D(1,2) < D(2,4) | 3 < 4 | g₂ < g₃ + g₄ |
| D(0,1) < D(1,3) | 5 < 6 | g₁ < g₂ + g₃ |
| D(1,4) < D(4,5) | 7 < 8 | g₂ + g₃ + g₄ < g₅ |
| D(3,5) < D(0,2) | 9 < 10 | g₄ + g₅ < g₁ + g₂ |

5. Adding them gives g₁ + 2g₂ + 2g₃ + 2g₄ + g₅ < g₁ + 2g₂ + 2g₃ + 2g₄ + g₅, a contradiction. ∎

Hence (X, δ) satisfies every hypothesis of Conjecture 7.4 with n = 6 but X does not embed in ℝ¹, so Conjecture 7.4 is false. ∎

Remark (why a certificate exists). Once the order of the Φ-values is forced (steps 1–3), and since D has no ties, embeddability is the feasibility of a homogeneous system of strict linear inequalities in g ∈ ℝ⁵_{>0}; by Gordan's theorem of the alternative, infeasibility is witnessed by a nonnegative combination of the inequalities summing to zero. The five-term combination above, with all coefficients 1, is such a witness. Since majorization holds, this cancellation is not an instance of majorization: majorization compares the two total intervals of two chains whose pieces match termwise, whereas here the five left-hand intervals and the five right-hand intervals do not arise in that way.

## 6. Lean correspondence (module `OrdinalLine`, namespace `OrdinalSpaces366371`)

| Source | Lean | Notes |
|---|---|---|
| Definition 1.1 (i)–(vii) | `IsOrdinalSpace δ` | structure with fields `ax_i` … `ax_vii`; δ : X → X → X → X → Ordering; (iii) via `Ordering.swap`; "∈ {<, =}" as `≠ .gt` |
| (7.1)–(7.3) | `EmbeddableInLine δ` | ∃ Φ : X → ℝ, three `↔` with \|Φ x − Φ y\| |
| 𝓘ₙ, ≺ | `Prec δ e I J` | I J : Fin (k+1) → Fin n; one π : Equiv.Perm (Fin k); piece l is (I l.castSucc, I l.succ) |
| ∼ | `Sim δ e I J` | same π convention |
| majorization property | `HasMajorization δ e` | ∀ k > 0, ∀ I J monotone (repeats allowed) |
| Conjecture 7.4 | `MajorizationConjecture` | ∀ X δ n (e : Fin n → X), 0 < n → IsOrdinalSpace δ → Bijective e → HasMajorization δ e → EmbeddableInLine δ |
| witness table | `D`, `δW` | values as in Section 2 |
| (a) | `isOrdinalSpace_W` | uses `D_symm`, `D_zero_iff` (kernel `decide`) |
| Lemma 1 | `count_le`, `count_lt`, `card_eq_sum` | |
| Lemma 2 | `adjFrom`, `adj`, `dd`, `lastD`, `red`, `adj_dd`, `lastD_dd`, `pairwise_dd`, `mem_dd`, `dd_cons`, `sum_pieces_eq_adj`, `lastD_ofFn`, `red_mem_sublists`, `adj_red` | recursions via `List.rec` (no compiler auxiliaries) |
| Lemma 3 | `okB`, `finite_check`, `okB_spec` | `decide +kernel`; also covers empty lists (`okB` returns true) |
| Proposition (b) | `majorization_W` | |
| (c) | `core`, `not_embeddable_W` | `core` assumes Φ0 < Φ5; reflection handled in `not_embeddable_W` |
| Theorem | `witness`, `not_majorizationConjecture` | endpoints |

The conjecture is quantified over `X : Type`; its negation for `Type` already refutes the source statement, since the witness lives on `Fin 6`. |X| = n is encoded by the bijection e : Fin n → X; the source's 1-based x₁, …, xₙ correspond to e 0, …, e (n − 1).

## 7. Certified content versus diagnostics

**Lean-certified** (kernel-checked; transitive axioms only propext, Classical.choice, Quot.sound): (a), (b), (c), `witness`, `not_majorizationConjecture`.

**Diagnostics only** (not used by any proof, not reproduced in Lean, no claim made from them):

- The author lane's scan (`evidence/author/outputs/ordinal-5-*.txt`, scipy LP) reports that for n = 5 every majorizing weak order (477, of which 114 tie-free) found by its search is embeddable.
- The same scan for n = 6, tie-free, reports 2612 majorizing linear orders of which 4 are non-embeddable, our witness among them (`evidence/author/outputs/ordinal-6-strict.txt`).

These scans use floating-point LP and a pruned search; they were not independently reproduced. **No minimality claim is made** (in particular, n = 5 is not claimed to satisfy the conjecture).

## 8. Context, prior art and limitations

- Classical measurement theory (Scott 1964; Krantz, Luce, Suppes and Tversky, *Foundations of Measurement* I, 1971) characterizes representability of finite structures by cancellation conditions, i.e. by solvability of linear inequality systems, and conditions of bounded order do not suffice in general. The classical analogue of the present phenomenon is Kraft, Pratt and Seidenberg (1959): a five-atom qualitative probability satisfying de Finetti's axioms but admitting no agreeing measure.
- Those results do not imply the present one. Majorization has unbounded order (every k) but a restricted shape: each side is a chain along the enumeration, and only its total interval is compared. Whether this family suffices for line embeddability is exactly what Conjecture 7.4 asserted; an explicit example was needed. The result is expected in spirit and modest in depth (a computer-found six-point witness with a five-term certificate).
- Citing works checked: C. Pech and M. Pech, *Echeloned spaces* (Forum Math. Sigma 2025; arXiv:2312.11141), text read by the independent review: metrizability, Fraïssé limits and Ramsey properties, nothing on line embedding or majorization. G. Stumme, D. Dürrschnabel and T. Hanika, *Towards ordinal data science* (TGDK 1(1), 2023; arXiv:2307.09477): identified by the review as a position paper; its body was not read by us.
- Searches (2026-11-01): one web search and one arXiv author search by the author lane; five web searches by the independent review, one specific to this conjecture; no refutation found. The classical unidimensional-scaling and absolute-difference literature (e.g. Coombs unfolding) was not searched body by body.
- **The published Acta Math. Hungar. text was not read** (institutional access only). That its Conjecture 7.4 coincides with arXiv v1 is assumed. The arXiv posting (December 2024) postdates the journal publication (2019/2020); MathDB cites the arXiv version.
- **No priority claim** is made beyond the bounded search described.
