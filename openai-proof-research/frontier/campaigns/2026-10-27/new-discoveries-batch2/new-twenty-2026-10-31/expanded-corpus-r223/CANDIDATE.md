# CANDIDATE: 371607, a counterexample to Venturi's rank-two word conjecture

**Status: candidate only, with zero credit unless root accepts it.** The significance risk is high and is stated first.

## Significance risk (read this first)

- The literal conjecture fails for the most standard object in synchronizing-groups theory: a group whose sum-zero (augmentation) module is irreducible, together with a constant letter. An example is S_3 = ⟨(0 1 2), (0 1)⟩ plus the constant map on 3 states. Root may class this as a trivial small-order failure (the 373480 precedent).
- The binary example below is less degenerate. Its permutation letter generates a *cyclic* group, which is C-reducible, so irreducibility has to come from the interaction with the non-permutation letter. It is still found by small exhaustive search and has a reset word of length 2.
- The examples in the source paper are all **circular**. Section 4 assumes "circular and synchronizing", while Conjecture 5.2 (Section 5) is stated for every irreducible automaton. The binary example is **not circular**. The S_n-plus-constant example **is circular** but uses three letters. An exhaustive search of circular binary automata (a = n-cycle, any b) found no counterexample for n = 4, 5, 6, 7.
- **Recommendation:** treat this as a low-significance refutation. Submit it only if root judges the literal published conjecture worth a short certificate. A more meaningful open question, outside this record's scope, is whether Conjecture 5.2 holds for *circular binary* automata.

## Source and exact statement

- **Source:** R. Venturi, *Simplicity and irreducibility in circular automata*, arXiv:2511.16611 v2 (2026-03-26). Published in Semigroup Forum, received 2025-11-21, published 2026-08-05; doi 10.1007/s00233-026-10664-0.
- Conjecture 5.2 is unchanged in the arXiv v2 HTML and in the Springer HTML, both of which were read (receipts in sources/).
- **Conjecture 5.2:** "Let A be an irreducible automaton. Then there exists u ∈ Σ* with rk(u) = 2."
- **Rank:** rk(u) = |Q·u|.
- **Irreducible (Definition 2.1):**
  - A must be synchronizing.
  - The synchronized representation ρ : M(A)/Syn(A) → End_C(ω^⊥) must be irreducible.
  - Here ω^⊥ is the span of the vectors q_i − q_1. This is the sum-zero subspace of CQ.
  - The action is v·u = Σ v_i (q_i·u), a pushforward that preserves the coordinate sum.
  - Synchronizing words act as 0 on ω^⊥.
  - So irreducibility means that no subspace U with 0 ≠ U ≠ ω^⊥ satisfies U·u ⊆ U for every word u.
- **MathDB 371607** records the same statement. The raw line hash is in results.json.

## Counterexample B (binary, n = 5)

- **States:** Q = {0, 1, 2, 3, 4}, alphabet {a, b}, right action.
  - a = (0 1 2 3)(4), that is 0→1, 1→2, 2→3, 3→0, 4→4.
  - b: 0→0, 1→2, 2→0, 3→4, 4→0.

1. **Images.** The family 𝒮 = {Q, {0,2,4}, {1,3,4}, {0}, {1}, {2}, {3}, {4}} contains Q and is closed under both letters:
   - Q·a = Q and Q·b = {0,2,4}.
   - {0,2,4}·a = {1,3,4} and {0,2,4}·b = {0}.
   - {1,3,4}·a = {0,2,4} and {1,3,4}·b = {0,2,4}.
   - Singletons go to singletons.

   By induction on the word, Q·u ∈ 𝒮 for every u. So rk(u) ∈ {5, 3, 1}, and **no word has rank 2**. Since Q·bb = {0}, the automaton is synchronizing.
2. **Irreducibility.**
   - Use the basis v_i = q_i − q_0 (i = 1..4) of ω^⊥, and let M(u) ∈ Z^{4×4} be the matrix of ρ(u).
   - The 16 words ε, a, b, aa, ab, ba, aaa, aab, aba, baa, bab, aaab, aaba, abaa, abab, aaaba have linearly independent matrices over Q.
   - The certificate writes each elementary matrix E_ij explicitly as E_ij = Σ_k c_ijk M(u_k), with c_ijk ∈ (1/3)Z and |numerators| ≤ 4. It is in outputs/cert-371607-binary-n5.json and was checked exactly with Fractions.
   - Let U ≠ 0 be an invariant subspace and take a nonzero x ∈ U with some coordinate x_j ≠ 0.
   - For each i, the vector x·E_ji = x_j v_i (row-vector convention) is a C-linear combination of the vectors x·u_k ∈ U, so it lies in U.
   - Hence every v_i ∈ U, so U = ω^⊥, and ρ is irreducible.

So A is an irreducible automaton with no word of rank 2, which refutes Conjecture 5.2.

## Counterexample A (circular, three letters, n = 3)

- **Automaton:** Q = {0, 1, 2} with letters a = (0 1 2), b = (0 1), and c the constant map to 0.
- **Ranks:** words are permutations (rank 3) or contain c (rank 1).
- **Irreducibility:** the words ε, a, b, ab span M_2(Q) (certificate in outputs/cert-371607-S3-constant.json). Equivalently, the standard 2-dimensional representation of S_3 is irreducible over C.
- **Generalization:** for every n ≥ 3, S_n together with any constant letter gives a circular counterexample.

## Novelty and prior-art checks performed

- **Searches:**
  - Web searches on the conjecture, on irreducible automata without rank-2 words, and on Arnold–Steinberg and Rystsov irreducibility: no published counterexample found.
  - The adjacent known results are Volkov's survey statement (a primitive automaton with a rank-2 word or a defect-1 letter is synchronizing) and the Arnold–Steinberg synchronizing-groups framework. The latter makes example A essentially folklore.
- **Registries (outputs/registry-screen.json):**
  - Lean Pool HEAD 01db1d7049cf9668bda1e9e106875ee1278b43e6, full recursive tree of 25038 paths (not truncated): no automata or Černý hits. projects.yml at that sha returned 404 and was recorded.
  - Cached root Omega D5 and Problems path lists and the OpenAI listing (nanostar-parent-final-r1/registries): only unrelated hits (quantum Černý channel files, a "SparseCharacterSynchronization" file).
  - GitHub repository search, 3 queries: 0 results each.
- **Not done:** no author contact. Arnold–Steinberg 2006 and Rystsov's papers were not read in full. Root should check them for an explicit remark that irreducible automata need not have rank-2 words.

## Uncompiled Lean plan (UNCOMPILED: do not trust until root and Sol replay)

```lean
-- UNCOMPILED DRAFT, not run in this lane (Claude lane restriction).
import Mathlib

open Finset

/-- A DFA on `Fin n` with letters `Fin k`, right action. -/
structure DFA (n k : ℕ) where
  δ : Fin k → Fin n → Fin n

namespace DFA
variable {n k : ℕ} (A : DFA n k)

def act : List (Fin k) → Fin n → Fin n
  | [], q => q
  | c :: w, q => act w (A.δ c q)

def rk (w : List (Fin k)) : ℕ := (univ.image (A.act w)).card

def Synchronizing : Prop := ∃ w, A.rk w = 1

/-- pushforward action on `Fin n → ℂ`: (v·w)(q) = Σ_{p ↦ q} v p -/
def rep (w : List (Fin k)) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun v := fun q => ∑ p ∈ univ.filter (fun p => A.act w p = q), v p
  map_add' := by intro x y; ext q; simp [Finset.sum_add_distrib]
  map_smul' := by intro c x; ext q; simp [Finset.mul_sum]

/-- sum-zero subspace ω^⊥ -/
def sumZero : Submodule ℂ (Fin n → ℂ) :=
  LinearMap.ker (∑ i : Fin n, LinearMap.proj (R := ℂ) (φ := fun _ => ℂ) i)

/-- Venturi Definition 2.1 (literal): synchronizing, and every subspace of ω^⊥ that is
invariant under all words is ⊥ or all of ω^⊥. -/
def Irreducible : Prop :=
  A.Synchronizing ∧
  ∀ U : Submodule ℂ (Fin n → ℂ), U ≤ A.sumZero →
    (∀ w, ∀ x ∈ U, A.rep w x ∈ U) → U = ⊥ ∨ U = A.sumZero
end DFA

def ex : DFA 5 2 := ⟨fun c => if c = 0 then ![1, 2, 3, 0, 4] else ![0, 2, 0, 4, 0]⟩

/-- Negation of Venturi Conjecture 5.2 (MathDB 371607). -/
theorem venturi_conj_5_2_false :
    ¬ ∀ (n k : ℕ) (A : DFA n k), A.Irreducible → ∃ w, A.rk w = 2 := by
  intro h
  obtain ⟨w, hw⟩ := h 5 2 ex ex_irreducible
  exact ex_no_rank_two w hw
```

**Lemma plan:**

1. `ex_images_mem : ∀ w, univ.image (ex.act w) ∈ S`, where S is the explicit 8-element `Finset (Finset (Fin 5))`.
   - Prove it by induction on w. Write `act (w ++ [c]) = δ c ∘ act w`, or use `List.reverseRecOn`.
   - The closure step is a single `decide` over S × letters.
   - Corollary `ex_no_rank_two`: the cards of the members of S are {5, 3, 1}, by `decide`.
2. `ex_sync : ex.rk [1, 1] = 1`, by `decide`.
3. `ex_irreducible`:
   - Fix the 16 words u_k and the certificate coefficients c_ijk ∈ ℚ. To keep `decide` in ℤ, scale by 3: 3·E_ij = Σ_k (3c_ijk) M(u_k).
   - Rather than matrices, state the identity on vectors. For x in the sum-zero subspace:
     3 · x_j' · (e_i' − e_0) = Σ_k d_ijk · rep u_k x,
     where x_j' is the coordinate of x along v_j in the basis (q_j − q_0), so x_j' = x_j for j ≥ 1.
   - The identity is linear in x, so it suffices to check it on the 4 basis vectors v_1..v_4, which gives a finite ℤ-matrix check by `decide` or `norm_num [Fin.sum_univ_five]`.
   - Then the argument above finishes: if U ≠ ⊥, there is x ∈ U with some x_j ≠ 0 (j ≥ 1, since x ∈ sumZero forces x_0 = −Σ_{j≥1} x_j), so e_i − e_0 ∈ U for all i, so U ⊇ sumZero.
4. **Statement-fidelity points for review:**
   - right action and pushforward;
   - ω^⊥ is the sum-zero subspace (the source's "orthogonal" basis description);
   - "irreducible" includes the synchronizing hypothesis;
   - quantification over all alphabets and all n, matching the MathDB literal statement.

**Expected Lean cost:** small (finite decide plus about 16 linear identities over ℤ on 4×4 data), probably under a few hundred lines. The S_3 example would be even smaller (4 words, a 2×2 certificate) but is the trivial one.
