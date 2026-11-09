/-
  UNCOMPILED DRAFT  (Claude lane expanded-corpus-r135; Lean was NOT run in this lane).
  Refutation of Bang-Jensen--Bessy--Yeo Conjecture 35 (MathDB 347138):
    "There exists an integer L such that every digraph D on at least L vertices with
     lambda(D) >= 2 and alpha(D) = 2 has a non-separating out-branching B_s^+ for every
     choice of s in V."
  Endpoint: `NonSepBranching.not_conjecture35 : ¬ Conjecture35`.

  Remaining obligations are marked `sorry` with the tag OBLIGATION; each has a complete
  ordinary proof in ../PROOF.md.  An accepted certificate must contain no sorry, no
  native_decide and only the axioms propext, Classical.choice and Quot.sound.
-/
import Mathlib

namespace NonSepBranching

open Relation

/-! ## Literal definitions -/

section Defs
variable {V : Type*}

/-- Strong connectivity of the arc relation `E`. -/
def Strong (E : V → V → Prop) : Prop := ∀ u v, ReflTransGen E u v

/-- Arc deletion `D \ A(F)`. -/
def del (E F : V → V → Prop) : V → V → Prop := fun u v => E u v ∧ ¬ F u v

/-- `λ(D) ≥ 2`: strong, and strong after deleting any single arc. -/
def TwoArcStrong (E : V → V → Prop) : Prop :=
  Strong E ∧ ∀ a b, E a b → Strong (del E (fun u v => u = a ∧ v = b))

def Adj (E : V → V → Prop) (u v : V) : Prop := E u v ∨ E v u

/-- `α(D) = 2`. -/
def IndepTwo (E : V → V → Prop) : Prop :=
  (∃ u v, u ≠ v ∧ ¬ Adj E u v) ∧
  ∀ u v w, u ≠ v → v ≠ w → u ≠ w → Adj E u v ∨ Adj E v w ∨ Adj E u w

/-- `F` is (the arc set of) an out-branching of `E` rooted at `s`. -/
structure OutBranching (E : V → V → Prop) (s : V) (F : V → V → Prop) : Prop where
  sub : ∀ u v, F u v → E u v
  root : ∀ u, ¬ F u s
  unique_in : ∀ v, v ≠ s → ∃! u, F u v
  spans : ∀ v, ReflTransGen F s v

def NonSeparating (E F : V → V → Prop) : Prop := Strong (del E F)

end Defs

/-- Conjecture 35 of Bang-Jensen, Bessy and Yeo (Graphs Combin. 38 (2022) 187),
MathDB 347138, stated over all finite loopless digraphs. -/
def Conjecture35 : Prop :=
  ∃ L : ℕ, ∀ (V : Type) [Fintype V] (E : V → V → Prop),
    L ≤ Fintype.card V → (∀ v, ¬ E v v) → TwoArcStrong E → IndepTwo E →
    ∀ s : V, ∃ F : V → V → Prop, OutBranching E s F ∧ NonSeparating E F

/-! ## Generic crossing lemmas -/

/-- Last crossing from `P` to `¬P` along a path, with the suffix inside `¬P`. -/
theorem last_cross {α : Type*} {G : α → α → Prop} {P : α → Prop} {x y : α}
    (h : ReflTransGen G x y) (hx : P x) (hy : ¬ P y) :
    ∃ u v, G u v ∧ P u ∧ ¬ P v ∧
      ReflTransGen (fun a b => G a b ∧ ¬ P a ∧ ¬ P b) v y := by
  revert hy
  induction h with
  | refl => intro hy; exact absurd hx hy
  | @tail b c _ hbc ih =>
    intro hc
    by_cases hb : P b
    · exact ⟨b, c, hbc, hb, hc, ReflTransGen.refl⟩
    · obtain ⟨u, v, huv, hu, hv, hvb⟩ := ih hb
      exact ⟨u, v, huv, hu, hv, hvb.tail ⟨hbc, hb, hc⟩⟩

/-- First crossing from `¬P` to `P`, with the prefix inside `¬P`. -/
theorem first_cross {α : Type*} {G : α → α → Prop} {P : α → Prop} {x y : α}
    (h : ReflTransGen G x y) (hx : ¬ P x) (hy : P y) :
    ∃ u v, ReflTransGen (fun a b => G a b ∧ ¬ P a ∧ ¬ P b) x u ∧ G u v ∧ ¬ P u ∧ P v := by
  obtain ⟨u, v, huv, hu, hv, hvx⟩ := last_cross (G := flip G) (P := P) h.swap hy hx
  refine ⟨v, u, ?_, huv, hv, hu⟩
  -- reverse the suffix path
  have := hvx.swap
  simpa [flip, and_comm, and_left_comm, and_assoc] using this

/-! ## The gadget W1 (source Theorem 19(b), Figure 3) -/

/-- Arcs of W1 on `Fin 4` (p1,p2,p3,p4 = 0,1,2,3): Hamiltonian cycle 0→1→2→3→0,
chord 0→2 and the 2-cycle 1↔3. Encoded as a Bool table for kernel `decide`. -/
def w1 : Fin 4 → Fin 4 → Bool := fun p q =>
  (p.val, q.val) ∈ [(0,1),(1,2),(2,3),(3,0),(0,2),(1,3),(3,1)]

def W1 (p q : Fin 4) : Prop := w1 p q = true

instance : DecidableRel W1 := fun p q => inferInstanceAs (Decidable (w1 p q = true))

/-! ### Finite reachability on `Fin 4` with Bool relations -/

/-- One closure step of the reachable set. -/
def stepB (r : Fin 4 → Fin 4 → Bool) (X : Fin 4 → Bool) : Fin 4 → Bool :=
  fun b => X b || (X 0 && r 0 b) || (X 1 && r 1 b) || (X 2 && r 2 b) || (X 3 && r 3 b)

def reachB (r : Fin 4 → Fin 4 → Bool) (a : Fin 4) : Fin 4 → Bool :=
  stepB r (stepB r (stepB r (stepB r (fun b => decide (b = a)))))

/-- Sub-relations of W1 indexed by their characteristic vector on the 7 arcs. -/
def arcList : List (Fin 4 × Fin 4) := [(0,1),(1,2),(2,3),(3,0),(0,2),(1,3),(3,1)]

def subRel (c : Fin 7 → Bool) : Fin 4 → Fin 4 → Bool := fun p q =>
  (List.finRange 7).any (fun i => c i && decide (arcList.get ⟨i.val, by simp [arcList]⟩ = (p, q)))

def compRel (c : Fin 7 → Bool) : Fin 4 → Fin 4 → Bool := fun p q => w1 p q && !(subRel c p q)

/-- Closure of `reachB` (checked by `decide` over all 128 sub-relations and the
complement relations). -/
theorem reachB_closed :
    ∀ c : Fin 7 → Bool, ∀ a x y : Fin 4,
      (reachB (subRel c) a x = true → subRel c x y = true → reachB (subRel c) a y = true) ∧
      (reachB (compRel c) a x = true → compRel c x y = true → reachB (compRel c) a y = true) := by
  decide

/-- The finite heart of the refutation (both cases of PROOF.md §5 Step 4), by `decide`. -/
theorem w1_finite :
    ∀ c : Fin 7 → Bool,
      ((∀ q, reachB (subRel c) 0 q = true) →
        ¬ ((∀ q, reachB (compRel c) 2 q = true) ∧ (∀ q, reachB (fun x y => compRel c y x) 2 q = true))) ∧
      ((∀ q, reachB (subRel c) 2 q = true) →
        ¬ ((∀ q, reachB (compRel c) 0 q = true) ∧ (∀ q, reachB (fun x y => compRel c y x) 2 q = true))) := by
  decide
  -- OBLIGATION (compile-time): the reversed relation also needs a closure lemma like
  -- `reachB_closed`; add it to the same `decide` if needed.

/-- Bridge: reachability along a Prop relation contained in a Bool relation lands in `reachB`.
OBLIGATION: induction on `ReflTransGen` using a closure lemma of `reachB` for `r`. -/
theorem rtg_to_reachB (r : Fin 4 → Fin 4 → Bool)
    (hclosed : ∀ a x y, reachB r a x = true → r x y = true → reachB r a y = true)
    {R : Fin 4 → Fin 4 → Prop} (hR : ∀ x y, R x y → r x y = true) {a b : Fin 4}
    (h : ReflTransGen R a b) : reachB r a b = true := by
  induction h with
  | refl =>
    -- `a` is in the initial set and `stepB` is inflationary
    simp [reachB, stepB]
  | tail _ hbc ih => exact hclosed _ _ _ ih (hR _ _ hbc)

/-! ## The family `D_m`, `m = k + 3` -/

abbrev Vm (k : ℕ) := Fin (k + 3) ⊕ Fin 4

/-- Arc relation of `D_m`: complete digraph on A, W1 on B, entries a₀→p1, a₁→p3,
exits p3→a₀, p3→a_last. -/
def Em (k : ℕ) : Vm k → Vm k → Prop
  | .inl i, .inl j => i ≠ j
  | .inr p, .inr q => W1 p q
  | .inl i, .inr q => (i = 0 ∧ q = 0) ∨ (i = 1 ∧ q = 2)
  | .inr p, .inl j => p = 2 ∧ (j = 0 ∨ j = Fin.last (k + 2))

theorem card_Vm (k : ℕ) : Fintype.card (Vm k) = k + 7 := by
  simp [Vm]; omega

theorem irrefl_Em (k : ℕ) : ∀ v : Vm k, ¬ Em k v v := by
  rintro (i | p)
  · simp [Em]
  · revert p; decide

theorem w1_semicomplete : ∀ p q : Fin 4, p ≠ q → W1 p q ∨ W1 q p := by decide

theorem indepTwo_Em (k : ℕ) : IndepTwo (Em k) := by
  refine ⟨⟨.inl 0, .inr 1, by simp, ?_⟩, ?_⟩
  · simp [Adj, Em]
  · -- pigeonhole: two of three vertices lie on the same side, and both sides are cliques
    intro u v w huv hvw huw
    rcases u with i | p <;> rcases v with j | q <;> rcases w with l | r <;>
      first
      | (left; left; simpa [Em] using huv)
      | (right; left; simpa [Em] using hvw)
      | (right; right; left; simpa [Em] using huw)
      | skip
    -- OBLIGATION: the B-side cases via `w1_semicomplete`; mixed cases pick the same-side pair.
    all_goals sorry

/-- `λ(D_m) ≥ 2`.  OBLIGATION (longest part): PROOF.md Lemma 2.  Suggested route:
(a) A is strongly connected after deleting any one arc (third vertex, m ≥ 3);
(b) contract A and check the 5-vertex quotient with two parallel exits by `decide`;
or prove the cut criterion and use the finite cut table of `gadget_certificate.py` (C3). -/
theorem twoArcStrong_Em (k : ℕ) : TwoArcStrong (Em k) := by
  sorry

/-! ## Main gluing argument -/

/-- Side predicate: the A side. -/
def isA {k : ℕ} (v : Vm k) : Prop := v.isLeft = true

/-- Paths inside B project to paths of the restricted relation on `Fin 4`. -/
theorem toB {k : ℕ} {R : Vm k → Vm k → Prop} {p : Fin 4} {y : Vm k}
    (h : ReflTransGen (fun a b => R a b ∧ ¬ isA a ∧ ¬ isA b) (.inr p) y) :
    ∀ q, y = .inr q → ReflTransGen (fun x z => R (.inr x) (.inr z)) p q := by
  induction h with
  | refl => intro q hq; cases hq; exact ReflTransGen.refl
  | @tail b c _ hbc ih =>
    intro q hq
    subst hq
    rcases b with b | b
    · exact absurd rfl hbc.2.1
    · exact (ih b rfl).tail hbc.1

theorem not_nonsep (k : ℕ) (F : Vm k → Vm k → Prop)
    (hF : OutBranching (Em k) (.inl 0) F) (hR : NonSeparating (Em k) F) : False := by
  classical
  set R := del (Em k) F with hRdef
  -- Step 1: F contains an entry; R contains an entry.
  have entryF : F (.inl 0) (.inr 0) ∨ F (.inl 1) (.inr 2) := by
    obtain ⟨u, v, huv, hu, hv, -⟩ :=
      last_cross (P := isA) (hF.spans (.inr 0)) (by simp [isA]) (by simp [isA])
    rcases u with i | p
    · rcases v with j | q
      · simp [isA] at hv
      · have := hF.sub _ _ huv
        rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl huv
        · exact Or.inr huv
    · simp [isA] at hu
  have entryR : ¬ F (.inl 0) (.inr 0) ∨ ¬ F (.inl 1) (.inr 2) := by
    obtain ⟨u, v, huv, hu, hv, -⟩ :=
      last_cross (P := isA) (hR (.inl 0) (.inr 0)) (by simp [isA]) (by simp [isA])
    rcases u with i | p
    · rcases v with j | q
      · simp [isA] at hv
      · rcases huv.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl huv.2
        · exact Or.inr huv.2
    · simp [isA] at hu
  -- Restricted relations on B.
  let T : Fin 4 → Fin 4 → Prop := fun p q => F (.inr p) (.inr q)
  let RB : Fin 4 → Fin 4 → Prop := fun p q => R (.inr p) (.inr q)
  have hT : ∀ p q, T p q → W1 p q := fun p q h => hF.sub _ _ h
  have hRB : ∀ p q, RB p q ↔ W1 p q ∧ ¬ T p q := fun p q => Iff.rfl
  -- Step 2: the F-entry head reaches all of B inside T.
  have Treach : ∀ e, (∀ i q, F (.inl i) (.inr q) → q = e) → ∀ q, ReflTransGen T e q := by
    intro e he q
    obtain ⟨u, v, huv, hu, hv, hpath⟩ :=
      last_cross (P := isA) (hF.spans (.inr q)) (by simp [isA]) (by simp [isA])
    rcases u with i | p
    · rcases v with j | q'
      · simp [isA] at hv
      · have := he i q' huv; subst this; exact toB hpath q rfl
    · simp [isA] at hu
  -- Step 3: R-entry head reaches all of B in RB; all of B reaches p3 (= 2) in RB.
  have Rreach : ∀ e', (∀ i q, R (.inl i) (.inr q) → q = e') → ∀ q, ReflTransGen RB e' q := by
    intro e' he q
    obtain ⟨u, v, huv, hu, hv, hpath⟩ :=
      last_cross (P := isA) (hR (.inl 0) (.inr q)) (by simp [isA]) (by simp [isA])
    rcases u with i | p
    · rcases v with j | q'
      · simp [isA] at hv
      · have := he i q' huv; subst this; exact toB hpath q rfl
    · simp [isA] at hu
  have Rback : ∀ q, ReflTransGen RB q 2 := by
    intro q
    obtain ⟨u, v, hpath, huv, hu, hv⟩ :=
      first_cross (P := isA) (hR (.inr q) (.inl 0)) (by simp [isA]) (by simp [isA])
    rcases u with i | p
    · simp [isA] at hu
    · rcases v with j | j
      · have h2 : p = 2 := huv.1.1
        subst h2; exact toB hpath 2 rfl
      · simp [isA] at hv
  -- Step 4: case split and finite contradiction.
  -- OBLIGATION: package T (resp. RB) as `subRel c` (resp. `compRel c`) with
  --   c i := decide (T (arcList.get i).1 (arcList.get i).2)  (classical),
  -- transfer `Treach`, `Rreach`, `Rback` through `rtg_to_reachB` and `reachB_closed`,
  -- and conclude with `w1_finite`.
  rcases entryF with h0 | h1
  · have hn1 : ¬ F (.inl 1) (.inr 2) := by
      rcases entryR with h | h
      · exact absurd h0 h
      · exact h
    have tT := Treach 0 (by
      intro i q h
      rcases hF.sub _ _ h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact absurd h hn1)
    have tR := Rreach 2 (by
      intro i q h
      rcases h.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd h0 h.2
      · rfl)
    sorry -- OBLIGATION: finite contradiction (case e = p1), see comment above.
  · have hn0 : ¬ F (.inl 0) (.inr 0) := by
      rcases entryR with h | h
      · exact h
      · exact absurd h1 h
    have tT := Treach 2 (by
      intro i q h
      rcases hF.sub _ _ h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd h hn0
      · rfl)
    have tR := Rreach 0 (by
      intro i q h
      rcases h.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact absurd h1 h.2)
    sorry -- OBLIGATION: finite contradiction (case e = p3), see comment above.

/-! ## Endpoint -/

theorem not_conjecture35 : ¬ Conjecture35 := by
  rintro ⟨L, hL⟩
  obtain ⟨F, hF, hns⟩ :=
    hL (Vm L) (Em L) (by rw [card_Vm]; omega) (irrefl_Em L) (twoArcStrong_Em L)
      (indepTwo_Em L) (.inl 0)
  exact not_nonsep L F hF hns

end NonSepBranching
