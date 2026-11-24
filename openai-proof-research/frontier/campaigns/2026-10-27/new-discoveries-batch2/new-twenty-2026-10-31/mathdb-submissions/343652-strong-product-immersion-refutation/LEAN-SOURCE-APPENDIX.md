# Lean source appendix

Modules follow in import order. Each fenced body is byte-identical to its file in src/.

### `ImmersionCore.lean`

```lean
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Lean.Elab.Tactic.Omega

namespace ProductImmersion

-- An ordinary weak clique immersion, with simple finite vertex sequences.
-- Both orientations are supplied; opposite orientations may use the same edges.
structure CliqueImmersion {V : Type} (G : SimpleGraph V) (q : ℕ) where
  branch : Fin q → V
  injective : Function.Injective branch
  len : Fin q → Fin q → ℕ
  vertex : Fin q → Fin q → ℕ → V
  start : ∀ i j, vertex i j 0 = branch i
  finish : ∀ i j, vertex i j (len i j) = branch j
  adjacent : ∀ i j, i ≠ j → ∀ a : Fin (len i j),
    G.Adj (vertex i j a) (vertex i j (a.val + 1))
  simple : ∀ i j, i ≠ j → ∀ a b : Fin (len i j + 1),
    vertex i j a = vertex i j b → a = b
  disjoint : ∀ i j, i ≠ j → ∀ k l, k ≠ l →
    ∀ a : Fin (len i j), ∀ b : Fin (len k l),
    ((vertex i j a = vertex k l b ∧
      vertex i j (a.val+1) = vertex k l (b.val+1)) ∨
     (vertex i j a = vertex k l (b.val+1) ∧
      vertex i j (a.val+1) = vertex k l b)) →
    ((i = k ∧ j = l) ∨ (i = l ∧ j = k))

variable {V : Type} {G : SimpleGraph V} {q : ℕ}

lemma CliqueImmersion.len_pos (I : CliqueImmersion G q) (i j : Fin q) (h : i ≠ j) :
    0 < I.len i j := by
  by_contra hh
  have hz : I.len i j = 0 := by omega
  have he := I.finish i j
  rw [hz, I.start] at he
  exact h (I.injective he)

lemma exists_crossing (f : ℕ → V) (side : V → Bool) (n : ℕ)
    (h : side (f 0) ≠ side (f n)) :
    ∃ a, a < n ∧ side (f a) ≠ side (f (a+1)) := by
  induction n with
  | zero => exact (h rfl).elim
  | succ n ih =>
    by_cases he : side (f 0) = side (f n)
    · exact ⟨n, Nat.lt_succ_self n, by simpa [← he] using h⟩
    · obtain ⟨a, ha, hc⟩ := ih he
      exact ⟨a, Nat.lt_trans ha (Nat.lt_succ_self n), hc⟩

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

def degree (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  (Finset.univ.filter (G.Adj v)).card

omit [DecidableEq V] in
lemma CliqueImmersion.degree_bound (I : CliqueImmersion G q) (i : Fin q) :
    q - 1 ≤ degree G (I.branch i) := by
  classical
  let D := {j : Fin q // j ≠ i}
  let N := {v : V // G.Adj (I.branch i) v}
  let f : D → N := fun j =>
    ⟨I.vertex i j.val 1, by
      have h := I.adjacent i j.val (Ne.symm j.property) ⟨0, I.len_pos i j.val (Ne.symm j.property)⟩
      simpa only [Nat.zero_add, I.start] using h⟩
  have hf : Function.Injective f := by
    intro j k he
    have hv : I.vertex i j.val 1 = I.vertex i k.val 1 := congrArg Subtype.val he
    have hd := I.disjoint i j.val (Ne.symm j.property) i k.val (Ne.symm k.property)
      ⟨0, I.len_pos i j.val (Ne.symm j.property)⟩
      ⟨0, I.len_pos i k.val (Ne.symm k.property)⟩ (Or.inl ⟨by simp [I.start], hv⟩)
    rcases hd with ⟨_, hj⟩ | ⟨_, hj⟩
    · exact Subtype.ext hj
    · exact (j.property hj).elim
  have hc := Fintype.card_le_of_injective f hf
  have hD : Fintype.card D = q - 1 := by
    dsimp [D]
    rw [Fintype.card_subtype_compl]
    simp
  have hN : Fintype.card N = degree G (I.branch i) := by
    exact Fintype.card_subtype _
  rw [hD, hN] at hc
  exact hc


abbrev CutEdge (G : SimpleGraph V) (side : V → Bool) :=
  {e : V × V // G.Adj e.1 e.2 ∧ side e.1 = false ∧ side e.2 = true}

abbrev CrossPair (I : CliqueImmersion G q) (side : V → Bool) :=
  {i : Fin q // side (I.branch i) = false} ×
  {j : Fin q // side (I.branch j) = true}

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma CliqueImmersion.cross_ne (I : CliqueImmersion G q) (side : V → Bool)
    (d : CrossPair I side) : d.1.val ≠ d.2.val := by
  intro he
  have h0 := d.1.property
  have h1 := d.2.property
  rw [he, h1] at h0
  contradiction

lemma CliqueImmersion.cross_edge (I : CliqueImmersion G q) (side : V → Bool)
    (d : CrossPair I side) :
    ∃ e : CutEdge G side, ∃ a : Fin (I.len d.1.val d.2.val),
      e.val = (I.vertex d.1.val d.2.val a,
        I.vertex d.1.val d.2.val (a.val+1)) ∨
      e.val = (I.vertex d.1.val d.2.val (a.val+1),
        I.vertex d.1.val d.2.val a) := by
  have hc : side (I.vertex d.1.val d.2.val 0) ≠
      side (I.vertex d.1.val d.2.val (I.len d.1.val d.2.val)) := by
    rw [I.start, I.finish, d.1.property, d.2.property]
    decide
  obtain ⟨a, ha, hd⟩ := exists_crossing _ side _ hc
  have hadj := I.adjacent d.1.val d.2.val (I.cross_ne side d) ⟨a,ha⟩
  cases h0 : side (I.vertex d.1.val d.2.val a) with
  | false =>
    have h1 : side (I.vertex d.1.val d.2.val (a+1)) = true := by
      cases hx : side (I.vertex d.1.val d.2.val (a+1)) <;> simp_all
    exact ⟨⟨(_, _), hadj, h0, h1⟩, ⟨a,ha⟩, Or.inl rfl⟩
  | true =>
    have h1 : side (I.vertex d.1.val d.2.val (a+1)) = false := by
      cases hx : side (I.vertex d.1.val d.2.val (a+1)) <;> simp_all
    exact ⟨⟨(_, _), hadj.symm, h1, h0⟩, ⟨a,ha⟩, Or.inr rfl⟩

lemma CliqueImmersion.cut_bound (I : CliqueImmersion G q) (side : V → Bool) :
    Fintype.card (CrossPair I side) ≤ Fintype.card (CutEdge G side) := by
  classical
  let f : CrossPair I side → CutEdge G side :=
    fun d => Classical.choose (I.cross_edge side d)
  have hf (d : CrossPair I side) := Classical.choose_spec (I.cross_edge side d)
  have hinj : Function.Injective f := by
    intro d e he
    obtain ⟨a, ha⟩ := hf d
    obtain ⟨b, hb⟩ := hf e
    have hv : (f d).val = (f e).val := congrArg Subtype.val he
    have heq :
        ((I.vertex d.1.val d.2.val a = I.vertex e.1.val e.2.val b ∧
          I.vertex d.1.val d.2.val (a.val+1) = I.vertex e.1.val e.2.val (b.val+1)) ∨
         (I.vertex d.1.val d.2.val a = I.vertex e.1.val e.2.val (b.val+1) ∧
          I.vertex d.1.val d.2.val (a.val+1) = I.vertex e.1.val e.2.val b)) := by
      change (f d).val = _ ∨ (f d).val = _ at ha
      change (f e).val = _ ∨ (f e).val = _ at hb
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · rw [ha, hb] at hv
        exact Or.inl (Prod.mk.inj hv)
      · rw [ha, hb] at hv
        exact Or.inr (Prod.mk.inj hv)
      · rw [ha, hb] at hv
        exact Or.inr ⟨(Prod.mk.inj hv).2, (Prod.mk.inj hv).1⟩
      · rw [ha, hb] at hv
        exact Or.inl ⟨(Prod.mk.inj hv).2, (Prod.mk.inj hv).1⟩
    have hd := I.disjoint d.1.val d.2.val (I.cross_ne side d)
      e.1.val e.2.val (I.cross_ne side e) a b heq
    rcases hd with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
    · have h0 := d.1.property
      rw [h1, e.2.property] at h0
      contradiction
  exact Fintype.card_le_of_injective f hinj

#print axioms CliqueImmersion.degree_bound
#print axioms CliqueImmersion.cut_bound
end ProductImmersion
```

### `ImmersionNumber.lean`

```lean
import ImmersionCore
import Mathlib.Data.Nat.Find

namespace ProductImmersion
variable {V : Type} {G : SimpleGraph V} {q r : ℕ}

def CliqueImmersion.restrict (I : CliqueImmersion G q) (f : Fin r ↪ Fin q) :
    CliqueImmersion G r where
  branch i := I.branch (f i)
  injective := I.injective.comp f.injective
  len i j := I.len (f i) (f j)
  vertex i j := I.vertex (f i) (f j)
  start i j := I.start (f i) (f j)
  finish i j := I.finish (f i) (f j)
  adjacent i j hij := I.adjacent (f i) (f j) (fun he => hij (f.injective he))
  simple i j hij := I.simple (f i) (f j) (fun he => hij (f.injective he))
  disjoint := by
    intro i j hij k l hkl a b he
    have h := I.disjoint (f i) (f j) (fun he => hij (f.injective he))
      (f k) (f l) (fun he => hkl (f.injective he)) a b he
    rcases h with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact Or.inl ⟨f.injective h1, f.injective h2⟩
    · exact Or.inr ⟨f.injective h1, f.injective h2⟩

def finEmbeddingLE (hrq : r ≤ q) : Fin r ↪ Fin q where
  toFun i := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hrq⟩
  inj' := by
    intro i j he
    exact Fin.ext (congrArg (fun x : Fin q => x.val) he)

lemma exists_immersion_mono (hrq : r ≤ q) (h : Nonempty (CliqueImmersion G q)) :
    Nonempty (CliqueImmersion G r) := by
  obtain ⟨I⟩ := h
  exact ⟨I.restrict (finEmbeddingLE hrq)⟩

variable [Fintype V]

lemma CliqueImmersion.card_bound (I : CliqueImmersion G q) : q ≤ Fintype.card V := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective I.branch I.injective

noncomputable def immersionNumber (G : SimpleGraph V) : ℕ := by
  classical
  exact Nat.findGreatest (fun q => Nonempty (CliqueImmersion G q)) (Fintype.card V)

lemma immersionNumber_is_largest (q : ℕ) (hq : Nonempty (CliqueImmersion G q)) :
    q ≤ immersionNumber G := by
  classical
  by_contra h
  have hlt : immersionNumber G < q := by omega
  have hcard : q ≤ Fintype.card V := hq.elim (fun I => I.card_bound)
  exact (Nat.findGreatest_is_greatest hlt hcard) hq

lemma immersionNumber_eq (q : ℕ) (hqcard : q ≤ Fintype.card V)
    (hq : Nonempty (CliqueImmersion G q))
    (hnext : ¬ Nonempty (CliqueImmersion G (q+1))) :
    immersionNumber G = q := by
  classical
  unfold immersionNumber
  apply Nat.findGreatest_eq_iff.mpr
  refine ⟨hqcard, fun _ => hq, ?_⟩
  intro n hqn _ hn
  exact hnext (exists_immersion_mono (by omega) hn)

lemma immersionNumber_lt (q : ℕ) (hq : 0 < q)
    (hno : ¬ Nonempty (CliqueImmersion G q)) : immersionNumber G < q := by
  classical
  by_contra h
  have hqmax : q ≤ immersionNumber G := by omega
  have hnz : immersionNumber G ≠ 0 := by omega
  have hm : Nonempty (CliqueImmersion G (immersionNumber G)) := by
    exact Nat.findGreatest_of_ne_zero rfl hnz
  exact hno (exists_immersion_mono hqmax hm)

#print axioms immersionNumber_eq
#print axioms immersionNumber_lt
end ProductImmersion
```

### `FactorDefinitions.lean`

```lean
import ImmersionCore

namespace ProductImmersion

def factorAdj (a : ℕ) (x y : ℕ) : Prop :=
  (x < a ∧ a ≤ y ∧ y < 3*a-1) ∨
  (y < a ∧ a ≤ x ∧ x < 3*a-1) ∨
  (a ≤ x ∧ x < 2*a ∧ 3*a-1 ≤ y) ∨
  (a ≤ y ∧ y < 2*a ∧ 3*a-1 ≤ x)

instance (a x y : ℕ) : Decidable (factorAdj a x y) := inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

def factor (a n : ℕ) : SimpleGraph (Fin n) where
  Adj x y := factorAdj a x.val y.val
  symm := ⟨by
    intro x y h
    rcases h with h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))⟩
  loopless := ⟨by
    intro x h
    rcases h with h | h | h | h <;> omega⟩

abbrev G := factor 4 14
abbrev H := factor 6 22
instance : DecidableRel G.Adj := fun x y => inferInstanceAs (Decidable (factorAdj 4 x.val y.val))
instance : DecidableRel H.Adj := fun x y => inferInstanceAs (Decidable (factorAdj 6 x.val y.val))

def strongProduct {V W : Type} (A : SimpleGraph V) (B : SimpleGraph W) :
    SimpleGraph (V × W) where
  Adj x y := (x.1 = y.1 ∧ B.Adj x.2 y.2) ∨
    (x.2 = y.2 ∧ A.Adj x.1 y.1) ∨
    (A.Adj x.1 y.1 ∧ B.Adj x.2 y.2)
  symm := ⟨by
    intro x y h
    rcases h with h | h | h
    · exact Or.inl ⟨h.1.symm, h.2.symm⟩
    · exact Or.inr (Or.inl ⟨h.1.symm, h.2.symm⟩)
    · exact Or.inr (Or.inr ⟨h.1.symm, h.2.symm⟩)⟩
  loopless := ⟨by
    intro x h
    rcases h with h | h | h
    · exact B.irrefl h.2
    · exact A.irrefl h.2
    · exact A.irrefl h.1⟩

abbrev P := strongProduct G H

def peg (a i j : ℕ) : ℕ :=
  if i = a-1 then j else if j = a-1 then i else ((a/2)*(i+j)) % (a-1)

def branchG (i : Fin 8) : Fin 14 := ⟨i.val, by omega⟩
def branchH (i : Fin 12) : Fin 22 := ⟨i.val, by omega⟩

def pathLen (a i j : ℕ) : ℕ := if i = j then 0 else if (i < a) = (j < a) then 2 else 1

def pathVal (a i j k : ℕ) : ℕ :=
  if k = 0 then i else
  if k = 1 ∧ (i < a) = (j < a) ∧ i ≠ j then
    2*a + (if i < a then 0 else a-1) + peg a (i%a) (j%a)
  else j

def vertexG (i j : Fin 8) (k : ℕ) : Fin 14 :=
  ⟨pathVal 4 i j k % 14, Nat.mod_lt _ (by decide)⟩
def vertexH (i j : Fin 12) (k : ℕ) : Fin 22 :=
  ⟨pathVal 6 i j k % 22, Nat.mod_lt _ (by decide)⟩


lemma degreeG : ∀ v : Fin 14, degree G v ≤ 7 := by decide
lemma degreeH : ∀ v : Fin 22, degree H v ≤ 11 := by decide

#print axioms degreeG
#print axioms degreeH
end ProductImmersion
```

### `FactorOwners.lean`

```lean
import FactorDefinitions
namespace ProductImmersion

def targetKey (i j : ℕ) : ℕ × ℕ := (min i j, max i j)
def partner (a i c : ℕ) : ℕ :=
  if i = a-1 then c else if i = c then a-1 else (2*c+(a-1)-i) % (a-1)
def edgeOwnerOrdered (a x y : ℕ) : ℕ × ℕ :=
  if y < 2*a then targetKey x y else
    let c := y - (if x < a then 2*a else 3*a-1)
    let z := partner a (x%a) c + (if x < a then 0 else a)
    targetKey x z
def edgeOwner (a x y : ℕ) : ℕ × ℕ := edgeOwnerOrdered a (min x y) (max x y)

lemma edgeOwner_symm (a x y : ℕ) : edgeOwner a x y = edgeOwner a y x := by
  simp only [edgeOwner, min_comm x y, max_comm x y]

lemma targetKey_inj (i j k l : ℕ) (he : targetKey i j = targetKey k l) :
    (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  dsimp [targetKey] at h1 h2
  omega

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
lemma ownerG : ∀ (i j : Fin 8), i ≠ j → ∀ k : Fin (pathLen 4 i j),
    edgeOwner 4 (vertexG i j k).val (vertexG i j (k.val+1)).val = targetKey i.val j.val := by
  decide
lemma ownerH : ∀ (i j : Fin 12), i ≠ j → ∀ k : Fin (pathLen 6 i j),
    edgeOwner 6 (vertexH i j k).val (vertexH i j (k.val+1)).val = targetKey i.val j.val := by
  decide

lemma disjoint_from_owner {n q : ℕ}
    (v : Fin q → Fin q → ℕ → Fin n) (len : Fin q → Fin q → ℕ)
    (owner : Fin n → Fin n → ℕ × ℕ)
    (hsymm : ∀ x y, owner x y = owner y x)
    (recover : ∀ i j, i ≠ j → ∀ a : Fin (len i j),
      owner (v i j a) (v i j (a.val+1)) = targetKey i.val j.val) :
    ∀ i j, i ≠ j → ∀ k l, k ≠ l →
      ∀ a : Fin (len i j), ∀ b : Fin (len k l),
      ((v i j a = v k l b ∧ v i j (a.val+1) = v k l (b.val+1)) ∨
       (v i j a = v k l (b.val+1) ∧ v i j (a.val+1) = v k l b)) →
      ((i = k ∧ j = l) ∨ (i = l ∧ j = k)) := by
  intro i j hij k l hkl a b he
  have hkey : targetKey i.val j.val = targetKey k.val l.val := by
    rw [← recover i j hij a, ← recover k l hkl b]
    rcases he with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · rw [h1,h2]
    · rw [h1,h2,hsymm]
  rcases targetKey_inj _ _ _ _ hkey with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact Or.inl ⟨Fin.ext h1, Fin.ext h2⟩
  · exact Or.inr ⟨Fin.ext h1, Fin.ext h2⟩

#print axioms ownerG
#print axioms ownerH
#print axioms disjoint_from_owner
end ProductImmersion
```

### `FactorImmersions.lean`

```lean
import FactorOwners
namespace ProductImmersion
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def immersionG : CliqueImmersion G 8 where
  branch := branchG
  injective := by intro i j h; exact Fin.ext (congrArg (fun x : Fin 14 => x.val) h)
  len i j := pathLen 4 i j
  vertex := vertexG
  start := by decide
  finish := by decide
  adjacent := by decide
  simple := by decide
  disjoint := disjoint_from_owner vertexG (fun i j => pathLen 4 i j)
    (fun x y => edgeOwner 4 x.val y.val) (fun x y => edgeOwner_symm 4 x.val y.val) ownerG

#check immersionG

def immersionH : CliqueImmersion H 12 where
  branch := branchH
  injective := by intro i j h; exact Fin.ext (congrArg (fun x : Fin 22 => x.val) h)
  len i j := pathLen 6 i j
  vertex := vertexH
  start := by decide
  finish := by decide
  adjacent := by decide
  simple := by decide
  disjoint := disjoint_from_owner vertexH (fun i j => pathLen 6 i j)
    (fun x y => edgeOwner 6 x.val y.val) (fun x y => edgeOwner_symm 6 x.val y.val) ownerH

#check immersionH

lemma no_immersionG : ¬ Nonempty (CliqueImmersion G 9) := by
  rintro ⟨I⟩
  have h := I.degree_bound 0
  have hh := degreeG (I.branch 0)
  omega
lemma no_immersionH : ¬ Nonempty (CliqueImmersion H 13) := by
  rintro ⟨I⟩
  have h := I.degree_bound 0
  have hh := degreeH (I.branch 0)
  omega


#print axioms immersionG
#print axioms immersionH
end ProductImmersion
```

### `ProductDegree.lean`

```lean
import FactorDefinitions
namespace ProductImmersion

instance strongProductDecidable {V W : Type} [DecidableEq V] [DecidableEq W]
    (A : SimpleGraph V) (B : SimpleGraph W) [DecidableRel A.Adj] [DecidableRel B.Adj] :
    DecidableRel (strongProduct A B).Adj :=
  fun _x _y => inferInstanceAs (Decidable (_ ∨ _ ∨ _))

variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (A : SimpleGraph V) (B : SimpleGraph W) [DecidableRel A.Adj] [DecidableRel B.Adj]

def closedN (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset V :=
  insert v (Finset.univ.filter (G.Adj v))

lemma closedN_card (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (closedN G v).card = degree G v + 1 := by
  have hn : v ∉ Finset.univ.filter (G.Adj v) := by simp
  simpa only [closedN, degree] using Finset.card_insert_of_notMem hn

lemma closedN_product (g : V) (h : W) :
    closedN (strongProduct A B) (g,h) = (closedN A g).product (closedN B h) := by
  ext ⟨u,v⟩
  simp only [Finset.product_eq_sprod, closedN, Finset.mem_product,
    Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
  change ((u,v) = (g,h) ∨
    (g = u ∧ B.Adj h v) ∨ (h = v ∧ A.Adj g u) ∨ (A.Adj g u ∧ B.Adj h v)) ↔
    ((u = g ∨ A.Adj g u) ∧ (v = h ∨ B.Adj h v))
  simp only [Prod.mk.injEq]
  aesop

lemma product_degree (g : V) (h : W) :
    degree (strongProduct A B) (g,h) + 1 = (degree A g + 1) * (degree B h + 1) := by
  have hc := congrArg Finset.card (closedN_product A B g h)
  simpa only [Finset.product_eq_sprod, Finset.card_product, closedN_card] using hc

lemma degreeG_exact : ∀ v : Fin 14, degree G v = if v.val < 8 then 7 else 4 := by decide
lemma degreeH_exact : ∀ v : Fin 22, degree H v = if v.val < 12 then 11 else 6 := by decide

lemma degree_eligible : ∀ v : Fin 14 × Fin 22,
    95 ≤ degree P v → v.1.val < 8 ∧ v.2.val < 12 := by
  intro ⟨g,h⟩ hd
  change g.val < 8 ∧ h.val < 12
  have he : degree P (g,h) + 1 = (degree G g + 1) * (degree H h + 1) :=
    product_degree G H g h
  rw [degreeG_exact, degreeH_exact] at he
  split_ifs at he <;> omega

#print axioms product_degree
#print axioms degree_eligible
end ProductImmersion
```

### `ProductCut.lean`

```lean
import ProductDegree
import Mathlib.Data.Fintype.Sum

namespace ProductImmersion
variable {V W : Type} (A : SimpleGraph V) (B : SimpleGraph W)
    (a : V → Bool) (b : W → Bool)

def productSide (v : V × W) : Bool := xor (a v.1) (b v.2)

lemma xor_both_flip (x x' y y' : Bool) (hx : x ≠ x') (hy : y ≠ y') :
    xor x y = xor x' y' := by
  cases x <;> cases x' <;> cases y <;> cases y' <;> simp_all

def horizontalCut (e : CutEdge A a) (h : W) :
    CutEdge (strongProduct A B) (productSide a b) := by
  by_cases hh : b h = false
  · exact ⟨((e.val.1,h),(e.val.2,h)), Or.inr (Or.inl ⟨rfl,e.property.1⟩),
      by simp only [productSide,e.property.2.1,hh]; rfl,
      by simp only [productSide,e.property.2.2,hh]; rfl⟩
  · have ht : b h = true := by cases he : b h <;> simp_all
    exact ⟨((e.val.2,h),(e.val.1,h)), Or.inr (Or.inl ⟨rfl,e.property.1.symm⟩),
      by simp only [productSide,e.property.2.2,ht]; rfl,
      by simp only [productSide,e.property.2.1,ht]; rfl⟩

def verticalCut (g : V) (e : CutEdge B b) :
    CutEdge (strongProduct A B) (productSide a b) := by
  by_cases hg : a g = false
  · exact ⟨((g,e.val.1),(g,e.val.2)), Or.inl ⟨rfl,e.property.1⟩,
      by simp only [productSide,hg,e.property.2.1]; rfl,
      by simp only [productSide,hg,e.property.2.2]; rfl⟩
  · have ht : a g = true := by cases he : a g <;> simp_all
    exact ⟨((g,e.val.2),(g,e.val.1)), Or.inl ⟨rfl,e.property.1.symm⟩,
      by simp only [productSide,ht,e.property.2.2]; rfl,
      by simp only [productSide,ht,e.property.2.1]; rfl⟩

abbrev CutSource := (CutEdge A a × W) ⊕ (V × CutEdge B b)
def cutCover : CutSource A B a b → CutEdge (strongProduct A B) (productSide a b) :=
  Sum.elim (fun x => horizontalCut A B a b x.1 x.2)
    (fun x => verticalCut A B a b x.1 x.2)

lemma cutCover_surjective
    (ha : ∀ u v, A.Adj u v → a u ≠ a v)
    (hb : ∀ u v, B.Adj u v → b u ≠ b v) :
    Function.Surjective (cutCover A B a b) := by
  rintro ⟨⟨⟨g,h⟩,⟨g',h'⟩⟩, hadj,h0,h1⟩
  change xor (a g) (b h) = false at h0
  change xor (a g') (b h') = true at h1
  rcases hadj with ⟨hgg,hadj⟩ | ⟨hhh,hadj⟩ | ⟨hadjA,hadjB⟩
  · change g = g' at hgg
    subst g'
    cases hg : a g with
    | false =>
      have hh : b h = false := by cases hh : b h <;> simp_all
      have hh' : b h' = true := by cases hh' : b h' <;> simp_all
      refine ⟨Sum.inr (g,⟨(h,h'),hadj,hh,hh'⟩), ?_⟩
      apply Subtype.ext
      simp [cutCover, verticalCut, hg]
    | true =>
      have hh : b h = true := by cases hh : b h <;> simp_all
      have hh' : b h' = false := by cases hh' : b h' <;> simp_all
      refine ⟨Sum.inr (g,⟨(h',h),hadj.symm,hh',hh⟩), ?_⟩
      apply Subtype.ext
      simp [cutCover, verticalCut, hg]
  · change h = h' at hhh
    subst h'
    cases hh : b h with
    | false =>
      have hg : a g = false := by cases hg : a g <;> simp_all
      have hg' : a g' = true := by cases hg' : a g' <;> simp_all
      refine ⟨Sum.inl (⟨(g,g'),hadj,hg,hg'⟩,h), ?_⟩
      apply Subtype.ext
      simp [cutCover, horizontalCut, hh]
    | true =>
      have hg : a g = true := by cases hg : a g <;> simp_all
      have hg' : a g' = false := by cases hg' : a g' <;> simp_all
      refine ⟨Sum.inl (⟨(g',g),hadj.symm,hg',hg⟩,h), ?_⟩
      apply Subtype.ext
      simp [cutCover, horizontalCut, hh]
  · have he := xor_both_flip _ _ _ _ (ha _ _ hadjA) (hb _ _ hadjB)
    rw [h0,h1] at he
    contradiction

lemma product_cut_card_le [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    [DecidableRel A.Adj] [DecidableRel B.Adj]
    (ha : ∀ u v, A.Adj u v → a u ≠ a v)
    (hb : ∀ u v, B.Adj u v → b u ≠ b v) :
    Fintype.card (CutEdge (strongProduct A B) (productSide a b)) ≤
      Fintype.card (CutEdge A a) * Fintype.card W +
      Fintype.card V * Fintype.card (CutEdge B b) := by
  have hc := Fintype.card_le_of_surjective (cutCover A B a b)
    (cutCover_surjective A B a b ha hb)
  simpa only [CutSource,Fintype.card_sum,Fintype.card_prod] using hc

#print axioms product_cut_card_le
end ProductImmersion
```

### `ProductCounts.lean`

```lean
import ProductCut
namespace ProductImmersion
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def sideG (i : Fin 14) : Bool := decide (4 ≤ i.val ∧ i.val < 11)
def sideH (i : Fin 22) : Bool := decide (6 ≤ i.val ∧ i.val < 17)
def sideP : Fin 14 × Fin 22 → Bool := productSide sideG sideH

abbrev Eligible := {v : Fin 14 × Fin 22 // v.1.val < 8 ∧ v.2.val < 12}
lemma eligible_card : Fintype.card Eligible = 96 := by decide
lemma eligible_left : Fintype.card {v : Eligible // sideP v.val = false} = 48 := by decide
lemma eligible_right : Fintype.card {v : Eligible // sideP v.val = true} = 48 := by decide

lemma bipartiteG : ∀ u v : Fin 14, G.Adj u v → sideG u ≠ sideG v := by decide
lemma bipartiteH : ∀ u v : Fin 22, H.Adj u v → sideH u ≠ sideH v := by decide
lemma factor_cutG : Fintype.card (CutEdge G sideG) = 40 := by decide
lemma factor_cutH : Fintype.card (CutEdge H sideH) = 96 := by decide

lemma cut_card_bound : Fintype.card (CutEdge P sideP) ≤ 2224 := by
  have hc := product_cut_card_le G H sideG sideH bipartiteG bipartiteH
  have hn : 40 * 22 + 14 * 96 = 2224 := by decide
  simp only [factor_cutG, factor_cutH, Fintype.card_fin, hn] at hc
  convert hc using 1
  exact Fintype.card_congr (Equiv.refl _)

#print axioms eligible_card
#print axioms eligible_left
#print axioms eligible_right
#print axioms cut_card_bound
end ProductImmersion
```

### `StrongProductCounterexample.lean`

```lean
import FactorImmersions
import ProductCounts
import Mathlib.Data.Fintype.EquivFin
import ImmersionNumber
namespace ProductImmersion
lemma no_immersionP : ¬ Nonempty (CliqueImmersion P 96) := by
  classical
  rintro ⟨I⟩
  have hcoords (i : Fin 96) : (I.branch i).1.val < 8 ∧ (I.branch i).2.val < 12 :=
    degree_eligible _ (I.degree_bound i)
  let f : Fin 96 → Eligible := fun i => ⟨I.branch i, hcoords i⟩
  have hf : Function.Injective f := by
    intro i j he
    exact I.injective (congrArg Subtype.val he)
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hf, by simp [eligible_card]⟩
  have side_card (b : Bool) :
      Fintype.card {i : Fin 96 // sideP (I.branch i) = b} =
      Fintype.card {v : Eligible // sideP v.val = b} := by
    let fside : {i : Fin 96 // sideP (I.branch i) = b} →
        {v : Eligible // sideP v.val = b} :=
      fun i => ⟨f i.val, i.property⟩
    apply Fintype.card_of_bijective (f := fside)
    constructor
    · intro i j he
      exact Subtype.ext (hf (congrArg Subtype.val he))
    · intro v
      obtain ⟨i, hi⟩ := hbij.2 v.val
      have hs : sideP (I.branch i) = b := by
        change sideP (f i).val = b
        rw [hi]
        exact v.property
      exact ⟨⟨i,hs⟩, Subtype.ext hi⟩
  have hleft : Fintype.card {i : Fin 96 // sideP (I.branch i) = false} = 48 :=
    (side_card false).trans eligible_left
  have hright : Fintype.card {i : Fin 96 // sideP (I.branch i) = true} = 48 :=
    (side_card true).trans eligible_right
  have hc := I.cut_bound sideP
  change Fintype.card (_ × _) ≤ _ at hc
  rw [Fintype.card_prod, hleft, hright] at hc
  have hb := cut_card_bound
  omega

theorem strong_product_counterexample :
    Nonempty (CliqueImmersion G 8) ∧ ¬ Nonempty (CliqueImmersion G 9) ∧
    Nonempty (CliqueImmersion H 12) ∧ ¬ Nonempty (CliqueImmersion H 13) ∧
    ¬ Nonempty (CliqueImmersion (strongProduct G H) 96) :=
  ⟨⟨immersionG⟩, no_immersionG, ⟨immersionH⟩, no_immersionH, no_immersionP⟩

theorem literal_immersion_number_counterexample :
    immersionNumber (strongProduct G H) < immersionNumber G * immersionNumber H := by
  have hg : immersionNumber G = 8 := immersionNumber_eq 8 (by decide) ⟨immersionG⟩ no_immersionG
  have hh : immersionNumber H = 12 := immersionNumber_eq 12 (by decide) ⟨immersionH⟩ no_immersionH
  have hp : immersionNumber (strongProduct G H) < 96 :=
    immersionNumber_lt 96 (by decide) no_immersionP
  rw [hg,hh]
  exact hp

#print axioms literal_immersion_number_counterexample
#print axioms strong_product_counterexample

end ProductImmersion
```

### `SelfProductGap.lean`

```lean
import StrongProductCounterexample
import Mathlib.Tactic.Linarith

namespace ProductImmersion
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

abbrev Q := strongProduct H H
def sideQ : Fin 22 × Fin 22 → Bool := productSide sideH sideH
abbrev EligibleQ := {v : Fin 22 × Fin 22 // v.1.val < 12 ∧ v.2.val < 12}

lemma eligibleQ_sides (b : Bool) :
    Fintype.card {v : EligibleQ // sideQ v.val = b} = 72 := by
  cases b <;> decide

lemma degreeQ_eligible (v : Fin 22 × Fin 22) (hd : 130 ≤ degree Q v) :
    v.1.val < 12 ∧ v.2.val < 12 := by
  rcases v with ⟨g,h⟩
  change g.val < 12 ∧ h.val < 12
  change 130 ≤ degree (strongProduct H H) (g,h) at hd
  have he := product_degree H H g h
  rw [degreeH_exact,degreeH_exact] at he
  split_ifs at he <;> omega

lemma cutQ_bound : Fintype.card (CutEdge Q sideQ) ≤ 4224 := by
  have hc := product_cut_card_le H H sideH sideH bipartiteH bipartiteH
  simp only [factor_cutH,Fintype.card_fin] at hc
  convert hc using 1
  exact Fintype.card_congr (Equiv.refl _)

lemma no_immersionQ131 : ¬ Nonempty (CliqueImmersion Q 131) := by
  classical
  rintro ⟨I⟩
  have hcoords (i : Fin 131) :
      (I.branch i).1.val < 12 ∧ (I.branch i).2.val < 12 :=
    degreeQ_eligible _ (I.degree_bound i)
  have side_card_le (b : Bool) :
      Fintype.card {i : Fin 131 // sideQ (I.branch i) = b} ≤ 72 := by
    let f : {i : Fin 131 // sideQ (I.branch i) = b} →
        {v : EligibleQ // sideQ v.val = b} :=
      fun i => ⟨⟨I.branch i.val,hcoords i.val⟩,i.property⟩
    have hf : Function.Injective f := by
      intro i j he
      apply Subtype.ext
      apply I.injective
      exact congrArg (fun x => x.val.val) he
    have hc := Fintype.card_le_of_injective f hf
    rwa [eligibleQ_sides] at hc
  let l := Fintype.card {i : Fin 131 // sideQ (I.branch i) = false}
  let r := Fintype.card {i : Fin 131 // sideQ (I.branch i) = true}
  have hl : l ≤ 72 := side_card_le false
  have hr : r ≤ 72 := side_card_le true
  have hsum : l + r = 131 := by
    have hc := Fintype.card_subtype_compl (fun i : Fin 131 => sideQ (I.branch i) = false)
    have hcard : Fintype.card {x : Fin 131 // ¬ sideQ (I.branch x) = false} = r := by
      apply Fintype.card_congr
      exact Equiv.subtypeEquivRight (fun x => by cases sideQ (I.branch x) <;> simp)
    have hlcard : l ≤ 131 := by
      exact Fintype.card_subtype_le _
    rw [hcard,Fintype.card_fin] at hc
    change r = 131 - l at hc
    omega
  have hc := I.cut_bound sideQ
  change Fintype.card (_ × _) ≤ _ at hc
  rw [Fintype.card_prod] at hc
  change l * r ≤ _ at hc
  have hb := cutQ_bound
  have hp : 0 ≤ (72 - (l : ℤ)) * (72 - (r : ℤ)) :=
    mul_nonneg (by omega) (by omega)
  have hc' : (l : ℤ) * (r : ℤ) ≤ 4224 := by
    exact_mod_cast Nat.le_trans hc hb
  have hs' : (l : ℤ) + (r : ℤ) = 131 := by exact_mod_cast hsum
  nlinarith

theorem self_product_immersion_number_le_130 :
    immersionNumber (strongProduct H H) ≤ 130 := by
  have h := immersionNumber_lt 131 (by decide) no_immersionQ131
  change immersionNumber (strongProduct H H) < 131 at h
  omega

#print axioms self_product_immersion_number_le_130
end ProductImmersion
```

### `CheckerboardLower.lean`

```lean
import SelfProductGap
import Mathlib.Tactic.FinCases
namespace ProductImmersion
set_option maxRecDepth 100000
set_option maxHeartbeats 64000000

abbrev Point := Fin 22 × Fin 22
def point (x y : ℕ) : Point := (⟨x%22,by omega⟩,⟨y%22,by omega⟩)
def branch72 (i : Fin 72) : Point :=
  point ((i.val/6)%6 + if i.val<36 then 0 else 6)
    (i.val%6 + if i.val<36 then 0 else 6)
def len72 (i j : Fin 72) : ℕ :=
  if i=j then 0 else if (i.val<36)=(j.val<36) then 2 else 1
def routeMiddle (x y : ℕ) : ℕ := if x=y then x else pathVal 6 x y 1
def middle72 (i j : Fin 72) : Point :=
  point (routeMiddle (branch72 i).1.val (branch72 j).1.val)
    (routeMiddle (branch72 i).2.val (branch72 j).2.val)
def vertex72 (i j : Fin 72) (k : ℕ) : Point :=
  if k=0 then branch72 i else
  if k=1 ∧ (i.val<36)=(j.val<36) ∧ i≠j then middle72 i j else branch72 j

def pointCode (v : Point) : Fin 484 := ⟨v.1.val*22+v.2.val,by omega⟩
def codeKey (x y : ℕ) : ℕ := (x%6)*6+y%6+(if x<6 then 0 else 36)
def otherEnd (x y : ℕ) : ℕ :=
  if x=y then x else
  let p := edgeOwner 6 x y
  if p.1=x then p.2 else p.1
def lowerOwnerOrdered (x y : ℕ) : ℕ × ℕ :=
  let p := (x/22,x%22)
  let q := (y/22,y%22)
  if p.1<12 ∧ p.2<12 ∧ q.1<12 ∧ q.2<12 then
    targetKey (codeKey p.1 p.2) (codeKey q.1 q.2)
  else
    let b := if p.1<12 ∧ p.2<12 then p else q
    let m := if p.1<12 ∧ p.2<12 then q else p
    targetKey (codeKey b.1 b.2) (codeKey (otherEnd b.1 m.1) (otherEnd b.2 m.2))
def lowerOwner (x y : Fin 484) : ℕ × ℕ :=
  lowerOwnerOrdered (min x.val y.val) (max x.val y.val)
lemma lowerOwner_symm (x y : Fin 484) : lowerOwner x y = lowerOwner y x := by
  simp only [lowerOwner,min_comm x.val y.val,max_comm x.val y.val]
lemma lowerOwner_recovers : ∀ (i j : Fin 72), i≠j → ∀ a : Fin (len72 i j),
    lowerOwner (pointCode (vertex72 i j a)) (pointCode (vertex72 i j (a.val+1))) =
      targetKey i.val j.val := by
  intro i
  fin_cases i <;> decide +kernel

def immersion72 : CliqueImmersion Q 72 where
  branch := branch72
  injective := by intro i; fin_cases i <;> decide +kernel
  len := len72
  vertex := vertex72
  start := by intro i j; rfl
  finish := by intro i; fin_cases i <;> decide +kernel
  adjacent := by intro i; fin_cases i <;> decide +kernel
  simple := by intro i; fin_cases i <;> decide +kernel
  disjoint := by
    intro i j hij k l hkl a b he
    apply disjoint_from_owner (fun i j a => pointCode (vertex72 i j a)) len72
      lowerOwner lowerOwner_symm lowerOwner_recovers i j hij k l hkl a b
    rcases he with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact Or.inl ⟨congrArg pointCode h1,congrArg pointCode h2⟩
    · exact Or.inr ⟨congrArg pointCode h1,congrArg pointCode h2⟩

theorem self_product_immersion_interval :
    72 ≤ immersionNumber (strongProduct H H) ∧
    immersionNumber (strongProduct H H) ≤ 130 :=
  ⟨immersionNumber_is_largest 72 ⟨immersion72⟩,self_product_immersion_number_le_130⟩

#print axioms immersion72
#print axioms self_product_immersion_interval
end ProductImmersion
```

### `StrongProductConjecture.lean`

```lean
import StrongProductCounterexample

namespace ProductImmersion

-- The source quantifies over finite simple graphs of arbitrary orders.
-- Type (universe zero) suffices and matches the copied definitions.
def StrongProductConjecture : Prop :=
  ∀ (V W : Type) [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W),
    immersionNumber G * immersionNumber H ≤ immersionNumber (strongProduct G H)

theorem strong_product_conjecture_false :
    ¬ ∀ (V W : Type) [Fintype V] [Fintype W]
      (G : SimpleGraph V) (H : SimpleGraph W),
      immersionNumber G * immersionNumber H ≤ immersionNumber (strongProduct G H) := by
  intro h
  exact (Nat.not_le_of_lt literal_immersion_number_counterexample)
    (h (Fin 14) (Fin 22) G H)

theorem mathdb343652 : ¬ StrongProductConjecture :=
  strong_product_conjecture_false

#check literal_immersion_number_counterexample
#check strong_product_conjecture_false
#print StrongProductConjecture
#print axioms literal_immersion_number_counterexample
#print axioms strong_product_conjecture_false
#print axioms mathdb343652
#print axioms strong_product_counterexample

end ProductImmersion
```

