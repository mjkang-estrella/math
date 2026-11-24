# Complete Lean source appendix

MathDB 337410. Modules are in dependency order.

### `RamseyDefinitions.lean`

```lean
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.ByContra

set_option autoImplicit false
namespace MultipartiteRamsey

abbrev Part (c s : ℕ) := Fin c × Fin s

def Host (c s : ℕ) : SimpleGraph (Fin c × Fin s) where
  Adj u v := u.1 ≠ v.1
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => h rfl⟩

def HasC4 {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ a b x y, a ≠ b ∧ x ≠ y ∧ G.Adj a x ∧ G.Adj a y ∧ G.Adj b x ∧ G.Adj b y

noncomputable def Nbr {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V) : Finset V :=
  @Finset.filter V (G.Adj v) (Classical.decPred _) Finset.univ

noncomputable def HasStarInRelCompl (c s n : ℕ)
    (G : SimpleGraph (Fin c × Fin s)) : Prop := by
  classical
  exact ∃ v, n ≤ (Finset.univ.filter (fun w => v.1 ≠ w.1 ∧ ¬ G.Adj v w)).card

def RamseyProp (s n c : ℕ) : Prop :=
  0 < c ∧ ∀ G : SimpleGraph (Fin c × Fin s),
    G ≤ Host c s → HasC4 G ∨ HasStarInRelCompl c s n G

noncomputable def M (s n : ℕ) : ℕ := by
  classical
  exact if h : ∃ c, RamseyProp s n c then Nat.find h else 0

@[simp] theorem mem_Nbr {V : Type*} [Fintype V] (G : SimpleGraph V) (v w : V) :
    w ∈ Nbr G v ↔ G.Adj v w := by
  classical
  simp [Nbr]

theorem common_unique {V : Type*} {G : SimpleGraph V} (hG : ¬ HasC4 G)
    {a b x y : V} (hab : a ≠ b) (hax : G.Adj a x) (hbx : G.Adj b x)
    (hay : G.Adj a y) (hby : G.Adj b y) : x = y := by
  by_contra hxy
  exact hG ⟨a, b, x, y, hab, hxy, hax, hay, hbx, hby⟩

theorem hasC4_of_injective {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : V → W) (hf : Function.Injective f)
    (he : ∀ a b, G.Adj a b → H.Adj (f a) (f b)) (h : HasC4 G) : HasC4 H := by
  obtain ⟨a,b,x,y,hab,hxy,hax,hay,hbx,hby⟩ := h
  exact ⟨f a, f b, f x, f y, fun h => hab (hf h), fun h => hxy (hf h),
    he _ _ hax, he _ _ hay, he _ _ hbx, he _ _ hby⟩

theorem M_le {s n c : ℕ} (h : RamseyProp s n c) : M s n ≤ c := by
  classical
  rw [M, dite_eq_left ⟨c,h⟩]
  exact Nat.find_min' _ h

theorem not_star_one (s n : ℕ) (hn : 1 ≤ n) (G : SimpleGraph (Part 1 s)) :
    ¬ HasStarInRelCompl 1 s n G := by
  classical
  rintro ⟨v,hv⟩
  have hz : (Finset.univ.filter (fun w : Part 1 s => v.1 ≠ w.1 ∧ ¬ G.Adj v w)).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro w _ hw
    exact hw.1 (Subsingleton.elim _ _)
  rw [hz] at hv
  omega

theorem not_ramseyProp_one (s n : ℕ) (hn : 1 ≤ n) : ¬ RamseyProp s n 1 := by
  classical
  rintro ⟨_, h⟩
  rcases h ⊥ bot_le with h4 | hstar
  · obtain ⟨a,b,x,y,_,_,hax,_⟩ := h4
    exact hax
  · exact not_star_one s n hn _ hstar

#print axioms common_unique
#print axioms hasC4_of_injective
#print axioms M_le
#print axioms not_ramseyProp_one
end MultipartiteRamsey
```

### `RamseyFinite.lean`

```lean
import RamseyDefinitions
import Mathlib.Tactic.Linarith

open scoped Classical
set_option autoImplicit false
namespace MultipartiteRamsey

variable {V : Type*} [Fintype V]

theorem common_card_le_one {G : SimpleGraph V} (hG : ¬ HasC4 G)
    {a b : V} (hab : a ≠ b) : ((Nbr G a) ∩ (Nbr G b)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro x hx y hy
  simp only [Finset.mem_inter, mem_Nbr] at hx hy
  exact common_unique hG hab hx.1 hx.2 hy.1 hy.2

theorem degree_pair_bound {G : SimpleGraph V} (hG : ¬ HasC4 G)
    {a b : V} (hab : a ≠ b) :
    (Nbr G a).card + (Nbr G b).card ≤ Fintype.card V + 1 := by
  classical
  have h1 := common_card_le_one hG hab
  have h2 := Finset.card_le_univ ((Nbr G a) ∪ (Nbr G b))
  have h3 := Finset.card_union_add_card_inter (Nbr G a) (Nbr G b)
  omega

theorem host_degree_lower {c s n : ℕ} (hn : 1 ≤ n)
    {G : SimpleGraph (Part c s)} (hS : ¬ HasStarInRelCompl c s n G)
    (v : Part c s) : c*s ≤ (Nbr G v).card + s + (n-1) := by
  classical
  let A : Finset (Part c s) := Finset.univ.filter (fun w => v.1 = w.1)
  let B : Finset (Part c s) :=
    Finset.univ.filter (fun w => v.1 ≠ w.1 ∧ ¬ G.Adj v w)
  have hB : B.card ≤ n-1 := by
    have h : ¬ n ≤ B.card := fun hb => hS ⟨v,hb⟩
    omega
  have hA : A.card = s := by
    have he : A = Finset.univ.image (fun t : Fin s => (v.1,t)) := by
      ext w
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro h
        exact ⟨w.2, Prod.ext h rfl⟩
      · rintro ⟨t,ht⟩
        have he := congrArg (fun z : Part c s => z.1) ht
        exact he
    rw [he, Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)]
    simp
  have hcover : (Finset.univ : Finset (Part c s)) ⊆ (Nbr G v) ∪ A ∪ B := by
    intro w _
    by_cases h : G.Adj v w
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (mem_Nbr _ _ _ |>.mpr h))
    · by_cases he : v.1 = w.1
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simp [A, he]))
      · exact Finset.mem_union_right _ (by simp [B, he, h])
  have hc := Finset.card_le_card hcover
  have hu := Finset.card_union_le ((Nbr G v) ∪ A) B
  have hu' := Finset.card_union_le (Nbr G v) A
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at hc
  omega

/-- A coarse uniform witness, including s=1, where the growth claim is not used. -/
theorem ramseyProp_bound (s n : ℕ) (hs : 1 ≤ s) (hn : 1 ≤ n) :
    RamseyProp s n (2*n+6) := by
  classical
  refine ⟨by omega, ?_⟩
  intro G _
  by_cases h4 : HasC4 G
  · exact Or.inl h4
  right
  by_contra hstar
  let a : Part (2*n+6) s := (⟨0, by omega⟩, ⟨0, by omega⟩)
  let b : Part (2*n+6) s := (⟨1, by omega⟩, ⟨0, by omega⟩)
  have hab : a ≠ b := by
    intro h
    have := congrArg (fun v => v.1.val) h
    simp [a,b] at this
  have ha := host_degree_lower hn hstar a
  have hb := host_degree_lower hn hstar b
  have hp := degree_pair_bound h4 hab
  simp only [Fintype.card_prod, Fintype.card_fin] at hp
  have hns : n ≤ n*s := by nlinarith
  have hn1 : n-1+1 = n := by omega
  nlinarith

theorem ramseyProp_exists (s n : ℕ) (hs : 1 ≤ s) (hn : 1 ≤ n) :
    ∃ c, RamseyProp s n c := ⟨2*n+6, ramseyProp_bound s n hs hn⟩

theorem M_spec (s n : ℕ) (hs : 1 ≤ s) (hn : 1 ≤ n) : RamseyProp s n (M s n) := by
  classical
  have hex := ramseyProp_exists s n hs hn
  rw [M, dite_eq_left hex]
  exact Nat.find_spec hex

theorem M_ge_two (s n : ℕ) (hs : 1 ≤ s) (hn : 1 ≤ n) : 2 ≤ M s n := by
  have h := M_spec s n hs hn
  have hne : M s n ≠ 1 := fun he => not_ramseyProp_one s n hn (he ▸ h)
  have := h.1
  omega

#print axioms degree_pair_bound
#print axioms host_degree_lower
#print axioms ramseyProp_exists
#print axioms M_spec
#print axioms M_ge_two
end MultipartiteRamsey
```

### `RamseyRepair.lean`

```lean
import RamseyDefinitions
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Embedding

set_option autoImplicit false
namespace MultipartiteRamsey

/-- Each other vertex in v's class sees at most one point of A; a point is missed. -/
theorem swap_missed {c s : ℕ} {G : SimpleGraph (Part c s)}
    (h4 : ¬ HasC4 G) (i : Fin c) (v : Part c s)
    (hall : ∀ t : Fin s, G.Adj v (i,t)) :
    ∃ a : Fin s, ∀ t : Fin s, t ≠ v.2 → ¬ G.Adj (i,a) (v.1,t) := by
  classical
  by_contra h
  have hex : ∀ a : Fin s, ∃ t : Fin s, t ≠ v.2 ∧ G.Adj (i,a) (v.1,t) := by
    intro a
    by_contra hn
    apply h
    refine ⟨a, ?_⟩
    intro t ht ha
    exact hn ⟨t, ht, ha⟩
  choose f hfne hfadj using hex
  have hinj : Function.Injective f := by
    intro a b hab
    have hvw : v ≠ (v.1, f a) := by
      intro he
      exact hfne a (congrArg Prod.snd he).symm
    have he := common_unique h4 hvw (hall a) (hfadj a).symm (hall b)
      (by simpa only [hab] using (hfadj b).symm)
    exact congrArg Prod.snd he
  obtain ⟨a, ha⟩ := (Finite.surjective_of_injective hinj) v.2
  exact hfne a ha

theorem exists_two_avoiding {s : ℕ} (hs : 3 ≤ s) (a : Fin s) :
    ∃ x y : Fin s, x ≠ a ∧ y ≠ a ∧ x ≠ y := by
  classical
  have hc : 1 < ((Finset.univ : Finset (Fin s)).erase a).card := by
    simp only [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ,
      Fintype.card_fin]
    omega
  obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp hc
  exact ⟨x,y,(Finset.mem_erase.mp hx).1,(Finset.mem_erase.mp hy).1,hxy⟩

/-- The literal transposition repairs the retained classes and prevents full loss. -/
theorem swap_good {c s : ℕ} (hs : 3 ≤ s) {G : SimpleGraph (Part c s)}
    (h4 : ¬ HasC4 G) (hh : G ≤ Host c s) (i : Fin c) (v : Part c s)
    (hvi : v.1 ≠ i) (hall : ∀ t : Fin s, G.Adj v (i,t))
    (a : Fin s) (hmiss : ∀ t : Fin s, t ≠ v.2 → ¬ G.Adj (i,a) (v.1,t)) :
    let e := Equiv.swap (i,a) v
    (∀ j x y, j ≠ i → ¬ G.Adj (e (j,x)) (e (j,y))) ∧
    (∀ w, (e.symm w).1 ≠ i → ∃ t, ¬ G.Adj w (e (i,t))) := by
  classical
  dsimp only
  constructor
  · intro j x y hji
    have hxA : (j,x) ≠ (i,a) := fun h => hji (congrArg Prod.fst h)
    have hyA : (j,y) ≠ (i,a) := fun h => hji (congrArg Prod.fst h)
    by_cases hx : (j,x) = v
    · rw [hx, Equiv.swap_apply_right]
      by_cases hy : (j,y) = v
      · rw [hy, Equiv.swap_apply_right]
        exact G.irrefl
      · rw [Equiv.swap_apply_of_ne_of_ne hyA hy]
        have hj : j = v.1 := congrArg Prod.fst hx
        have hy' : y ≠ v.2 := fun he => hy (Prod.ext hj he)
        simpa only [hj] using hmiss y hy'
    · rw [Equiv.swap_apply_of_ne_of_ne hxA hx]
      by_cases hy : (j,y) = v
      · rw [hy, Equiv.swap_apply_right]
        have hj : j = v.1 := congrArg Prod.fst hy
        have hx' : x ≠ v.2 := fun he => hx (Prod.ext hj he)
        exact fun he => hmiss x hx' (by simpa only [hj] using he.symm)
      · rw [Equiv.swap_apply_of_ne_of_ne hyA hy]
        exact fun he => hh he rfl
  · intro w hw
    have hwv : w ≠ v := by
      intro he
      subst w
      exact hw (by simp only [Equiv.symm_swap, Equiv.swap_apply_right])
    obtain ⟨x,y,hxa,hya,hxy⟩ := exists_two_avoiding hs a
    have hxA : (i,x) ≠ (i,a) := fun h => hxa (congrArg Prod.snd h)
    have hyA : (i,y) ≠ (i,a) := fun h => hya (congrArg Prod.snd h)
    have hxv : (i,x) ≠ v := fun h => hvi (congrArg Prod.fst h).symm
    have hyv : (i,y) ≠ v := fun h => hvi (congrArg Prod.fst h).symm
    by_cases hx : G.Adj w (i,x)
    · refine ⟨y, ?_⟩
      rw [Equiv.swap_apply_of_ne_of_ne hyA hyv]
      intro hy
      have he := common_unique h4 hwv hx (hall x) hy (hall y)
      exact hxy (congrArg Prod.snd he)
    · refine ⟨x, ?_⟩
      rwa [Equiv.swap_apply_of_ne_of_ne hxA hxv]

/-- Repartitioning, with no assertion that the deleted set is independent. -/
theorem repair_large {c s : ℕ} (hs : 3 ≤ s) {G : SimpleGraph (Part (c+1) s)}
    (h4 : ¬ HasC4 G) (hh : G ≤ Host (c+1) s) (i : Fin (c+1)) :
    ∃ e : Part (c+1) s ≃ Part (c+1) s,
    (∀ j x y, j ≠ i → ¬ G.Adj (e (j,x)) (e (j,y))) ∧
    (∀ w, (e.symm w).1 ≠ i → ∃ t, ¬ G.Adj w (e (i,t))) := by
  classical
  by_cases hex : ∃ v, ∀ t : Fin s, G.Adj v (i,t)
  · obtain ⟨v,hv⟩ := hex
    have hvi : v.1 ≠ i := by
      have : Nonempty (Fin s) := ⟨⟨0,by omega⟩⟩
      exact hh (hv Classical.ofNonempty)
    obtain ⟨a,ha⟩ := swap_missed h4 i v hv
    exact ⟨Equiv.swap (i,a) v, swap_good hs h4 hh i v hvi hv a ha⟩
  · refine ⟨Equiv.refl _, ?_, ?_⟩
    · intro j x y _ he
      exact hh he rfl
    · intro w _
      by_contra hn
      apply hex
      refine ⟨w, ?_⟩
      intro t
      by_contra ht
      exact hn ⟨t,ht⟩

#print axioms swap_missed
#print axioms swap_good
#print axioms repair_large
end MultipartiteRamsey
```

### `RamseyMatching.lean`

```lean
import RamseyDefinitions
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.Perm
import Mathlib.Logic.Equiv.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.FinCases

open scoped Classical
set_option autoImplicit false
namespace MultipartiteRamsey

/-- A pairing is a fixed-point-free involution; every vertex is paired. -/
abbrev Pairing (V : Type*) := {f : V → V // Function.Involutive f ∧ ∀ v, f v ≠ v}

variable {V : Type*} [Fintype V]

instance : Finite (Pairing V) := inferInstanceAs (Finite {_f : V → V // _})

theorem pairing_exists (he : Even (Fintype.card V)) : Nonempty (Pairing V) := by
  classical
  obtain ⟨k,hk⟩ := he
  let e : V ≃ Fin k × Fin 2 := Fintype.equivOfCardEq (by
    simp only [Fintype.card_prod, Fintype.card_fin]
    omega)
  let t := Equiv.swap (0 : Fin 2) 1
  let f : V → V := fun v => e.symm ((e v).1, t (e v).2)
  refine ⟨⟨f, ?_, ?_⟩⟩
  · intro v
    simp [f,t,Equiv.swap_apply_self]
  · intro v hv
    have h := congrArg (fun w => (e w).2) hv
    have h' : t (e v).2 = (e v).2 := by simpa only [f,Equiv.apply_symm_apply] using h
    have hne : ∀ u : Fin 2, t u ≠ u := by
      intro u
      fin_cases u <;> decide
    exact hne _ h'


noncomputable def Good (G : SimpleGraph V) (f : Pairing V) : Finset V :=
  Finset.univ.filter (fun v => G.Adj v (f.val v))

@[simp] theorem mem_Good (G : SimpleGraph V) (f : Pairing V) (v : V) :
    v ∈ Good G f ↔ G.Adj v (f.val v) := by simp [Good]

/-- Conjugation by a transposition preserves a pairing. -/
noncomputable def rewire (f : Pairing V) (b x : V) : Pairing V := by
  classical
  let t := Equiv.swap b x
  refine ⟨fun v => t (f.val (t v)), ?_, ?_⟩
  · intro v
    dsimp only
    rw [Equiv.swap_apply_self, f.property.1, Equiv.swap_apply_self]
  · intro v h
    have hh := congrArg t h
    rw [Equiv.swap_apply_self] at hh
    exact f.property.2 (t v) hh

theorem rewire_improves {G : SimpleGraph V} (f : Pairing V) (a x : V)
    (hab : ¬ G.Adj a (f.val a))
    (hax : G.Adj a x) (hby : G.Adj (f.val a) (f.val x)) :
    (Good G f).card < (Good G (rewire f (f.val a) x)).card := by
  classical
  let b := f.val a
  let y := f.val x
  have hba : f.val b = a := f.property.1 a
  have hyx : f.val y = x := f.property.1 x
  have habne : a ≠ b := (f.property.2 a).symm
  have hxyne : x ≠ y := (f.property.2 x).symm
  have haxne : a ≠ x := hax.ne
  have hbxne : b ≠ x := by
    intro h
    apply hab
    change G.Adj a b
    exact h.symm ▸ hax
  have hayne : a ≠ y := by
    intro h
    have hh : b = x := by simpa only [b,hba,hyx] using congrArg f.val h
    exact hbxne hh
  have hbyne : b ≠ y := hby.ne
  let g := rewire f b x
  have hga : g.val a = x := by
    simp [g,rewire,Equiv.swap_apply_of_ne_of_ne habne haxne,b]
  have hgb : g.val b = y := by
    simp only [g,rewire,Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne hbyne.symm hxyne.symm
  have hgx : g.val x = a := by
    simp only [g,rewire,Equiv.swap_apply_right,hba]
    exact Equiv.swap_apply_of_ne_of_ne habne haxne
  have hgy : g.val y = b := by
    simp only [g,rewire,Equiv.swap_apply_of_ne_of_ne hbyne.symm hxyne.symm,hyx,
      Equiv.swap_apply_right]
  have hother : ∀ v, v ≠ a → v ≠ b → v ≠ x → v ≠ y → g.val v = f.val v := by
    intro v hva hvb hvx hvy
    have hfb : f.val v ≠ b := fun h => hva (f.property.1 v ▸ (congrArg f.val h).trans hba)
    have hfx : f.val v ≠ x := fun h => hvy (f.property.1 v ▸ congrArg f.val h)
    simp only [g,rewire,Equiv.swap_apply_of_ne_of_ne hvb hvx,
      Equiv.swap_apply_of_ne_of_ne hfb hfx]
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro v hv
    rw [mem_Good] at hv ⊢
    by_cases hva : v = a
    · subst v
      exact (hab hv).elim
    by_cases hvb : v = b
    · subst v
      exact (hab (by simpa only [hba] using hv.symm)).elim
    by_cases hvx : v = x
    · subst v
      rw [hgx]
      exact hax.symm
    by_cases hvy : v = y
    · subst v
      rw [hgy]
      exact hby.symm
    rw [hother v hva hvb hvx hvy]
    exact hv
  · intro he
    have hmem : a ∈ Good G g := by rw [mem_Good,hga]; exact hax
    have : a ∈ Good G f := he ▸ hmem
    exact hab ((mem_Good _ _ _).mp this)

/-- A finite even graph of minimum degree at least half its order has a pairing
whose pairs are edges. This is the exact dense matching fact used later. -/
theorem dense_matching (G : SimpleGraph V) (he : Even (Fintype.card V))
    (hd : ∀ v, Fintype.card V ≤ 2*(Nbr G v).card) :
    ∃ f : V ≃ V, (∀ v, f (f v) = v) ∧ (∀ v, G.Adj v (f v)) := by
  classical
  let _ : Nonempty (Pairing V) := pairing_exists he
  obtain ⟨f,hmax⟩ := Finite.exists_max (fun f : Pairing V => (Good G f).card)
  have hall : ∀ a, G.Adj a (f.val a) := by
    intro a
    by_contra hab
    let b := f.val a
    let A := Nbr G a
    let B := (Nbr G b).image f.val
    have hdis : Disjoint A B := by
      apply Finset.disjoint_left.mpr
      intro x hx hB
      obtain ⟨y,hy,hyx⟩ := Finset.mem_image.mp hB
      have hby : G.Adj b (f.val x) := by
        rw [← hyx, f.property.1]
        exact (mem_Nbr _ _ _).mp hy
      have him := rewire_improves f a x hab ((mem_Nbr _ _ _).mp hx) hby
      have hm := hmax (rewire f b x)
      exact (not_lt_of_ge hm) him
    have hcardB : B.card = (Nbr G b).card :=
      Finset.card_image_of_injective _ f.property.1.injective
    have hnot : a ∉ A ∪ B := by
      intro ha
      rcases Finset.mem_union.mp ha with ha | ha
      · exact G.irrefl ((mem_Nbr _ _ _).mp ha)
      · obtain ⟨y,hy,hyv⟩ := Finset.mem_image.mp ha
        have hyb : y = b := (f.property.1 y).symm.trans (congrArg f.val hyv)
        exact G.irrefl ((mem_Nbr _ _ _).mp (hyb ▸ hy))
    have hle : (A ∪ B).card < Fintype.card V := by
      have hi : A ∪ B ⊂ (Finset.univ : Finset V) :=
        Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, fun h =>
          hnot (h.symm ▸ Finset.mem_univ a)⟩
      simpa only [Finset.card_univ] using Finset.card_lt_card hi
    rw [Finset.card_union_of_disjoint hdis, hcardB] at hle
    have ha := hd a
    have hb := hd b
    dsimp only [A] at hle
    omega
  refine ⟨⟨f.val,f.val,f.property.1,f.property.1⟩,f.property.1,hall⟩

#print axioms rewire_improves
#print axioms dense_matching
end MultipartiteRamsey
```

### `RamseyFriendship.lean`

```lean
import RamseyFinite
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Parity

open scoped Classical
open scoped BigOperators
set_option autoImplicit false
namespace MultipartiteRamsey

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Counting the non-returning two-step walks out of v. -/
theorem twoStep_count (h4 : ¬ HasC4 G) (v : V) :
    (∑ x ∈ Nbr G v, ((Nbr G x).card - 1)) ≤ Fintype.card V - 1 := by
  classical
  let T := Σ x : ↑(Nbr G v), ↑((Nbr G x.val).erase v)
  let f : T → ↑((Finset.univ : Finset V).erase v) := fun p =>
    ⟨p.2.val, by
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact (Finset.mem_erase.mp p.2.property).1⟩
  have hinj : Function.Injective f := by
    rintro ⟨⟨x,hx⟩,⟨y,hy⟩⟩ ⟨⟨x',hx'⟩,⟨y',hy'⟩⟩ he
    have hyy : y = y' := congrArg Subtype.val he
    subst y'
    have hyv : y ≠ v := (Finset.mem_erase.mp hy).1
    have hxx : x = x' := common_unique h4 hyv.symm
      ((mem_Nbr _ _ _).mp hx) ((mem_Nbr _ _ _).mp (Finset.mem_erase.mp hy).2).symm
      ((mem_Nbr _ _ _).mp hx') ((mem_Nbr _ _ _).mp (Finset.mem_erase.mp hy').2).symm
    subst x'
    rfl
  have hc := Fintype.card_le_of_injective f hinj
  have hT : Fintype.card T = ∑ x ∈ Nbr G v, ((Nbr G x).card - 1) := by
    dsimp only [T]
    rw [Fintype.card_sigma]
    simp only [Fintype.card_coe]
    rw [Finset.sum_coe_sort (Nbr G v) (fun x => ((Nbr G x).erase v).card)]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.card_erase_of_mem]
    exact (mem_Nbr _ _ _).mpr ((mem_Nbr _ _ _).mp hx).symm
  rw [hT] at hc
  simpa only [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ v),
    Finset.card_univ] using hc

theorem degree_count (h4 : ¬ HasC4 G) (d : ℕ)
    (hd : ∀ w, d ≤ (Nbr G w).card) (v : V) :
    (Nbr G v).card * (d-1) ≤ Fintype.card V - 1 := by
  classical
  have h := twoStep_count h4 v
  have hl : (Nbr G v).card * (d-1) ≤ ∑ x ∈ Nbr G v, ((Nbr G x).card-1) := by
    calc
      _ = ∑ _x ∈ Nbr G v, (d-1) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun x _ => Nat.sub_le_sub_right (hd x) 1)
  exact hl.trans h

/-- Equal-degree lemma needs only existence and uniqueness of common neighbors. -/
theorem nonadj_degree_eq (h4 : ¬ HasC4 G)
    (hc : ∀ a b : V, a ≠ b → ∃ x, G.Adj a x ∧ G.Adj b x)
    {u v : V} (huv : ¬ G.Adj u v) : (Nbr G u).card = (Nbr G v).card := by
  classical
  have hex : ∀ x, x ∈ Nbr G u → ∃ y, G.Adj x y ∧ G.Adj v y := by
    intro x hx
    have hxv : x ≠ v := fun h => huv (h ▸ (mem_Nbr _ _ _).mp hx)
    exact hc x v hxv
  choose f hf using hex
  apply Finset.card_bij f
  · intro x hx
    exact (mem_Nbr _ _ _).mpr (hf x hx).2
  · intro x hx y hy he
    have huf : u ≠ f x hx := fun h => huv (by simpa only [← h] using (hf x hx).2.symm)
    exact common_unique h4 huf ((mem_Nbr _ _ _).mp hx) (hf x hx).1.symm
      ((mem_Nbr _ _ _).mp hy) (by simpa only [he] using (hf y hy).1.symm)
  · intro y hy
    have hyu : y ≠ u := fun h => huv (by simpa only [h] using ((mem_Nbr _ _ _).mp hy).symm)
    obtain ⟨x,hxy,hxu⟩ := hc y u hyu
    have hx : x ∈ Nbr G u := (mem_Nbr _ _ _).mpr hxu
    refine ⟨x,hx, ?_⟩
    have hxv : x ≠ v := fun h => huv (h ▸ hxu)
    exact common_unique h4 hxv (hf x hx).1 (hf x hx).2 hxy.symm ((mem_Nbr _ _ _).mp hy)

theorem no_universal (h4 : ¬ HasC4 G) (hd : ∀ v, 3 ≤ (Nbr G v).card) (z : V) :
    ∃ x, x ≠ z ∧ ¬ G.Adj z x := by
  classical
  by_contra hn
  have hz : ∀ x, x ≠ z → G.Adj z x := by
    intro x hx
    by_contra h
    exact hn ⟨x,hx,h⟩
  have he : Nbr G z = Finset.univ.erase z := by
    ext x
    simp only [mem_Nbr,Finset.mem_erase,Finset.mem_univ,and_true]
    exact ⟨fun h => h.ne.symm, hz x⟩
  have hdz := hd z
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0 < (Nbr G z).card by omega)
  have hzx := (mem_Nbr _ _ _).mp hx
  have hp := degree_pair_bound h4 hzx.ne
  have hdx := hd x
  rw [he,Finset.card_erase_of_mem (Finset.mem_univ z),Finset.card_univ] at hp
  omega

theorem regular_of_common (h4 : ¬ HasC4 G)
    (hc : ∀ a b : V, a ≠ b → ∃ x, G.Adj a x ∧ G.Adj b x)
    (hd : ∀ v, 3 ≤ (Nbr G v).card) (u v : V) :
    (Nbr G u).card = (Nbr G v).card := by
  classical
  by_contra hdeg
  have he : ∀ a b : V, (Nbr G a).card ≠ (Nbr G b).card → G.Adj a b := by
    intro a b hab
    by_contra hn
    exact hab (nonadj_degree_eq h4 hc hn)
  obtain ⟨u',hu'u,hu'⟩ := no_universal h4 hd u
  obtain ⟨v',hv'v,hv'⟩ := no_universal h4 hd v
  have hdu := nonadj_degree_eq h4 hc hu'
  have hdv := nonadj_degree_eq h4 hc hv'
  apply h4
  refine ⟨u,u',v,v',hu'u.symm,hv'v.symm,he u v hdeg,?_,?_,?_⟩
  · apply he
    exact fun h => hdeg (h.trans hdv.symm)
  · apply he
    exact fun h => hdeg (hdu.trans h)
  · apply he
    exact fun h => hdeg (hdu.trans (h.trans hdv.symm))

/-- Coverage gives the reverse count when every distinct pair has a common neighbor. -/
theorem twoStep_cover
    (hc : ∀ a b : V, a ≠ b → ∃ x, G.Adj a x ∧ G.Adj b x) (v : V) :
    Fintype.card V - 1 ≤ (∑ x ∈ Nbr G v, ((Nbr G x).card - 1)) := by
  classical
  let T := Σ x : ↑(Nbr G v), ↑((Nbr G x.val).erase v)
  let f : T → ↑((Finset.univ : Finset V).erase v) := fun p =>
    ⟨p.2.val, by
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact (Finset.mem_erase.mp p.2.property).1⟩
  have hsur : Function.Surjective f := by
    intro y
    have hyv := (Finset.mem_erase.mp y.property).1
    obtain ⟨x,hvx,hyx⟩ := hc v y.val hyv.symm
    refine ⟨⟨⟨x,(mem_Nbr _ _ _).mpr hvx⟩,⟨y.val, ?_⟩⟩,rfl⟩
    exact Finset.mem_erase.mpr ⟨hyv,(mem_Nbr _ _ _).mpr hyx.symm⟩
  have hc' := Fintype.card_le_of_surjective f hsur
  have hT : Fintype.card T = ∑ x ∈ Nbr G v, ((Nbr G x).card - 1) := by
    dsimp only [T]
    rw [Fintype.card_sigma]
    simp only [Fintype.card_coe]
    rw [Finset.sum_coe_sort (Nbr G v) (fun x => ((Nbr G x).erase v).card)]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.card_erase_of_mem]
    exact (mem_Nbr _ _ _).mpr ((mem_Nbr _ _ _).mp hx).symm
  rw [hT] at hc'
  simpa only [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ v),
    Finset.card_univ] using hc'

/-- The exact weak friendship theorem needed here. Nonemptiness is essential. -/
theorem even_no_common [Nonempty V] (he : Even (Fintype.card V))
    (h4 : ¬ HasC4 G) (hd : ∀ v, 3 ≤ (Nbr G v).card) :
    ∃ x y, x ≠ y ∧ ∀ z, ¬ (G.Adj x z ∧ G.Adj y z) := by
  classical
  by_contra hn
  have hc : ∀ a b : V, a ≠ b → ∃ x, G.Adj a x ∧ G.Adj b x := by
    intro a b hab
    by_contra h
    exact hn ⟨a,b,hab,fun z hz => h ⟨z,hz⟩⟩
  let v : V := Classical.ofNonempty
  let d := (Nbr G v).card
  have hr : ∀ x, (Nbr G x).card = d := fun x => regular_of_common h4 hc hd x v
  have ht := le_antisymm (twoStep_count h4 v) (twoStep_cover hc v)
  have hsum : (∑ x ∈ Nbr G v, ((Nbr G x).card - 1)) = d*(d-1) := by
    simp only [hr, Finset.sum_const, smul_eq_mul, d]
  rw [hsum] at ht
  have hp := Nat.even_mul_pred_self d
  obtain ⟨k,hk⟩ := hp
  obtain ⟨j,hj⟩ := he
  have hpos : 0 < Fintype.card V := Fintype.card_pos
  omega

#print axioms twoStep_count
#print axioms degree_count
#print axioms nonadj_degree_eq
#print axioms regular_of_common
#print axioms even_no_common
end MultipartiteRamsey
```

### `RamseyHost.lean`

```lean
import RamseyFinite

open scoped Classical
set_option autoImplicit false
namespace MultipartiteRamsey

noncomputable def RelNbr {c s : ℕ} (G : SimpleGraph (Part c s)) (v : Part c s) : Finset (Part c s) :=
  Finset.univ.filter (fun w => v.1 ≠ w.1 ∧ ¬ G.Adj v w)

@[simp] theorem mem_RelNbr {c s : ℕ} (G : SimpleGraph (Part c s)) (v w : Part c s) :
    w ∈ RelNbr G v ↔ v.1 ≠ w.1 ∧ ¬ G.Adj v w := by simp [RelNbr]

theorem class_card {c s : ℕ} (v : Part c s) :
    (Finset.univ.filter (fun w : Part c s => v.1 = w.1)).card = s := by
  classical
  have he : Finset.univ.filter (fun w : Part c s => v.1 = w.1) =
      Finset.univ.image (fun t : Fin s => (v.1,t)) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      exact ⟨w.2, Prod.ext h rfl⟩
    · rintro ⟨t,ht⟩
      have he := congrArg (fun z : Part c s => z.1) ht
      exact he
  rw [he,Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)]
  simp

theorem degree_add_relNbr {c s : ℕ} {G : SimpleGraph (Part c s)}
    (hh : G ≤ Host c s) (v : Part c s) :
    (Nbr G v).card + (RelNbr G v).card + s = c*s := by
  classical
  let T := Finset.univ.filter (fun w : Part c s => v.1 ≠ w.1)
  have he : T = (Nbr G v) ∪ (RelNbr G v) := by
    ext w
    simp only [T,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union,
      mem_Nbr,mem_RelNbr]
    constructor
    · intro h
      by_cases ha : G.Adj v w
      · exact Or.inl ha
      · exact Or.inr ⟨h,ha⟩
    · rintro (h | h)
      · exact hh h
      · exact h.1
  have hdis : Disjoint (Nbr G v) (RelNbr G v) := by
    apply Finset.disjoint_left.mpr
    intro w hw hb
    exact ((mem_RelNbr _ _ _).mp hb).2 ((mem_Nbr _ _ _).mp hw)
  have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Part c s)))
    (fun w => v.1 = w.1)
  rw [class_card] at hc
  change s + T.card = _ at hc
  rw [he,Finset.card_union_of_disjoint hdis] at hc
  simp only [Finset.card_univ,Fintype.card_prod,Fintype.card_fin] at hc
  omega

theorem adj_of_no_star_one {c s : ℕ} {G : SimpleGraph (Part c s)}
    (hn : ¬ HasStarInRelCompl c s 1 G) (v w : Part c s) (hvw : v.1 ≠ w.1) : G.Adj v w := by
  classical
  by_contra h
  apply hn
  refine ⟨v,Finset.one_le_card.mpr ⟨w,?_⟩⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvw,h⟩

theorem ramseyProp_two_one (s : ℕ) (hs : 2 ≤ s) : RamseyProp s 1 2 := by
  classical
  refine ⟨by omega, ?_⟩
  intro G _
  by_cases hstar : HasStarInRelCompl 2 s 1 G
  · exact Or.inr hstar
  left
  let t0 : Fin s := ⟨0,by omega⟩
  let t1 : Fin s := ⟨1,by omega⟩
  have ht : t0 ≠ t1 := by
    intro h
    have := congrArg Fin.val h
    simp only [t0,t1] at this
    omega
  refine ⟨(0,t0),(0,t1),(1,t0),(1,t1),?_,?_,?_,?_,?_,?_⟩
  · exact fun h => ht (congrArg Prod.snd h)
  · exact fun h => ht (congrArg Prod.snd h)
  all_goals exact adj_of_no_star_one hstar _ _ (by change (0 : Fin 2) ≠ 1; decide)

theorem M_one (s : ℕ) (hs : 2 ≤ s) : M s 1 = 2 := by
  have hu := M_le (ramseyProp_two_one s hs)
  have hl := M_ge_two s 1 (by omega) (by omega)
  omega

#print axioms degree_add_relNbr
#print axioms ramseyProp_two_one
#print axioms M_one
end MultipartiteRamsey
```

### `RamseyTransport.lean`

```lean
import RamseyRepair
import RamseyHost

open scoped Classical
set_option autoImplicit false
namespace MultipartiteRamsey

noncomputable def retain {c s : ℕ} (e : Part (c+1) s ≃ Part (c+1) s)
    (i : Fin (c+1)) (v : Part c s) : Part (c+1) s := e (i.succAbove v.1,v.2)

theorem retain_injective {c s : ℕ} (e : Part (c+1) s ≃ Part (c+1) s)
    (i : Fin (c+1)) : Function.Injective (retain e i) := by
  intro u v h
  have he := e.injective h
  have h1 := congrArg (fun w : Part (c+1) s => w.1) he
  have h2 := congrArg (fun w : Part (c+1) s => w.2) he
  exact Prod.ext (Fin.succAbove_right_injective h1) h2

theorem retain_survivor {c s : ℕ} (e : Part (c+1) s ≃ Part (c+1) s)
    (i : Fin (c+1)) (v : Part c s) : (e.symm (retain e i v)).1 ≠ i := by
  simpa only [retain,Equiv.symm_apply_apply] using Fin.succAbove_ne i v.1

theorem restrict_host {c s : ℕ} {G : SimpleGraph (Part (c+1) s)}
    (e : Part (c+1) s ≃ Part (c+1) s) (i : Fin (c+1))
    (hi : ∀ j x y, j ≠ i → ¬ G.Adj (e (j,x)) (e (j,y))) :
    G.comap (retain e i) ≤ Host c s := by
  rintro ⟨j,x⟩ ⟨k,y⟩ h
  change j ≠ k
  intro he
  subst k
  exact hi (i.succAbove j) x y (Fin.succAbove_ne i j) h

theorem restrict_noC4 {c s : ℕ} {G : SimpleGraph (Part (c+1) s)}
    (h4 : ¬ HasC4 G) (e : Part (c+1) s ≃ Part (c+1) s) (i : Fin (c+1)) :
    ¬ HasC4 (G.comap (retain e i)) := by
  intro h
  exact h4 (hasC4_of_injective (retain e i) (retain_injective e i) (fun _ _ h => h) h)

/-- Every survivor loses at most s-1 neighbors, proved on the literal host types. -/
theorem restrict_degree {c s : ℕ} {G : SimpleGraph (Part (c+1) s)}
    (e : Part (c+1) s ≃ Part (c+1) s) (i : Fin (c+1))
    (hm : ∀ w, (e.symm w).1 ≠ i → ∃ t, ¬ G.Adj w (e (i,t)))
    (v : Part c s) :
    (Nbr G (retain e i v)).card ≤
      (Nbr (G.comap (retain e i)) v).card + (s-1) := by
  classical
  obtain ⟨t,ht⟩ := hm (retain e i v) (retain_survivor e i v)
  let A := (Nbr (G.comap (retain e i)) v).image (retain e i)
  let B := ((Finset.univ : Finset (Fin s)).erase t).image (fun u => e (i,u))
  have hcover : Nbr G (retain e i v) ⊆ A ∪ B := by
    intro w hw
    have hadj := (mem_Nbr _ _ _).mp hw
    by_cases he : (e.symm w).1 = i
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨(e.symm w).2, ?_, ?_⟩
      · apply Finset.mem_erase.mpr
        refine ⟨?_,Finset.mem_univ _⟩
        intro het
        have hew : e (i,t) = w := by
          rw [← het,← he]
          exact e.apply_symm_apply w
        exact ht (hew.symm ▸ hadj)
      · rw [← he]
        exact e.apply_symm_apply w
    · obtain ⟨j,hj⟩ := Fin.exists_succAbove_eq he
      have hew : retain e i (j,(e.symm w).2) = w := by
        simp only [retain,hj,Prod.eta,Equiv.apply_symm_apply]
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨(j,(e.symm w).2), ?_,hew⟩
      apply (mem_Nbr _ _ _).mpr
      change G.Adj (retain e i v) (retain e i (j,(e.symm w).2))
      rwa [hew]
  have hA : A.card ≤ (Nbr (G.comap (retain e i)) v).card := Finset.card_image_le
  have hB : B.card ≤ s-1 := by
    have hc := Finset.card_image_le (s := (Finset.univ : Finset (Fin s)).erase t)
      (f := fun u => e (i,u))
    simpa only [Finset.card_erase_of_mem (Finset.mem_univ t),Finset.card_univ,
      Fintype.card_fin] using hc
  have hc := Finset.card_le_card hcover
  have hu := Finset.card_union_le A B
  omega

theorem step_large {s n c : ℕ} (hs : 3 ≤ s) (hn : 2 ≤ n)
    (hp : RamseyProp s n c) : RamseyProp s (n+1) (c+1) := by
  classical
  refine ⟨by omega, ?_⟩
  intro G hh
  by_cases h4 : HasC4 G
  · exact Or.inl h4
  right
  by_contra hstar
  let i : Fin (c+1) := ⟨0,by omega⟩
  obtain ⟨e,hi,hm⟩ := repair_large hs h4 hh i
  let H := G.comap (retain e i)
  have hhH : H ≤ Host c s := restrict_host e i hi
  have h4H : ¬ HasC4 H := restrict_noC4 h4 e i
  rcases hp.2 H hhH with h | h
  · exact h4H h
  obtain ⟨v,hv⟩ := h
  have hD := degree_add_relNbr hhH v
  have hL := restrict_degree e i hm v
  have hG := host_degree_lower (show 1 ≤ n+1 by omega) hstar (retain e i v)
  change n ≤ (RelNbr H v).card at hv
  change (Nbr G (retain e i v)).card ≤ (Nbr H v).card + (s-1) at hL
  have hs1 : s-1+1=s := by omega
  simp only [Nat.add_sub_cancel] at hG
  nlinarith

theorem conj_2_3_large (s n : ℕ) (hs : 3 ≤ s) (hn : 2 ≤ n) :
    M s (n+1) ≤ M s n + 1 := by
  exact M_le (step_large hs hn (M_spec s n (by omega) (by omega)))

#print axioms retain_injective
#print axioms restrict_host
#print axioms restrict_noC4
#print axioms restrict_degree
#print axioms step_large
#print axioms conj_2_3_large
end MultipartiteRamsey
```

### `RamseyPairingEquiv.lean`

```lean
import RamseyMatching

open scoped Classical
set_option autoImplicit false
namespace MultipartiteRamsey

variable {V : Type*} [Fintype V]

/-- A fixed-point-free involution canonically gives equal-size two-element classes. -/
theorem pairing_equiv (f : Pairing V) (c : ℕ) (hc : Fintype.card V = c*2) :
    ∃ e : Part c 2 ≃ V, ∀ i, e (i,1) = f.val (e (i,0)) := by
  classical
  let code := Fintype.equivFin V
  let L := {v : V // code v < code (f.val v)}
  let toV : L × Fin 2 → V := fun p => if p.2 = 0 then p.1.val else f.val p.1.val
  have hinj : Function.Injective toV := by
    rintro ⟨a,i⟩ ⟨b,j⟩ h
    have ha := a.property
    have hb := b.property
    fin_cases i <;> fin_cases j
    · have he : a.val = b.val := by simpa [toV] using h
      exact Prod.ext (Subtype.ext he) rfl
    · have he : a.val = f.val b.val := by simpa [toV] using h
      rw [he,f.property.1] at ha
      exact (lt_asymm ha hb).elim
    · have he : f.val a.val = b.val := by simpa [toV] using h
      rw [← he,f.property.1] at hb
      exact (lt_asymm ha hb).elim
    · have he : f.val a.val = f.val b.val := by simpa [toV] using h
      exact Prod.ext (Subtype.ext (f.property.1.injective he)) rfl
  have hsur : Function.Surjective toV := by
    intro v
    by_cases hlt : code v < code (f.val v)
    · exact ⟨(⟨v,hlt⟩,0),by simp only [toV,ite_true]⟩
    · have hne : code v ≠ code (f.val v) := fun h => f.property.2 v (code.injective h).symm
      have hgt : code (f.val v) < code v := lt_of_le_of_ne (le_of_not_gt hlt) hne.symm
      refine ⟨(⟨f.val v, ?_⟩,1), ?_⟩
      · rwa [f.property.1]
      · simpa [toV] using f.property.1 v
  let E : L × Fin 2 ≃ V := Equiv.ofBijective toV ⟨hinj,hsur⟩
  have hL : Fintype.card L = c := by
    have h := Fintype.card_congr E
    simp only [Fintype.card_prod,Fintype.card_fin] at h
    omega
  let d : Fin c ≃ L := Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using hL.symm)
  let e : Part c 2 ≃ V := (Equiv.prodCongr d (Equiv.refl (Fin 2))).trans E
  refine ⟨e,?_⟩
  intro i
  change toV (d i,1) = f.val (toV (d i,0))
  simp [toV]

/-- Pair labels transport ordinary-complement edges to independent host classes. -/
theorem independent_pair_equiv (G : SimpleGraph V) (f : Pairing V)
    (hf : ∀ v, ¬ G.Adj v (f.val v)) (c : ℕ) (hc : Fintype.card V = c*2) :
    ∃ e : Part c 2 ≃ V, ∀ i x y, ¬ G.Adj (e (i,x)) (e (i,y)) := by
  classical
  obtain ⟨e,he⟩ := pairing_equiv f c hc
  refine ⟨e,?_⟩
  intro i x y
  fin_cases x <;> fin_cases y
  · exact G.irrefl
  · change ¬ G.Adj (e (i,0)) (e (i,1))
    rw [he]
    exact hf _
  · change ¬ G.Adj (e (i,1)) (e (i,0))
    rw [he]
    exact fun h => hf _ h.symm
  · exact G.irrefl

#print axioms pairing_equiv
#print axioms independent_pair_equiv
end MultipartiteRamsey
```

### `RamseyPairs.lean`

```lean
import RamseyFriendship
import RamseyPairingEquiv
import RamseyTransport

open scoped Classical
set_option autoImplicit false
namespace MultipartiteRamsey

variable {V : Type*} [Fintype V]

abbrev EraseTwo (x y : V) := {z : V // z ≠ x ∧ z ≠ y}

theorem eraseTwo_card {x y : V} [Fintype (EraseTwo x y)] (hxy : x ≠ y) :
    Fintype.card (EraseTwo x y) = Fintype.card V - 2 := by
  classical
  rw [Fintype.card_of_subtype ((Finset.univ.erase x).erase y) (by
    intro z
    simp only [Finset.mem_erase,Finset.mem_univ,and_true]
    exact and_comm)]
  rw [Finset.card_erase_of_mem (by simp [hxy.symm]),
    Finset.card_erase_of_mem (Finset.mem_univ x),Finset.card_univ]
  omega

theorem nbr_card_degree (G : SimpleGraph V) (v : V) : (Nbr G v).card = G.degree v := by
  classical
  unfold SimpleGraph.degree
  congr 1
  ext w
  simp

theorem comap_degree_le {W : Type*} [Fintype W] (G : SimpleGraph V)
    (f : W → V) (hf : Function.Injective f) (v : W) :
    (Nbr (G.comap f) v).card ≤ (Nbr G (f v)).card := by
  classical
  have he : (Nbr (G.comap f) v).image f ⊆ Nbr G (f v) := by
    intro w hw
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hw
    exact (mem_Nbr G (f v) (f x)).mpr ((mem_Nbr (G.comap f) v x).mp hx)
  have hc := Finset.card_le_card he
  rwa [Finset.card_image_of_injective _ hf] at hc

/-- The analytic bound used by the complement matching, for every vertex. -/
theorem degree_twice_bound [Nonempty V] (he : Even (Fintype.card V))
    {G : SimpleGraph V} (h4 : ¬ HasC4 G) (hd : ∀ v, 4 ≤ (Nbr G v).card) :
    14 ≤ Fintype.card V ∧ ∀ v, 2*(Nbr G v).card ≤ Fintype.card V - 4 := by
  classical
  let v : V := Classical.ofNonempty
  have hv := degree_count h4 4 hd v
  have hv4 := hd v
  have hN : 14 ≤ Fintype.card V := by
    obtain ⟨k,hk⟩ := he
    norm_num only [Nat.reduceSub] at hv
    omega
  refine ⟨hN,?_⟩
  intro w
  have hw := degree_count h4 4 hd w
  norm_num only [Nat.reduceSub] at hw
  omega

/-- Delete a no-common-neighbor pair; the survivor complement has a perfect matching. -/
theorem pair_delete_matching [Nonempty V] (he : Even (Fintype.card V))
    {G : SimpleGraph V} (h4 : ¬ HasC4 G) (hd : ∀ v, 4 ≤ (Nbr G v).card) :
    ∃ x y : V, x ≠ y ∧ (∀ z, ¬ (G.Adj x z ∧ G.Adj y z)) ∧
      ∃ f : Pairing (EraseTwo x y), ∀ z, ¬ G.Adj z.val (f.val z).val := by
  classical
  obtain ⟨x,y,hxy,hcommon⟩ := even_no_common he h4 (fun v => (by have := hd v; omega))
  let R := EraseTwo x y
  let H : SimpleGraph R := G.comap Subtype.val
  have hcard : Fintype.card R = Fintype.card V - 2 := eraseTwo_card hxy
  obtain ⟨hN,hbound⟩ := degree_twice_bound he h4 hd
  have heR : Even (Fintype.card R) := by
    obtain ⟨k,hk⟩ := he
    refine ⟨k-1,?_⟩
    omega
  have hmin : ∀ z : R, Fintype.card R ≤ 2*(Nbr Hᶜ z).card := by
    intro z
    have hle := comap_degree_le G (Subtype.val : R → V) Subtype.val_injective z
    have hb := hbound z.val
    have hc : (Nbr Hᶜ z).card = Fintype.card R - 1 - (Nbr H z).card := by
      simp only [nbr_card_degree,SimpleGraph.degree_compl]
      rfl
    rw [hc]
    change (Nbr H z).card ≤ (Nbr G z.val).card at hle
    omega
  obtain ⟨f,hfi,hfe⟩ := dense_matching Hᶜ heR hmin
  refine ⟨x,y,hxy,hcommon,⟨f,hfi,?_⟩,?_⟩
  · intro z h
    exact (hfe z).ne h.symm
  · intro z
    exact (hfe z).2

/-- A pair with no common neighbor costs each survivor at most one edge. -/
theorem pair_delete_degree {G : SimpleGraph V} {x y : V} [Fintype (EraseTwo x y)]
    (hc : ∀ z, ¬ (G.Adj x z ∧ G.Adj y z)) (v : EraseTwo x y) :
    (Nbr G v.val).card ≤ (Nbr (G.comap (Subtype.val : EraseTwo x y → V)) v).card + 1 := by
  classical
  let H := G.comap (Subtype.val : EraseTwo x y → V)
  let A := (Nbr H v).image Subtype.val
  let B := (Finset.univ.filter (fun z => (z = x ∨ z = y) ∧ G.Adj v.val z))
  have hB : B.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    rcases ha'.1 with rfl | rfl <;> rcases hb'.1 with rfl | rfl
    · rfl
    · exact (hc v.val ⟨ha'.2.symm,hb'.2.symm⟩).elim
    · exact (hc v.val ⟨hb'.2.symm,ha'.2.symm⟩).elim
    · rfl
  have hcov : Nbr G v.val ⊆ A ∪ B := by
    intro w hw
    by_cases hx : w = x
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        Or.inl hx,(mem_Nbr G v.val w).mp hw⟩)
    by_cases hy : w = y
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        Or.inr hy,(mem_Nbr G v.val w).mp hw⟩)
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    exact ⟨⟨w,hx,hy⟩,(mem_Nbr H v _).mpr ((mem_Nbr G v.val w).mp hw),rfl⟩
  have hA : A.card = (Nbr H v).card := Finset.card_image_of_injective _ Subtype.val_injective
  change (Nbr G v.val).card ≤ (Nbr H v).card + 1
  have hle := Finset.card_le_card hcov
  have hu := Finset.card_union_le A B
  omega

theorem comap_degree_equiv {W : Type*} [Fintype W] (G : SimpleGraph V)
    (e : W ≃ V) (v : W) : (Nbr (G.comap e) v).card = (Nbr G (e v)).card := by
  classical
  apply Finset.card_bij (fun w _ => e w)
  · intro w hw
    exact (mem_Nbr G (e v) (e w)).mpr ((mem_Nbr (G.comap e) v w).mp hw)
  · intro a _ b _ h
    exact e.injective h
  · intro w hw
    refine ⟨e.symm w,?_,e.apply_symm_apply w⟩
    apply (mem_Nbr (G.comap e) v _).mpr
    change G.Adj (e v) (e (e.symm w))
    rw [e.apply_symm_apply]
    exact (mem_Nbr G (e v) w).mp hw

/-- Full repair into the literal smaller host, including all transport bridges. -/
theorem repair_pairs {c : ℕ} {G : SimpleGraph (Part (c+1) 2)}
    (h4 : ¬ HasC4 G) (hd : ∀ v, 4 ≤ (Nbr G v).card) :
    ∃ f : Part c 2 ↪ Part (c+1) 2,
      G.comap f ≤ Host c 2 ∧ ¬ HasC4 (G.comap f) ∧
      ∀ v, (Nbr G (f v)).card ≤ (Nbr (G.comap f) v).card + 1 := by
  classical
  have he : Even (Fintype.card (Part (c+1) 2)) := by
    refine ⟨c+1,?_⟩
    simp only [Fintype.card_prod,Fintype.card_fin]
    omega
  obtain ⟨x,y,hxy,hcommon,f,hf⟩ := pair_delete_matching he h4 hd
  let R := EraseTwo x y
  let H : SimpleGraph R := G.comap Subtype.val
  have hc : Fintype.card R = c*2 := by
    dsimp only [R]
    rw [eraseTwo_card hxy]
    simp only [Fintype.card_prod,Fintype.card_fin]
    omega
  obtain ⟨e,hi⟩ := independent_pair_equiv H f hf c hc
  let q : Part c 2 ↪ Part (c+1) 2 :=
    ⟨fun v => (e v).val, fun _ _ h => e.injective (Subtype.ext h)⟩
  refine ⟨q,?_,?_,?_⟩
  · rintro ⟨j,a⟩ ⟨k,b⟩ h
    change j ≠ k
    intro heq
    subst k
    exact hi j a b h
  · intro h
    exact h4 (hasC4_of_injective q q.injective (fun _ _ h => h) h)
  · intro v
    have hl := pair_delete_degree hcommon (e v)
    change (Nbr G (q v)).card ≤ (Nbr (H.comap e) v).card + 1
    rw [comap_degree_equiv]
    exact hl

theorem step_pairs_high {c n : ℕ} (hn : 2 ≤ n) (hD : n+4 ≤ 2*c)
    (hp : RamseyProp 2 n c) : RamseyProp 2 (n+1) (c+1) := by
  classical
  refine ⟨by omega,?_⟩
  intro G _
  by_cases h4 : HasC4 G
  · exact Or.inl h4
  right
  by_contra hstar
  have hd : ∀ v, 4 ≤ (Nbr G v).card := by
    intro v
    have hl := host_degree_lower (show 1 ≤ n+1 by omega) hstar v
    simp only [Nat.add_sub_cancel] at hl
    omega
  obtain ⟨f,hh,h4H,hdeg⟩ := repair_pairs h4 hd
  rcases hp.2 (G.comap f) hh with h | ⟨v,hv⟩
  · exact h4H h
  · have hcount := degree_add_relNbr hh v
    change n ≤ (RelNbr (G.comap f) v).card at hv
    have hl := hdeg v
    have hG := host_degree_lower (show 1 ≤ n+1 by omega) hstar (f v)
    simp only [Nat.add_sub_cancel] at hG
    omega

#print axioms degree_twice_bound
#print axioms pair_delete_matching
#print axioms pair_delete_degree
#print axioms repair_pairs
#print axioms step_pairs_high
end MultipartiteRamsey
```

### `RamseySmall.lean`

```lean
import RamseyPairs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination

open scoped Classical
set_option autoImplicit false
namespace MultipartiteRamsey

section RingCycle
variable {R : Type*} [CommRing R]

def RingCycle (h1 : (1 : R) ≠ 0) : SimpleGraph R where
  Adj u v := v = u+1 ∨ u = v+1
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by
    intro u h
    rcases h with h | h
    all_goals
      apply h1
      have hh : u+1 = u+0 := by simpa only [add_zero] using h.symm
      exact add_left_cancel hh⟩

theorem ringCycle_noC4 (h1 : (1 : R) ≠ 0) (h4 : (4 : R) ≠ 0) :
    ¬ HasC4 (RingCycle h1) := by
  rintro ⟨a,b,x,y,hab,hxy,hax,hay,hbx,hby⟩
  change (x = a+1 ∨ a = x+1) at hax
  change (y = a+1 ∨ a = y+1) at hay
  change (x = b+1 ∨ b = x+1) at hbx
  change (y = b+1 ∨ b = y+1) at hby
  rcases hax with hax | hax
  · rcases hbx with hbx | hbx
    · exact hab (add_right_cancel (hax.symm.trans hbx))
    · rcases hay with hay | hay
      · exact hxy (hax.trans hay.symm)
      · rcases hby with hby | hby
        · apply h4
          linear_combination -hax - hbx - hay - hby
        · exact hxy (add_right_cancel (hbx.symm.trans hby))
  · rcases hbx with hbx | hbx
    · rcases hay with hay | hay
      · rcases hby with hby | hby
        · exact hxy (hbx.trans hby.symm)
        · apply h4
          linear_combination -hax - hbx - hay - hby
      · exact hxy (add_right_cancel (hax.symm.trans hay))
    · exact hab (hax.trans hbx.symm)

theorem ringCycle_degree [Fintype R] (h1 : (1 : R) ≠ 0) (h2 : (2 : R) ≠ 0) (v : R) :
    (Nbr (RingCycle h1) v).card = 2 := by
  classical
  have he : Nbr (RingCycle h1) v = {v+1,v-1} := by
    ext w
    simp only [mem_Nbr,Finset.mem_insert,Finset.mem_singleton]
    change (w=v+1 ∨ v=w+1) ↔ (w=v+1 ∨ w=v-1)
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · right
        linear_combination -h
    · rintro (h | h)
      · exact Or.inl h
      · right
        linear_combination -h
  rw [he,Finset.card_pair]
  have hne : v+1 ≠ v-1 := by
    intro h
    apply h2
    linear_combination h
  exact hne
end RingCycle

/-- The 2c-cycle, paired by antipodal points, is a counterexample at low D. -/
theorem small_pair_cycle (c n : ℕ) (hc : 3 ≤ c) (_hn : 2 ≤ n) (hD : 2*c ≤ n+3) :
    ¬ RamseyProp 2 n c := by
  classical
  let N := c*2
  let Z := ZMod N
  let _ : NeZero N := ⟨by dsimp [N]; omega⟩
  have hval : ∀ k : ℕ, 0 < k → k < N → (k : Z) ≠ 0 := by
    intro k hk0 hk hz
    have hh := congrArg ZMod.val hz
    rw [ZMod.val_natCast_of_lt hk,ZMod.val_zero] at hh
    omega
  have h1 : (1 : Z) ≠ 0 := by
    simpa only [Nat.cast_one] using hval 1 (by omega) (by dsimp [N]; omega)
  have h2 : (2 : Z) ≠ 0 := hval 2 (by omega) (by dsimp [N]; omega)
  have h4 : (4 : Z) ≠ 0 := hval 4 (by omega) (by dsimp [N]; omega)
  have hc0 : (c : Z)+(c : Z)=0 := by
    simpa [N,mul_two] using ZMod.natCast_self N
  let f : Pairing Z := ⟨fun v => v+c, (by
    intro v
    dsimp only
    linear_combination hc0), (by
    intro v h
    apply hval c (by omega) (by dsimp [N]; omega)
    linear_combination h)⟩
  let G := RingCycle h1
  have hf : ∀ v, ¬ G.Adj v (f.val v) := by
    intro v ha
    change (v+c=v+1 ∨ v=(v+c)+1) at ha
    rcases ha with ha | ha
    · have he : (c : Z) = 1 := add_left_cancel ha
      have hh := congrArg ZMod.val he
      rw [ZMod.val_natCast_of_lt (show c < N by dsimp [N]; omega),
        ZMod.val_one'' (show N ≠ 1 by dsimp [N]; omega)] at hh
      omega
    · apply hval (c+1) (by omega) (by dsimp [N]; omega)
      push_cast
      linear_combination -ha
  have hcard : Fintype.card Z = c*2 := by
    dsimp only [Z]
    rw [ZMod.card]
  obtain ⟨e,hi⟩ := independent_pair_equiv G f hf c hcard
  let H := G.comap e
  have hh : H ≤ Host c 2 := by
    rintro ⟨j,a⟩ ⟨k,b⟩ ha
    change j ≠ k
    intro he
    subst k
    exact hi j a b ha
  have hfree : ¬ HasC4 H := by
    intro h
    exact ringCycle_noC4 h1 h4 (hasC4_of_injective e e.injective (fun _ _ h => h) h)
  have hdeg : ∀ v, (Nbr H v).card = 2 := by
    intro v
    rw [comap_degree_equiv]
    exact ringCycle_degree h1 h2 _
  rintro ⟨_,hp⟩
  rcases hp H hh with h | ⟨v,hv⟩
  · exact hfree h
  · have ht := degree_add_relNbr hh v
    change n ≤ (RelNbr H v).card at hv
    rw [hdeg] at ht
    omega

def SmallMatching : SimpleGraph (Part 2 2) where
  Adj u v := u.1 ≠ v.1 ∧ u.2 = v.2
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem small_matching_degree (v : Part 2 2) : (Nbr SmallMatching v).card = 1 := by
  classical
  let w : Part 2 2 := (if v.1=0 then 1 else 0,v.2)
  have he : Nbr SmallMatching v = {w} := by
    ext u
    simp only [mem_Nbr,Finset.mem_singleton]
    change (v.1 ≠ u.1 ∧ v.2 = u.2) ↔ u=w
    constructor
    · rintro ⟨hne,hsame⟩
      apply Prod.ext
      · dsimp only [w]
        split_ifs <;> omega
      · exact hsame.symm
    · rintro rfl
      refine ⟨?_,rfl⟩
      dsimp only [w]
      split_ifs <;> omega
  rw [he,Finset.card_singleton]

theorem small_matching_noC4 : ¬ HasC4 SmallMatching := by
  classical
  rintro ⟨a,b,x,y,_,hxy,hax,hay,_⟩
  have hcard : (Nbr SmallMatching a).card ≤ 1 := (small_matching_degree a).le
  exact hxy (Finset.card_le_one.mp hcard x ((mem_Nbr _ _ _).mpr hax) y ((mem_Nbr _ _ _).mpr hay))

theorem not_ramseyProp_two_two (n : ℕ) (hn : 2 ≤ n) : ¬ RamseyProp 2 n 2 := by
  classical
  rintro ⟨_,hp⟩
  have hh : SmallMatching ≤ Host 2 2 := fun _ _ h => h.1
  rcases hp SmallMatching hh with h | ⟨v,hv⟩
  · exact small_matching_noC4 h
  · have hc := degree_add_relNbr hh v
    rw [small_matching_degree] at hc
    change n ≤ (RelNbr SmallMatching v).card at hv
    omega

theorem small_pair_counterexample (c n : ℕ) (hc : 2 ≤ c) (hn : 2 ≤ n)
    (hD : 2*c ≤ n+3) : ¬ RamseyProp 2 n c := by
  by_cases hc2 : c=2
  · subst c
    exact not_ramseyProp_two_two n hn
  · exact small_pair_cycle c n (by omega) hn hD

#print axioms ringCycle_noC4
#print axioms ringCycle_degree
#print axioms small_pair_cycle
#print axioms small_pair_counterexample
end MultipartiteRamsey
```

### `RamseyConjecture.lean`

```lean
import RamseySmall

set_option autoImplicit false
namespace MultipartiteRamsey

theorem step_pairs {n c : ℕ} (hn : 2 ≤ n) (hp : RamseyProp 2 n c) :
    RamseyProp 2 (n+1) (c+1) := by
  have hc : 2 ≤ c := by
    have hpos := hp.1
    have hne : c ≠ 1 := fun he => not_ramseyProp_one 2 n (by omega) (he ▸ hp)
    omega
  by_cases hD : n+4 ≤ 2*c
  · exact step_pairs_high hn hD hp
  · exact (small_pair_counterexample c n hc hn (by omega) hp).elim

theorem step {s n c : ℕ} (hs : 2 ≤ s) (hn : 2 ≤ n) (hp : RamseyProp s n c) :
    RamseyProp s (n+1) (c+1) := by
  by_cases hs2 : s=2
  · subst s
    exact step_pairs hn hp
  · exact step_large (by omega) hn hp

/-- Gonçalves–Monte Carmelo–Nakaoka, Conjecture 2.3, in its full source range. -/
theorem conj_2_3 (s n : ℕ) (hs : 2 ≤ s) (hn : 2 ≤ n) :
    M s (n+1) ≤ M s n + 1 := by
  exact M_le (step hs hn (M_spec s n (by omega) (by omega)))

#check Host
#check HasC4
#check HasStarInRelCompl
#check RamseyProp
#check M
#check ramseyProp_exists
#check M_spec
#check M_ge_two
#check M_one
#check repair_large
#check dense_matching
#check even_no_common
#check repair_pairs
#check small_pair_counterexample
#check step
#check conj_2_3
#print axioms Host
#print axioms HasC4
#print axioms HasStarInRelCompl
#print axioms RamseyProp
#print axioms M
#print axioms ramseyProp_exists
#print axioms M_spec
#print axioms M_ge_two
#print axioms M_one
#print axioms repair_large
#print axioms dense_matching
#print axioms even_no_common
#print axioms repair_pairs
#print axioms small_pair_counterexample
#print axioms step
#print axioms conj_2_3
#eval Lean.versionString
end MultipartiteRamsey
```
