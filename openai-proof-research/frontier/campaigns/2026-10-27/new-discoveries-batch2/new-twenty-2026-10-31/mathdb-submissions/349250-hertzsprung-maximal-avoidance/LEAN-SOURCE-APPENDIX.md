# Lean source appendix

Modules are listed in import order.

## HzCore.lean

```lean
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

namespace Hertzsprung

open Finset
open scoped BigOperators Classical
noncomputable section

def HOcc {n k : ℕ} (π : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin k)) (s : ℕ) : Prop :=
  ∃ h : s + k ≤ n, ∃ c : ℤ, ∀ i : Fin k,
    ((π ⟨s + i, by have := i.isLt; omega⟩ : ℕ) : ℤ) = ((τ i : ℕ) : ℤ) + c

def avoidCount (n k : ℕ) (τ : Equiv.Perm (Fin k)) : ℕ :=
  (univ.filter (fun π : Equiv.Perm (Fin n) => ∀ s, ¬ HOcc π τ s)).card

def ClaessonConjecture313 : Prop :=
  ∀ (k n : ℕ) (τ : Equiv.Perm (Fin k)), avoidCount n k τ ≤ avoidCount n k (Equiv.refl _)

def loc {n k s : ℕ} (h : s+k ≤ n) (i : Fin k) : Fin n :=
  ⟨s+i, by have := i.isLt; omega⟩

def block (n s k : ℕ) : Finset (Fin n) :=
  univ.filter (fun i => s ≤ (i : ℕ) ∧ (i : ℕ) < s+k)

@[simp] theorem mem_block {n s k : ℕ} {i : Fin n} :
    i ∈ block n s k ↔ s ≤ (i : ℕ) ∧ (i : ℕ) < s+k := by simp [block]

theorem loc_injective {n k s : ℕ} (h : s+k ≤ n) : Function.Injective (loc h) := by
  intro a b e
  have := congrArg Fin.val e
  change s+(a:ℕ) = s+(b:ℕ) at this
  exact Fin.ext (by omega)

def blockEquiv {n k s : ℕ} (h : s+k ≤ n) : Fin k ≃ {x // x ∈ block n s k} :=
  Equiv.ofBijective (fun i => ⟨loc h i, by rw [mem_block]; change s ≤ s+(i:ℕ) ∧ s+(i:ℕ) < s+k; have := i.isLt; omega⟩)
    ⟨fun _ _ e => loc_injective h (congrArg Subtype.val e), by
      intro x
      have hx := mem_block.mp x.property
      refine ⟨⟨(x.val : ℕ)-s, by omega⟩, Subtype.ext (Fin.ext ?_)⟩
      change s+((x.val : ℕ)-s) = (x.val : ℕ)
      omega⟩

theorem card_block {n s k : ℕ} (h : s+k ≤ n) : (block n s k).card = k := by
  rw [← Fintype.card_coe, ← Fintype.card_congr (blockEquiv h), Fintype.card_fin]

def At {n k : ℕ} (π : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin k)) (s c : ℕ) : Prop :=
  ∃ (hs : s+k ≤ n) (hc : c+k ≤ n), ∀ i, π (loc hs i) = loc hc (τ i)

theorem hOcc_iff_at {n k s : ℕ} (hk : 0 < k)
    (π : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin k)) :
    HOcc π τ s ↔ ∃ c, At π τ s c := by
  constructor
  · rintro ⟨hs,c,h⟩
    have h₀ := h (τ.symm ⟨0,hk⟩)
    have h₁ := h (τ.symm ⟨k-1,by omega⟩)
    simp only [Equiv.apply_symm_apply, Fin.val_mk] at h₀ h₁
    have hb := (π ⟨s+(τ.symm ⟨k-1,by omega⟩ : Fin k).val, by
      have := (τ.symm ⟨k-1,by omega⟩ : Fin k).isLt
      omega⟩).isLt
    have hc : c.toNat + k ≤ n := by omega
    refine ⟨c.toNat,hs,hc,fun i => Fin.ext ?_⟩
    have hi := h i
    change (π (loc hs i)).val = c.toNat + (τ i).val
    change ((π (loc hs i)).val : ℤ) = _ at hi
    omega
  · rintro ⟨c,hs,hc,h⟩
    refine ⟨hs,c,fun i => ?_⟩
    have hi := congrArg Fin.val (h i)
    change (π (loc hs i)).val = c+(τ i).val at hi
    change ((π (loc hs i)).val : ℤ) = _
    omega

theorem at_unique {n k s c c' : ℕ} {π : Equiv.Perm (Fin n)} {τ : Equiv.Perm (Fin k)}
    (hk : 0 < k) (h : At π τ s c) (h' : At π τ s c') : c = c' := by
  obtain ⟨hs,hc,h⟩ := h
  obtain ⟨_,hc',h'⟩ := h'
  have he := congrArg Fin.val ((h ⟨0,hk⟩).symm.trans (h' ⟨0,hk⟩))
  change c+(τ ⟨0,hk⟩).val = c'+(τ ⟨0,hk⟩).val at he
  omega

theorem at_mem_iff {n k s c : ℕ} {π : Equiv.Perm (Fin n)} {τ : Equiv.Perm (Fin k)}
    (h : At π τ s c) (x : Fin n) : π x ∈ block n c k ↔ x ∈ block n s k := by
  obtain ⟨hs,hc,h⟩ := h
  let e := (blockEquiv hs).symm.trans (τ.trans (blockEquiv hc))
  have he (y : {x // x ∈ block n s k}) : π y.val = (e y).val := by
    obtain ⟨i,rfl⟩ := (blockEquiv hs).surjective y
    change π (loc hs i) = (blockEquiv hc (τ ((blockEquiv hs).symm (blockEquiv hs i)))).val
    rw [Equiv.symm_apply_apply]
    exact h i
  constructor
  · intro hx
    let y := e.symm ⟨π x,hx⟩
    have hy : π y.val = π x := (he y).trans (congrArg Subtype.val (e.apply_symm_apply _))
    exact π.injective hy ▸ y.property
  · intro hx
    rw [he ⟨x,hx⟩]
    exact (e ⟨x,hx⟩).property

theorem agrees_on_block {n k s c : ℕ} {π ρ : Equiv.Perm (Fin n)} {τ : Equiv.Perm (Fin k)}
    (hπ : At π τ s c) (hρ : At ρ τ s c) {x : Fin n} (hx : x ∈ block n s k) : π x = ρ x := by
  obtain ⟨hs,_,hp⟩ := hπ
  obtain ⟨_,_,hr⟩ := hρ
  obtain ⟨i,hi⟩ := (blockEquiv hs).surjective ⟨x,hx⟩
  have he : loc hs i = x := congrArg Subtype.val hi
  rw [← he, hp, hr]

theorem card_completions {n : ℕ} (S : Finset (Fin n)) (ρ : Equiv.Perm (Fin n)) :
    Fintype.card {π : Equiv.Perm (Fin n) // ∀ x ∈ S, π x = ρ x} = (n-S.card).factorial := by
  let fix (u : Equiv.Perm {x : Fin n // x ∉ S}) : Equiv.Perm (Fin n) :=
    Equiv.Perm.subtypeCongr (p := fun x : Fin n => x ∈ S) (Equiv.refl _) u
  have hl (u) (x) (hx : x ∈ S) : fix u x = x :=
    Equiv.Perm.subtypeCongr.left_apply (p := fun x : Fin n => x ∈ S) (Equiv.refl _) u hx
  have hr (u) (x) (hx : x ∉ S) : fix u x = (u ⟨x,hx⟩).val :=
    Equiv.Perm.subtypeCongr.right_apply (p := fun x : Fin n => x ∈ S) (Equiv.refl _) u hx
  let f (u : Equiv.Perm {x : Fin n // x ∉ S}) :
      {π : Equiv.Perm (Fin n) // ∀ x ∈ S, π x = ρ x} :=
    ⟨(fix u).trans ρ, fun x hx => congrArg ρ (hl u x hx)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro u v h
      apply Equiv.ext
      intro x
      apply Subtype.ext
      have he := ρ.injective (congrArg (fun q => q.val x.val) h)
      change fix u x.val = fix v x.val at he
      rwa [hr u _ x.property, hr v _ x.property] at he
    · intro π
      let g := π.val.trans ρ.symm
      have hg (x : Fin n) (hx : x ∈ S) : g x = x := by simp [g, π.property x hx]
      have hm (x : Fin n) : g x ∉ S ↔ x ∉ S := by
        constructor
        · exact fun h hx => h (by rwa [hg x hx])
        · intro h hx
          have he := g.injective (hg (g x) hx)
          exact h (he ▸ hx)
      let u : Equiv.Perm {x : Fin n // x ∉ S} := g.subtypeEquiv (fun x => (hm x).symm)
      refine ⟨u,Subtype.ext (Equiv.ext fun x => ?_)⟩
      change ρ (fix u x) = π.val x
      by_cases hx : x ∈ S
      · rw [hl u _ hx]
        exact (π.property x hx).symm
      · rw [hr u _ hx]
        change ρ (ρ.symm (π.val x)) = _
        simp
  rw [← Fintype.card_congr (Equiv.ofBijective f hf), Fintype.card_perm]
  have hcard : Fintype.card {x : Fin n // x ∉ S} = n-S.card := by
    calc
      _ = Fintype.card ↥(Sᶜ) := Fintype.card_congr
        (Equiv.subtypeEquivRight fun _ => Finset.mem_compl.symm)
      _ = (Sᶜ).card := Fintype.card_coe _
      _ = _ := by rw [Finset.card_compl, Fintype.card_fin]
  rw [hcard]

theorem card_at {n k s c : ℕ} (τ : Equiv.Perm (Fin k)) (hs : s+k ≤ n) (hc : c+k ≤ n) :
    Fintype.card {π : Equiv.Perm (Fin n) // At π τ s c} = (n-k).factorial := by
  let e := (blockEquiv hs).symm.trans (τ.trans (blockEquiv hc))
  let ρ := e.extendSubtype
  have hr : At ρ τ s c := by
    refine ⟨hs,hc,fun i => ?_⟩
    have hx : loc hs i ∈ block n s k := (blockEquiv hs i).property
    change e.extendSubtype (loc hs i) = _
    rw [e.extendSubtype_apply_of_mem _ hx]
    change (blockEquiv hc (τ ((blockEquiv hs).symm (blockEquiv hs i)))).val = _
    rw [Equiv.symm_apply_apply]
    rfl
  have hh := card_completions (block n s k) ρ
  rw [card_block hs] at hh
  rw [← hh]
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro π
  refine ⟨fun h x hx => agrees_on_block h hr hx, fun h => ?_⟩
  obtain ⟨_,_,hr⟩ := hr
  exact ⟨hs,hc,fun i => (h _ (blockEquiv hs i).property).trans (hr i)⟩

end
end Hertzsprung
```

## HzGeometry.lean

```lean
import HzCore

namespace Hertzsprung

open Finset
open scoped Classical
noncomputable section

theorem card_union_at {n k s t c e : ℕ} {π : Equiv.Perm (Fin n)} {τ : Equiv.Perm (Fin k)}
    (h : At π τ s c) (h' : At π τ t e) :
    ((block n s k) ∪ block n t k).card = ((block n c k) ∪ block n e k).card := by
  let f : {x // x ∈ block n s k ∪ block n t k} ≃
      {x // x ∈ block n c k ∪ block n e k} :=
    π.subtypeEquiv (fun x => by
      simp only [mem_union, at_mem_iff h, at_mem_iff h'])
  simpa only [Fintype.card_coe] using Fintype.card_congr f

theorem union_overlap {n a b k : ℕ} (hab : a ≤ b) (hb : b ≤ a+k) :
    block n a k ∪ block n b k = block n a (k+(b-a)) := by
  ext x
  simp only [mem_union, mem_block]
  omega

theorem disjoint_blocks {n a b k : ℕ} (h : a+k ≤ b) :
    Disjoint (block n a k) (block n b k) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  simp only [mem_block] at hx hy
  omega

theorem offsets_disjoint {n k s t c e : ℕ} (hk : 0 < k)
    {π : Equiv.Perm (Fin n)} {τ : Equiv.Perm (Fin k)}
    (hst : s+k ≤ t) (h : At π τ s c) (h' : At π τ t e) :
    c+k ≤ e ∨ e+k ≤ c := by
  by_contra! hn
  have hc := h.choose_spec.choose
  have he := h'.choose_spec.choose
  let y : Fin n := ⟨max c e, by omega⟩
  have h₁ : y ∈ block n c k := mem_block.mpr (by change c ≤ max c e ∧ max c e < c+k; omega)
  have h₂ : y ∈ block n e k := mem_block.mpr (by change e ≤ max c e ∧ max c e < e+k; omega)
  obtain ⟨x,hx⟩ := π.surjective y
  rw [← hx] at h₁ h₂
  exact Finset.disjoint_left.mp (disjoint_blocks hst) ((at_mem_iff h x).mp h₁)
    ((at_mem_iff h' x).mp h₂)

theorem overlap_data {n k s d c e : ℕ} {π : Equiv.Perm (Fin n)} {τ : Equiv.Perm (Fin k)}
    (hd : d < k) (h : At π τ s c) (h' : At π τ (s+d) e) :
    min c e + (k+d) ≤ n ∧ max c e = min c e + d ∧
    (e : ℤ) - c = ((τ ⟨d,hd⟩).val : ℤ) - (τ ⟨0,by omega⟩).val := by
  obtain ⟨hs,hc,hv⟩ := h
  obtain ⟨ht,he,hw⟩ := h'
  have heq : loc hs ⟨d,hd⟩ = loc ht ⟨0,by omega⟩ := Fin.ext (by simp [loc])
  have heng := congrArg Fin.val ((hv ⟨d,hd⟩).symm.trans ((congrArg π heq).trans (hw ⟨0,by omega⟩)))
  change c+(τ ⟨d,hd⟩).val = e+(τ ⟨0,by omega⟩).val at heng
  have hpos : (block n s k ∪ block n (s+d) k).card = k+d := by
    rw [union_overlap (by omega) (by omega), show s+d-s = d by omega, card_block (by omega)]
  have hval := card_union_at (show At π τ s c from ⟨hs,hc,hv⟩)
    (show At π τ (s+d) e from ⟨ht,he,hw⟩)
  rw [hpos] at hval
  have hdiff : max c e = min c e + d := by
    rcases le_total c e with hce | hec
    · rw [union_overlap hce (by
        have := (τ ⟨d,hd⟩).isLt
        omega), card_block (by omega)] at hval
      simp only [max_eq_right hce, min_eq_left hce]
      omega
    · rw [Finset.union_comm, union_overlap hec (by
        have := (τ ⟨0,by omega⟩ : Fin k).isLt
        omega), card_block (by omega)] at hval
      simp only [max_eq_left hec, min_eq_right hec]
      omega
  exact ⟨by omega, hdiff, by omega⟩

theorem adj_monotone {n k s c e : ℕ} (hk : 2 ≤ k)
    {π : Equiv.Perm (Fin n)} {τ : Equiv.Perm (Fin k)}
    (h : At π τ s c) (h' : At π τ (s+1) e) :
    τ = Equiv.refl _ ∨ τ = Fin.revPerm := by
  have ⟨_, hh, _⟩ := overlap_data (d := 1) (by omega) h h'
  obtain ⟨hs,_,hv⟩ := h
  obtain ⟨ht,_,hw⟩ := h'
  have step (i : ℕ) (hi : i+1 < k) :
      c + (τ ⟨i+1,hi⟩).val = e + (τ ⟨i,by omega⟩).val := by
    have heq : loc hs ⟨i+1,hi⟩ = loc ht ⟨i,by omega⟩ := Fin.ext (by
      change s+(i+1) = (s+1)+i
      omega)
    exact congrArg Fin.val ((hv _).symm.trans ((congrArg π heq).trans (hw _)))
  let z := (τ ⟨0,by omega⟩).val
  have hz : z < k := (τ _).isLt
  have line (i : ℕ) (hi : i < k) :
      ((τ ⟨i,hi⟩).val : ℤ) = (z : ℤ) + (i : ℤ)*((e : ℤ)-c) := by
    induction i with
    | zero => simp [z]
    | succ i ih =>
      have hst := step i hi
      have hp := ih (by omega)
      push_cast
      rw [add_mul, one_mul]
      omega
  let l : Fin k := ⟨k-1,by omega⟩
  let w := (τ l).val
  have hwlt : w < k := (τ l).isLt
  have last : (w : ℤ) = (z : ℤ) + ((k-1 : ℕ) : ℤ)*((e : ℤ)-c) := line (k-1) l.isLt
  by_cases hce : c ≤ e
  · left
    have hec : (e : ℤ)-c = 1 := by omega
    rw [hec, mul_one] at last
    have hz0 : z = 0 := by omega
    apply Equiv.ext
    intro i
    apply Fin.ext
    have hi : ((τ i).val : ℤ) = (z : ℤ) + (i.val : ℤ)*((e : ℤ)-c) := line i.val i.isLt
    rw [hec, mul_one] at hi
    change (τ i).val = i.val
    omega
  · right
    have hec : (e : ℤ)-c = -1 := by omega
    rw [hec, mul_neg_one] at last
    have hzk : z = k-1 := by omega
    apply Equiv.ext
    intro i
    apply Fin.ext
    have hi : ((τ i).val : ℤ) = (z : ℤ) + (i.val : ℤ)*((e : ℤ)-c) := line i.val i.isLt
    rw [hec, mul_neg_one] at hi
    change (τ i).val = k-(i.val+1)
    have := i.isLt
    omega

theorem at_adj_id_iff {n k s : ℕ} (hk : 2 ≤ k) (π : Equiv.Perm (Fin n)) :
    (∃ c, At π (Equiv.refl (Fin k)) s c ∧
      ∃ e, At π (Equiv.refl (Fin k)) (s+1) e) ↔
    ∃ c, At π (Equiv.refl (Fin (k+1))) s c := by
  constructor
  · rintro ⟨c,h,e,h'⟩
    have ⟨hn, hc, he⟩ := overlap_data (d := 1) (by omega) h h'
    change (e : ℤ)-c = (1 : ℕ) - (0 : ℕ) at he
    obtain ⟨hs,hcs,hv⟩ := h
    obtain ⟨ht,hct,hw⟩ := h'
    refine ⟨c,by omega,by omega,fun i => Fin.ext ?_⟩
    by_cases hi : i.val < k
    · have heq := congrArg Fin.val (hv ⟨i.val,hi⟩)
      exact heq
    · have heq := congrArg Fin.val (hw ⟨i.val-1,by have := i.isLt; omega⟩)
      change (π (loc ht ⟨i.val-1,_⟩)).val = e+(i.val-1) at heq
      have he' : loc ht ⟨i.val-1,by have := i.isLt; omega⟩ =
          loc (k := k+1) (s := s) (by omega) i := Fin.ext (by
            change s+1+(i.val-1) = s+i.val
            have := i.isLt
            omega)
      rw [he'] at heq
      change (π (loc (k := k+1) (s := s) (by omega) i)).val = c+i.val
      omega
  · rintro ⟨c,hs,hc,hv⟩
    refine ⟨c,⟨by omega,by omega,fun i => Fin.ext (congrArg Fin.val
      (hv ⟨i.val,by have := i.isLt; omega⟩))⟩,c+1,by omega,by omega,fun i => Fin.ext ?_⟩
    have hh := congrArg Fin.val (hv ⟨i.val+1,by have := i.isLt; omega⟩)
    change (π (loc hs ⟨i.val+1,_⟩)).val = c+(i.val+1) at hh
    have he : loc hs ⟨i.val+1,by have := i.isLt; omega⟩ =
        loc (k := k) (s := s+1) (by omega) i := Fin.ext (by
          change s+(i.val+1) = (s+1)+i.val
          omega)
    rw [he] at hh
    change (π (loc (k := k) (s := s+1) (by omega) i)).val = c+1+i.val
    omega

end
end Hertzsprung
```

## HzMoments.lean

```lean
import HzGeometry
import Mathlib.Data.Fintype.BigOperators

namespace Hertzsprung

open Finset
open scoped Classical BigOperators
noncomputable section

abbrev Perm (n : ℕ) := Equiv.Perm (Fin n)
abbrev Start (n k : ℕ) := Fin (n-k+1)

theorem start_lt {n k s : ℕ} (h : s+k ≤ n) : s < n-k+1 := by omega

theorem start_bound {n k : ℕ} (h : k ≤ n) (s : Start n k) : s.val+k ≤ n := by
  have := s.isLt
  omega

abbrev Starts {n k : ℕ} (τ : Perm k) (π : Perm n) :=
  {s : Start n k // HOcc π τ s}

abbrev Occs {n k : ℕ} (τ : Perm k) := Σ π : Perm n, Starts τ π

abbrev Pairs {n k : ℕ} (τ : Perm k) (π : Perm n) :=
  {p : Starts τ π × Starts τ π // p.1.val < p.2.val}

abbrev Adj {n k : ℕ} (τ : Perm k) (π : Perm n) :=
  {p : Pairs τ π // p.val.2.val.val = p.val.1.val.val+1}

theorem card_fibers {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (f : α → β) :
    Fintype.card α = ∑ b : β, Fintype.card {a // f a = b} := by
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv f).symm

theorem first_moment {n k : ℕ} (hk : 0 < k) (hn : k ≤ n) (τ : Perm k) :
    Fintype.card (Occs (n := n) τ) = (n-k+1)^2 * (n-k).factorial := by
  let β := Σ p : Start n k × Start n k, {π : Perm n // At π τ p.1 p.2}
  have h (a : Occs (n := n) τ) := (hOcc_iff_at hk _ _).mp a.2.property
  let f (a : Occs (n := n) τ) : β :=
    ⟨(a.2.val,⟨(h a).choose,start_lt (h a).choose_spec.choose_spec.choose⟩),a.1,(h a).choose_spec⟩
  let g (b : β) : Occs (n := n) τ :=
    ⟨b.2.val,b.1.1,(hOcc_iff_at hk _ _).mpr ⟨b.1.2,b.2.property⟩⟩
  have hfg : Function.LeftInverse g f := fun ⟨_,_⟩ => rfl
  have hgf : Function.RightInverse g f := by
    intro ⟨⟨s,c⟩,π,hπ⟩
    have hc := at_unique hk (h (g ⟨(s,c),π,hπ⟩)).choose_spec hπ
    have hbase : (f (g ⟨(s,c),π,hπ⟩)).1 = (s,c) := Prod.ext rfl (Fin.ext hc)
    apply Sigma.ext hbase
    apply (Subtype.heq_iff_coe_eq (by intro x; rw [hbase])).2
    rfl
  calc
    _ = Fintype.card β := Fintype.card_congr ⟨f,g,hfg,hgf⟩
    _ = _ := by
      dsimp only [β]
      rw [Fintype.card_sigma]
      simp_rw [card_at τ (start_bound hn _) (start_bound hn _)]
      simp [pow_two, mul_assoc]

def indicator {n k : ℕ} (τ : Perm k) (π : Perm n) : ℕ :=
  if Nonempty (Starts τ π) then 1 else 0

def containsCount {n k : ℕ} (τ : Perm k) : ℕ := ∑ π : Perm n, indicator τ π

theorem no_occ_iff {n k : ℕ} (τ : Perm k) (π : Perm n) :
    (∀ s, ¬ HOcc π τ s) ↔ ¬ Nonempty (Starts τ π) := by
  constructor
  · exact fun h ⟨⟨s,hs⟩⟩ => h s hs
  · intro h s hs
    exact h ⟨⟨⟨s,start_lt hs.choose⟩,hs⟩⟩

theorem avoid_add_contains {n k : ℕ} (τ : Perm k) :
    avoidCount n k τ + containsCount (n := n) τ = Fintype.card (Perm n) := by
  unfold avoidCount containsCount indicator
  rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones, ← Finset.card_univ]
  rw [← Finset.card_filter_add_card_filter_not (s := (univ : Finset (Perm n)))
    (p := fun π => Nonempty (Starts τ π)), add_comm]
  congr 1
  congr 1
  ext π
  simp only [mem_filter, mem_univ, true_and, no_occ_iff]

theorem lower_local {n k : ℕ} (τ : Perm k) (π : Perm n) :
    Fintype.card (Starts τ π) ≤ indicator τ π + Fintype.card (Pairs τ π) := by
  let S := (univ : Finset (Start n k)).filter (fun s : Start n k => HOcc π τ s)
  by_cases hs : S.Nonempty
  · let m := S.min' hs
    have hm : m ∈ S := S.min'_mem hs
    let a : Starts τ π := ⟨m,(mem_filter.mp hm).2⟩
    let f (x : Starts τ π) : Option (Pairs τ π) :=
      if h : m < x.val then some ⟨(a,x),h⟩ else none
    have hf : Function.Injective f := by
      intro x y hxy
      have hsmall (b : Starts τ π) : m ≤ b.val :=
        S.min'_le _ (mem_filter.mpr ⟨mem_univ _,b.property⟩)
      by_cases hx : m < x.val <;> by_cases hy : m < y.val
      · have he : (⟨(a,x),hx⟩ : Pairs τ π) = ⟨(a,y),hy⟩ := by
          apply Option.some.inj
          simpa only [f, dite_eq_left hx, dite_eq_left hy] using hxy
        exact congrArg (fun p : Pairs τ π => p.val.2) he
      · simp [f,hx,hy] at hxy
      · simp [f,hx,hy] at hxy
      · exact Subtype.ext (le_antisymm (not_lt.mp hx) (hsmall x) |>.trans
          (le_antisymm (not_lt.mp hy) (hsmall y)).symm)
    have hc := Fintype.card_le_of_injective f hf
    simpa [indicator, show Nonempty (Starts τ π) from ⟨a⟩, Nat.add_comm] using hc
  · have : IsEmpty (Starts τ π) := ⟨fun x => hs ⟨x.val,mem_filter.mpr ⟨mem_univ _,x.property⟩⟩⟩
    simp

theorem upper_local {n k : ℕ} (τ : Perm k) (π : Perm n) :
    indicator τ π + Fintype.card (Adj τ π) ≤ Fintype.card (Starts τ π) := by
  let S := (univ : Finset (Start n k)).filter (fun s : Start n k => HOcc π τ s)
  by_cases hs : S.Nonempty
  · let m := S.min' hs
    have hm : m ∈ S := S.min'_mem hs
    let a : Starts τ π := ⟨m,(mem_filter.mp hm).2⟩
    let f : Option (Adj τ π) → Starts τ π
      | none => a
      | some q => q.val.val.2
    have hmin (q : Adj τ π) : m < q.val.val.2.val :=
      lt_of_le_of_lt (S.min'_le _ (mem_filter.mpr ⟨mem_univ _,q.val.val.1.property⟩))
        q.val.property
    have hf : Function.Injective f := by
      intro x y h
      cases x with
      | none =>
        cases y with
        | none => rfl
        | some q =>
          exact ((ne_of_lt (hmin q)) (congrArg Subtype.val h)).elim
      | some p =>
        cases y with
        | none =>
          exact ((ne_of_lt (hmin p)) (congrArg Subtype.val h).symm).elim
        | some q =>
          have hr : p.val.val.2 = q.val.val.2 := h
          have hl : p.val.val.1 = q.val.val.1 := by
            apply Subtype.ext
            apply Fin.ext
            have hp := p.property
            have hq := q.property
            have he := congrArg (fun x : Starts τ π => x.val.val) hr
            omega
          exact congrArg some (Subtype.ext (Subtype.ext (Prod.ext hl hr)))
    have hc := Fintype.card_le_of_injective f hf
    simpa [indicator, show Nonempty (Starts τ π) from ⟨a⟩, Nat.add_comm] using hc
  · have he : ¬ Nonempty (Starts τ π) := fun ⟨x⟩ =>
      hs ⟨x.val,mem_filter.mpr ⟨mem_univ _,x.property⟩⟩
    have : IsEmpty (Adj τ π) := ⟨fun x => he ⟨x.val.val.1⟩⟩
    simp [indicator,he]

theorem lower_global {n k : ℕ} (τ : Perm k) :
    Fintype.card (Occs (n := n) τ) ≤ containsCount (n := n) τ +
      Fintype.card (Σ π : Perm n, Pairs τ π) := by
  unfold containsCount
  rw [Fintype.card_sigma, Fintype.card_sigma, ← Finset.sum_add_distrib]
  exact sum_le_sum (fun π _ => lower_local τ π)

theorem upper_global {n k : ℕ} (τ : Perm k) :
    containsCount (n := n) τ + Fintype.card (Σ π : Perm n, Adj τ π) ≤
      Fintype.card (Occs (n := n) τ) := by
  unfold containsCount
  rw [Fintype.card_sigma, Fintype.card_sigma, ← Finset.sum_add_distrib]
  exact sum_le_sum (fun π _ => upper_local τ π)

end
end Hertzsprung
```

## HzPairs.lean

```lean
import HzMoments
import Mathlib.Data.Finset.Prod

namespace Hertzsprung

open Finset
open scoped Classical BigOperators
noncomputable section

abbrev Marked {n k : ℕ} (τ : Perm k) := Σ π : Perm n, Pairs τ π

def leftStart {n k : ℕ} {τ : Perm k} (p : Marked (n := n) τ) : ℕ := p.2.val.1.val.val
def rightStart {n k : ℕ} {τ : Perm k} (p : Marked (n := n) τ) : ℕ := p.2.val.2.val.val
def distance {n k : ℕ} {τ : Perm k} (p : Marked (n := n) τ) : ℕ := rightStart p - leftStart p

theorem start_order {n k : ℕ} {τ : Perm k} (p : Marked (n := n) τ) :
    leftStart p < rightStart p := p.2.property

theorem right_eq {n k : ℕ} {τ : Perm k} (p : Marked (n := n) τ) :
    rightStart p = leftStart p + distance p := by
  have := start_order p
  unfold distance
  omega

theorem distance_bound {n k : ℕ} {τ : Perm k} (p : Marked (n := n) τ) :
    0 < distance p ∧ k + distance p ≤ n := by
  have := start_order p
  have ht := p.2.val.2.property.choose
  change rightStart p + k ≤ n at ht
  unfold distance
  omega

theorem marked_ext {n k : ℕ} {τ : Perm k} {p q : Marked (n := n) τ}
    (h : p.1 = q.1) (hl : leftStart p = leftStart q) (hr : rightStart p = rightStart q) : p = q := by
  rcases p with ⟨π,p⟩
  rcases q with ⟨ρ,q⟩
  change π = ρ at h
  subst ρ
  have hp : p = q := Subtype.ext (Prod.ext (Subtype.ext (Fin.ext hl)) (Subtype.ext (Fin.ext hr)))
  subst q
  rfl

def offsetL {n k : ℕ} {τ : Perm k} (hk : 0 < k) (p : Marked (n := n) τ) : ℕ :=
  ((hOcc_iff_at hk _ _).mp p.2.val.1.property).choose

def offsetR {n k : ℕ} {τ : Perm k} (hk : 0 < k) (p : Marked (n := n) τ) : ℕ :=
  ((hOcc_iff_at hk _ _).mp p.2.val.2.property).choose

theorem pair_atL {n k : ℕ} {τ : Perm k} (hk : 0 < k) (p : Marked (n := n) τ) :
    At p.1 τ (leftStart p) (offsetL hk p) :=
  ((hOcc_iff_at hk _ _).mp p.2.val.1.property).choose_spec

theorem pair_atR {n k : ℕ} {τ : Perm k} (hk : 0 < k) (p : Marked (n := n) τ) :
    At p.1 τ (rightStart p) (offsetR hk p) :=
  ((hOcc_iff_at hk _ _).mp p.2.val.2.property).choose_spec

abbrev Both {n k : ℕ} (τ : Perm k) (s t c e : ℕ) :=
  {π : Perm n // At π τ s c ∧ At π τ t e}

theorem card_both {n k : ℕ} (τ : Perm k) (s t c e m : ℕ)
    (hm : (block n s k ∪ block n t k).card = m) :
    Fintype.card (Both (n := n) τ s t c e) ≤ (n-m).factorial := by
  by_cases h : Nonempty (Both (n := n) τ s t c e)
  · obtain ⟨ρ⟩ := h
    let f (π : Both (n := n) τ s t c e) :
        {π : Perm n // ∀ x ∈ block n s k ∪ block n t k, π x = ρ.val x} :=
      ⟨π.val, fun _ hx => (mem_union.mp hx).elim
        (agrees_on_block π.property.1 ρ.property.1)
        (agrees_on_block π.property.2 ρ.property.2)⟩
    have hh := Fintype.card_le_of_injective f (fun _ _ h => Subtype.ext (congrArg (fun q => q.val) h))
    rw [card_completions, hm] at hh
    exact hh
  · have : IsEmpty (Both (n := n) τ s t c e) := ⟨fun x => h ⟨x⟩⟩
    simp

abbrev AtDistance {n k : ℕ} (τ : Perm k) (d : ℕ) :=
  {p : Marked (n := n) τ // distance p = d}

theorem overlap_bound {n k : ℕ} (τ : Perm k) {d : ℕ}
    (hd : d < k) (hn : k+d ≤ n) :
    Fintype.card (AtDistance (n := n) τ d) ≤ (n-(k+d)+1)^2 * (n-(k+d)).factorial := by
  have hk : 0 < k := by omega
  let increasing : Prop := (τ ⟨0,hk⟩).val ≤ (τ ⟨d,hd⟩).val
  let c (a : ℕ) := if increasing then a else a+d
  let e (a : ℕ) := if increasing then a+d else a
  let β := Start n (k+d) × Start n (k+d)
  have hd' (p : AtDistance (n := n) τ d) :
      rightStart p.val = leftStart p.val + d := (right_eq p.val).trans (congrArg (_ + ·) p.property)
  have hdata (p : AtDistance (n := n) τ d) :=
    overlap_data hd (pair_atL hk p.val) (hd' p ▸ pair_atR hk p.val)
  -- The signed difference fixes which of the two offsets is the smaller one.
  have hc (p : AtDistance (n := n) τ d) :
      c (min (offsetL hk p.val) (offsetR hk p.val)) = offsetL hk p.val := by
    obtain ⟨_,hm,hs⟩ := hdata p
    dsimp only [c]
    split
    · rename_i hinc
      change (τ ⟨0,hk⟩).val ≤ (τ ⟨d,hd⟩).val at hinc
      omega
    · rename_i hinc
      change ¬ (τ ⟨0,hk⟩).val ≤ (τ ⟨d,hd⟩).val at hinc
      omega
  have he (p : AtDistance (n := n) τ d) :
      e (min (offsetL hk p.val) (offsetR hk p.val)) = offsetR hk p.val := by
    obtain ⟨_,hm,hs⟩ := hdata p
    dsimp only [e]
    split
    · rename_i hinc
      change (τ ⟨0,hk⟩).val ≤ (τ ⟨d,hd⟩).val at hinc
      omega
    · rename_i hinc
      change ¬ (τ ⟨0,hk⟩).val ≤ (τ ⟨d,hd⟩).val at hinc
      omega
  let f (p : AtDistance (n := n) τ d) :
      Σ b : β, Both (n := n) τ b.1 (b.1.val+d) (c b.2) (e b.2) := by
    let a := min (offsetL hk p.val) (offsetR hk p.val)
    have ht := (pair_atR hk p.val).choose
    rw [hd' p] at ht
    refine ⟨(⟨leftStart p.val,start_lt (by omega)⟩,⟨a,start_lt (hdata p).1⟩),p.val.1,?_⟩
    dsimp only [a]
    exact ⟨by simpa only [hc p] using pair_atL hk p.val,
      by simpa only [he p, ← hd' p] using pair_atR hk p.val⟩
  have hf : Function.Injective f := by
    intro p q h
    have hl := congrArg (fun a => a.1.1.val) h
    change leftStart p.val = leftStart q.val at hl
    have hπ := congrArg (fun a => a.2.val) h
    exact Subtype.ext (marked_ext hπ hl (by rw [hd' p, hd' q, hl]))
  refine (Fintype.card_le_of_injective f hf).trans ?_
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _ : β, (n-(k+d)).factorial := by
      apply sum_le_sum
      intro b _
      apply card_both
      have hs := start_bound hn b.1
      rw [union_overlap (by omega) (by omega), show b.1.val+d-b.1.val = d by omega,
        card_block hs]
    _ = _ := by simp [β, pow_two, mul_assoc]

def Ordered (m : ℕ) := { p : Fin m × Fin m // p.1 < p.2 }

instance (m : ℕ) : Fintype (Ordered m) :=
  inferInstanceAs (Fintype { p : Fin m × Fin m // p.1 < p.2 })

theorem ordered_card (m : ℕ) : 2 * Fintype.card (Ordered m) = m*(m-1) := by
  let S := (univ : Finset (Fin m)).offDiag
  let f (b : Bool × Ordered m) : ↥S := by
    rcases b with ⟨b,⟨⟨a,c⟩,h⟩⟩
    cases b
    · exact ⟨(a,c),by simp [S,h.ne]⟩
    · exact ⟨(c,a),by simp [S,h.ne.symm]⟩
  let g (b : ↥S) : Bool × Ordered m := by
    rcases b with ⟨⟨a,c⟩,h⟩
    have hn : a ≠ c := by simpa [S] using h
    exact if hl : a < c then (false,⟨(a,c),hl⟩) else
      (true,⟨(c,a),lt_of_le_of_ne (le_of_not_gt hl) hn.symm⟩)
  have h₁ : Function.LeftInverse g f := by
    rintro ⟨b,⟨⟨a,c⟩,h⟩⟩
    cases b <;> simp [f,g,h,h.not_gt]
  have h₂ : Function.RightInverse g f := by
    rintro ⟨⟨a,c⟩,h⟩
    by_cases hl : a < c <;> simp [f,g,hl]
  have hh := Fintype.card_congr (Equiv.mk f g h₁ h₂)
  simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_coe, S, offDiag_card,
    card_univ, Fintype.card_fin] at hh
  rw [hh, Nat.mul_sub, Nat.mul_one]

abbrev Separated {n k : ℕ} (τ : Perm k) :=
  {p : Marked (n := n) τ // k ≤ distance p}

theorem separated_size {n k : ℕ} {τ : Perm k} (p : Separated (n := n) τ) :
    2*k ≤ n := by
  have := (distance_bound p.val).2
  have := p.property
  omega

theorem separated_bound {n k : ℕ} (τ : Perm k) (hk : 0 < k) (hn : 2*k ≤ n) :
    let L := n-2*k
    2 * Fintype.card (Separated (n := n) τ) ≤ ((L+2)*(L+1))^2 * L.factorial := by
  dsimp only
  let L := n-2*k
  let β := Ordered (L+2) × Ordered (L+2) × Bool
  let s (b : β) := b.1.val.1.val
  let t (b : β) := b.1.val.2.val+k-1
  let lo (b : β) := b.2.1.val.1.val
  let hi (b : β) := b.2.1.val.2.val+k-1
  let c (b : β) := if b.2.2 then hi b else lo b
  let e (b : β) := if b.2.2 then lo b else hi b
  let encode (x y : ℕ) (hxy : x+k ≤ y) (hy : y+k ≤ n) : Ordered (L+2) :=
    ⟨(⟨x,by dsimp [L]; omega⟩,⟨y-k+1,by dsimp [L]; omega⟩),by
      change x < y-k+1
      omega⟩
  have gap (p : Separated (n := n) τ) : leftStart p.val+k ≤ rightStart p.val := by
    rw [right_eq p.val]
    have := p.property
    omega
  have lv (p : Separated (n := n) τ) := (pair_atL hk p.val).choose_spec.choose
  have rv (p : Separated (n := n) τ) := (pair_atR hk p.val).choose_spec.choose
  let key (p : Separated (n := n) τ) : β := by
    have hs := (pair_atR hk p.val).choose
    have hp := encode (leftStart p.val) (rightStart p.val) (gap p) hs
    have h := offsets_disjoint hk (gap p) (pair_atL hk p.val) (pair_atR hk p.val)
    exact if hl : offsetL hk p.val+k ≤ offsetR hk p.val then
      (hp,encode _ _ hl (rv p),false)
    else (hp,encode _ _ (h.resolve_left hl) (lv p),true)
  have key_data (p : Separated (n := n) τ) :
      s (key p) = leftStart p.val ∧ t (key p) = rightStart p.val ∧
      c (key p) = offsetL hk p.val ∧ e (key p) = offsetR hk p.val := by
    have h := offsets_disjoint hk (gap p) (pair_atL hk p.val) (pair_atR hk p.val)
    have hgap := gap p
    by_cases hl : offsetL hk p.val+k ≤ offsetR hk p.val
    · simp [key, s,t,c,e,lo,hi,encode,hl]
      constructor <;> omega
    · have hr := h.resolve_left hl
      simp [key,s,t,c,e,lo,hi,encode,hl]
      constructor <;> omega
  let f (p : Separated (n := n) τ) :
      Σ b : β, Both (n := n) τ (s b) (t b) (c b) (e b) :=
    ⟨key p,p.val.1,by
      obtain ⟨h₁,h₂,h₃,h₄⟩ := key_data p
      rw [h₁,h₂,h₃,h₄]
      exact ⟨pair_atL hk p.val,pair_atR hk p.val⟩⟩
  have hf : Function.Injective f := by
    intro p q h
    have hkey := congrArg Sigma.fst h
    change key p = key q at hkey
    exact Subtype.ext (marked_ext (congrArg (fun a => a.2.val) h)
      (by rw [← (key_data p).1, ← (key_data q).1, hkey])
      (by rw [← (key_data p).2.1, ← (key_data q).2.1, hkey]))
  have hb : Fintype.card (Σ b : β, Both (n := n) τ (s b) (t b) (c b) (e b)) ≤
      Fintype.card β * L.factorial := by
    rw [Fintype.card_sigma]
    calc
      _ ≤ ∑ _ : β, L.factorial := by
        apply sum_le_sum
        intro b _
        have hlt : s b < b.1.val.2.val := b.1.property
        have hmax := b.1.val.2.isLt
        have hst : s b+k ≤ t b := by dsimp [t]; omega
        have ht : t b+k ≤ n := by dsimp [L,t] at *; omega
        have HH : (block n (s b) k ∪ block n (t b) k).card = 2*k := by
          rw [card_union_of_disjoint (disjoint_blocks hst), card_block (by omega), card_block ht]
          omega
        exact card_both τ _ _ _ _ _ HH
      _ = _ := by simp
  refine (Nat.mul_le_mul_left 2 ((Fintype.card_le_of_injective f hf).trans hb)).trans ?_
  have hcard := ordered_card (L+2)
  have hsub : L+2-1 = L+1 := by omega
  rw [hsub] at hcard
  simp only [β, Fintype.card_prod, Fintype.card_bool]
  calc
    _ = (2 * Fintype.card (Ordered (L+2)))^2 * L.factorial := by ring
    _ = ((L+2)*(L+1))^2 * L.factorial := by rw [hcard]
    _ ≤ _ := le_rfl

end
end Hertzsprung
```

## HzEstimates.lean

```lean
import HzPairs

namespace Hertzsprung

open Finset
open scoped Classical BigOperators
noncomputable section

def weight (m : ℕ) : ℕ := (m+1)^2 * m.factorial

theorem weight_step (m : ℕ) : 4 * weight m ≤ weight (m+1) := by
  have h : 4*(m+1) ≤ (m+1+1)^2 := by nlinarith [sq_nonneg (m : ℤ)]
  unfold weight
  rw [Nat.factorial_succ]
  calc
    _ = (4*(m+1))*((m+1)*m.factorial) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ h

theorem overlap_sum (M : ℕ) (hM : 1 ≤ M) :
    3 * (∑ d ∈ range (M+1), if 2 ≤ d then weight (M-d) else 0) ≤ weight (M-1) := by
  have partialSum (r : ℕ) (hr : r+1 ≤ M) :
      3 * (∑ d ∈ range (r+2), if 2 ≤ d then weight (M-d) else 0) +
        weight (M-(r+1)) ≤ weight (M-1) := by
    induction r with
    | zero => simp [Finset.sum_range_succ]
    | succ r ih =>
      rw [show r+1+2 = (r+2)+1 by omega, Finset.sum_range_succ, ite_eq_left (by omega)]
      have h := ih (by omega)
      have hw := weight_step (M-(r+2))
      rw [show M-(r+2)+1 = M-(r+1) by omega] at hw
      rw [show r+1+1 = r+2 by omega]
      omega
  have h := partialSum (M-1) (by omega)
  rw [show M-1+2 = M+1 by omega] at h
  omega

theorem separated_weight (L k : ℕ) (hk : 3 ≤ k) :
    ((L+2)*(L+1))^2 * L.factorial ≤ weight (L+k-1) := by
  have hfac := Nat.factorial_le (show L+2 ≤ L+k-1 by omega)
  rw [Nat.factorial_succ (L+1), Nat.factorial_succ L] at hfac
  have hsq : (L+2)*(L+1) ≤ (L+k-1+1)^2 := by
    have h₁ : L+2 ≤ L+k-1+1 := by omega
    have h₂ : L+1 ≤ L+k-1+1 := by omega
    simpa only [pow_two] using Nat.mul_le_mul h₁ h₂
  unfold weight
  calc
    _ = ((L+2)*(L+1))*((L+2)*((L+1)*L.factorial)) := by ring
    _ ≤ _ := Nat.mul_le_mul hsq hfac

abbrev Overlapping {n k : ℕ} (τ : Perm k) :=
  {p : Marked (n := n) τ // distance p < k}

theorem overlap_total {n k : ℕ} (τ : Perm k) (hk : 3 ≤ k) (hn : k < n)
    (hinc : τ ≠ Equiv.refl _) (hdec : τ ≠ Fin.revPerm) :
    3 * Fintype.card (Overlapping (n := n) τ) ≤ weight (n-k-1) := by
  let f (p : Overlapping (n := n) τ) : Start n k :=
    ⟨distance p.val, start_lt (by have := (distance_bound p.val).2; omega)⟩
  have hf (d : Start n k) :
      Fintype.card {p // f p = d} ≤ (if 2 ≤ d.val then weight (n-k-d.val) else 0) := by
    by_cases hd : 2 ≤ d.val
    · rw [ite_eq_left hd]
      by_cases hdk : d.val < k
      · let g (p : {p // f p = d}) : AtDistance (n := n) τ d.val :=
          ⟨p.val.val,congrArg Fin.val p.property⟩
        have hg : Function.Injective g := fun _ _ h =>
          Subtype.ext (Subtype.ext (congrArg (fun q => q.val) h))
        have h := overlap_bound (n := n) τ hdk (by simpa only [Nat.add_comm k] using start_bound (show k ≤ n by omega) d)
        have hsub : n-(k+d.val) = n-k-d.val := by omega
        rw [hsub] at h
        exact (Fintype.card_le_of_injective g hg).trans h
      · have : IsEmpty {p // f p = d} := ⟨fun p => hdk
          ((congrArg Fin.val p.property : distance p.val.val = d.val) ▸ p.val.property)⟩
        simp
    · rw [ite_eq_right hd]
      have : IsEmpty {p // f p = d} := by
        constructor
        intro p
        let q := p.val.val
        have h := congrArg Fin.val p.property
        change distance q = d.val at h
        have hq := (distance_bound q).1
        have he : rightStart q = leftStart q+1 := by
          rw [right_eq q]
          have : distance q = 1 := by omega
          rw [this]
        exact (adj_monotone (by omega) (pair_atL (by omega) q)
          (he ▸ pair_atR (by omega) q)).elim hinc hdec
      simp
  have h := Finset.sum_le_sum (s := (univ : Finset (Start n k))) (fun d _ => hf d)
  rw [← card_fibers f, Fin.sum_univ_eq_sum_range (fun d : ℕ => if 2 ≤ d then weight (n-k-d) else 0)] at h
  exact (Nat.mul_le_mul_left 3 h).trans (overlap_sum (n-k) (by omega))

theorem separated_total {n k : ℕ} (τ : Perm k) (hk : 3 ≤ k) :
    2 * Fintype.card (Separated (n := n) τ) ≤ weight (n-k-1) := by
  by_cases hn : 2*k ≤ n
  · have h := separated_bound τ (by omega) hn
    have hw := separated_weight (n-2*k) k hk
    rw [show n-2*k+k-1 = n-k-1 by omega] at hw
    exact h.trans hw
  · have : IsEmpty (Separated (n := n) τ) := ⟨fun p => hn (separated_size p)⟩
    simp

theorem pairs_total {n k : ℕ} (τ : Perm k) (hk : 3 ≤ k) (hn : k < n)
    (hinc : τ ≠ Equiv.refl _) (hdec : τ ≠ Fin.revPerm) :
    Fintype.card (Marked (n := n) τ) < weight (n-k-1) := by
  have hsplit : Fintype.card (Marked (n := n) τ) =
      Fintype.card (Overlapping (n := n) τ) + Fintype.card (Separated (n := n) τ) := by
    rw [← Fintype.card_sum]
    exact Fintype.card_congr ((Equiv.sumCompl (fun p : Marked (n := n) τ => distance p < k)).symm.trans
      (Equiv.sumCongr (Equiv.refl _) (Equiv.subtypeEquivRight fun _ => not_lt)))
  have ho := overlap_total τ hk hn hinc hdec
  have hs := separated_total (n := n) τ hk
  have hp : 0 < weight (n-k-1) := by unfold weight; positivity
  omega

end
end Hertzsprung
```

## HzTheorem.lean

```lean
import HzEstimates

namespace Hertzsprung

open Finset
open scoped Classical BigOperators
noncomputable section

def adjacent_equiv {n k : ℕ} (hk : 2 ≤ k) :
    (Σ π : Perm n, Adj (Equiv.refl (Fin k)) π) ≃ Occs (n := n) (Equiv.refl (Fin (k+1))) := by
  have adj_iff (π : Perm n) (s : ℕ) :
      HOcc π (Equiv.refl (Fin k)) s ∧ HOcc π (Equiv.refl (Fin k)) (s+1) ↔
        HOcc π (Equiv.refl (Fin (k+1))) s := by
    simp_rw [hOcc_iff_at (show 0 < k by omega), hOcc_iff_at (Nat.succ_pos k)]
    rw [← exists_and_right]
    exact at_adj_id_iff hk π
  let f (p : Σ π : Perm n, Adj (Equiv.refl (Fin k)) π) :
      Occs (n := n) (Equiv.refl (Fin (k+1))) := by
    have hl := p.2.val.val.1.property
    have hr := p.2.val.val.2.property
    rw [p.2.property] at hr
    have h := (adj_iff p.1 _).mp ⟨hl,hr⟩
    exact ⟨p.1,⟨⟨_,start_lt h.choose⟩,h⟩⟩
  let g (o : Occs (n := n) (Equiv.refl (Fin (k+1)))) :
      Σ π : Perm n, Adj (Equiv.refl (Fin k)) π := by
    let s := o.2.val.val
    have h := (adj_iff o.1 s).mpr o.2.property
    have hl := h.1
    have hr := h.2
    let l : Starts (Equiv.refl (Fin k)) o.1 := ⟨⟨s,start_lt hl.choose⟩,hl⟩
    let r : Starts (Equiv.refl (Fin k)) o.1 := ⟨⟨s+1,start_lt hr.choose⟩,hr⟩
    exact ⟨o.1,⟨⟨(l,r),by change s < s+1; omega⟩,rfl⟩⟩
  refine ⟨f,g,?_,?_⟩
  · intro ⟨π,p⟩
    apply Sigma.ext (show (g (f ⟨π,p⟩)).1 = π from rfl)
    apply heq_of_eq
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact Subtype.ext (Fin.ext p.property.symm)
  · intro ⟨π,p⟩
    rfl

theorem rev_hOcc {n k s : ℕ} (π : Perm n) :
    HOcc (π.trans Fin.revPerm) (Equiv.refl (Fin k)) s ↔ HOcc π (@Fin.revPerm k) s := by
  constructor
  · rintro ⟨hs,c,h⟩
    refine ⟨hs,(n : ℤ)-k-c,fun i => ?_⟩
    let a := π (loc hs i)
    have ha := a.isLt
    have hi := i.isLt
    have h' := h i
    change ((n-(a.val+1) : ℕ) : ℤ) = (i.val : ℤ) + c at h'
    change (a.val : ℤ) = ((k-(i.val+1) : ℕ) : ℤ) + ((n : ℤ)-k-c)
    omega
  · rintro ⟨hs,c,h⟩
    refine ⟨hs,(n : ℤ)-k-c,fun i => ?_⟩
    let a := π (loc hs i)
    have ha := a.isLt
    have hi := i.isLt
    have h' := h i
    change (a.val : ℤ) = ((k-(i.val+1) : ℕ) : ℤ) + c at h'
    change ((n-(a.val+1) : ℕ) : ℤ) = (i.val : ℤ) + ((n : ℤ)-k-c)
    omega

theorem rev_avoid (n k : ℕ) : avoidCount n k Fin.revPerm = avoidCount n k (Equiv.refl _) := by
  let e : Perm n ≃ Perm n :=
    { toFun := fun π => π.trans Fin.revPerm
      invFun := fun π => π.trans Fin.revPerm
      left_inv := fun π => Equiv.ext fun i => Fin.rev_rev (π i)
      right_inv := fun π => Equiv.ext fun i => Fin.rev_rev (π i) }
  unfold avoidCount
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  apply Fintype.card_congr
  apply e.subtypeEquiv
  intro π
  simp only [mem_filter, mem_univ, true_and]
  change (∀ s, ¬ HOcc π Fin.revPerm s) ↔
    (∀ s, ¬ HOcc (π.trans Fin.revPerm) (Equiv.refl (Fin k)) s)
  simp only [rev_hOcc]

theorem short_pattern {k : ℕ} (hk : k ≤ 2) (τ : Perm k) :
    τ = Equiv.refl _ ∨ τ = Fin.revPerm := by
  by_cases he : k ≤ 1
  · left
    apply Equiv.ext
    intro i
    apply Fin.ext
    have := i.isLt
    have := (τ i).isLt
    change (τ i).val = i.val
    omega
  · have : k = 2 := by omega
    subst k
    by_cases hz : τ 0 = 0
    · left
      apply Equiv.ext
      intro i
      fin_cases i
      · exact hz
      · have hn : τ 1 ≠ 0 := fun h => (by decide : (1 : Fin 2) ≠ 0) (τ.injective (h.trans hz.symm))
        apply Fin.ext
        have hlt := (τ 1).isLt
        change (τ 1).val = 1
        have hpos : (τ 1).val ≠ 0 := fun h => hn (Fin.ext h)
        omega
    · right
      have hz' : τ 0 = 1 := by
        apply Fin.ext
        have hlt := (τ 0).isLt
        have hn : (τ 0).val ≠ 0 := fun h => hz (Fin.ext h)
        omega
      apply Equiv.ext
      intro i
      fin_cases i
      · exact hz'
      · have hn : τ 1 ≠ 1 := fun h => (by decide : (1 : Fin 2) ≠ 0) (τ.injective (h.trans hz'.symm))
        apply Fin.ext
        have hlt := (τ 1).isLt
        change (τ 1).val = 0
        have hne : (τ 1).val ≠ 1 := fun h => hn (Fin.ext h)
        omega

theorem avoid_too_short {n k : ℕ} (h : n < k) (τ : Perm k) :
    avoidCount n k τ = Fintype.card (Perm n) := by
  unfold avoidCount
  have hf : (univ.filter (fun π : Perm n => ∀ s, ¬ HOcc π τ s)) = univ := by
    ext π
    simp only [mem_filter, mem_univ, true_and, iff_true]
    intro s hs
    have := hs.choose
    omega
  rw [hf, card_univ]

theorem avoid_empty (n : ℕ) (τ : Perm 0) : avoidCount n 0 τ = 0 := by
  unfold avoidCount
  have h (π : Perm n) : HOcc π τ 0 := ⟨by omega,0,fun i => Fin.elim0 i⟩
  simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff, mem_univ, forall_const, not_forall, not_not]
  exact fun π => ⟨0,h π⟩

theorem avoid_singleton {n : ℕ} (hn : 0 < n) (τ : Perm 1) : avoidCount n 1 τ = 0 := by
  unfold avoidCount
  have h (π : Perm n) : HOcc π τ 0 := by
    refine ⟨by omega,(π ⟨0,hn⟩).val,fun i => ?_⟩
    have hi : i = 0 := Subsingleton.elim _ _
    have ht : τ 0 = 0 := Subsingleton.elim _ _
    subst i
    simp [ht]
  simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff, mem_univ, forall_const, not_forall, not_not]
  exact fun π => ⟨0,h π⟩

theorem avoid_same_length {n : ℕ} (hn : 0 < n) (τ : Perm n) :
    avoidCount n n τ + 1 = Fintype.card (Perm n) := by
  have hm := first_moment hn (le_refl n) τ
  simp only [Nat.sub_self, zero_add, one_pow, Nat.factorial_zero, mul_one] at hm
  have he : IsEmpty (Marked (n := n) τ) := ⟨fun p => by
    have := distance_bound p
    omega⟩
  have ha : IsEmpty (Σ π : Perm n, Adj τ π) := ⟨fun p => he.false ⟨p.1,p.2.val⟩⟩
  have hl := lower_global (n := n) τ
  have hu := upper_global (n := n) τ
  have hzero : Fintype.card (Marked (n := n) τ) = 0 := Fintype.card_of_isEmpty
  have hzero' : Fintype.card (Σ π : Perm n, Adj τ π) = 0 := Fintype.card_of_isEmpty
  rw [hzero] at hl
  rw [hzero'] at hu
  have hh := avoid_add_contains (n := n) τ
  omega

theorem strict_avoidance {k n : ℕ} (hn : k < n) (τ : Perm k)
    (hinc : τ ≠ Equiv.refl _) (hdec : τ ≠ Fin.revPerm) :
    avoidCount n k τ < avoidCount n k (Equiv.refl _) := by
  have hk : 3 ≤ k := by
    by_contra! h
    exact (short_pattern (by omega) τ).elim hinc hdec
  have hm := first_moment (n := n) (show 0 < k by omega) (by omega) τ
  have hmi := first_moment (n := n) (show 0 < k by omega) (by omega) (Equiv.refl (Fin k))
  have hj := Fintype.card_congr (adjacent_equiv (n := n) (show 2 ≤ k by omega))
  have hji := first_moment (n := n) (Nat.succ_pos k) (show k+1 ≤ n by omega) (Equiv.refl (Fin (k+1)))
  rw [hji, show n-k.succ = n-k-1 by omega] at hj
  have hp := pairs_total τ hk hn hinc hdec
  unfold weight at hp
  have hl := lower_global (n := n) τ
  change Fintype.card (Occs (n := n) τ) ≤ containsCount (n := n) τ +
    Fintype.card (Marked (n := n) τ) at hl
  have hu := upper_global (n := n) (Equiv.refl (Fin k))
  have h₁ := avoid_add_contains (n := n) τ
  have h₂ := avoid_add_contains (n := n) (Equiv.refl (Fin k))
  omega

theorem claesson_conj_3_13 (k n : ℕ) (τ : Equiv.Perm (Fin k)) :
    avoidCount n k τ ≤ avoidCount n k (Equiv.refl _) := by
  by_cases hi : τ = Equiv.refl _
  · simp [hi]
  by_cases hd : τ = Fin.revPerm
  · rw [hd, rev_avoid]
  rcases lt_trichotomy k n with hn | he | hn
  · exact (strict_avoidance hn τ hi hd).le
  · subst k
    have hp : 0 < n := by
      by_contra! h
      exact (short_pattern (by omega) τ).elim hi hd
    have h₁ := avoid_same_length hp τ
    have h₂ := avoid_same_length hp (Equiv.refl (Fin n))
    omega
  · rw [avoid_too_short hn, avoid_too_short hn]

theorem claesson_source : ClaessonConjecture313 := claesson_conj_3_13

#check claesson_conj_3_13
#check claesson_source
#check strict_avoidance
#check avoid_empty
#check avoid_singleton
#check avoid_too_short
#check avoid_same_length
#check rev_avoid
#print axioms claesson_conj_3_13
#print axioms claesson_source
#print axioms strict_avoidance
#print axioms avoid_empty
#print axioms avoid_singleton
#print axioms avoid_too_short
#print axioms avoid_same_length
#print axioms rev_avoid

end
end Hertzsprung
```

