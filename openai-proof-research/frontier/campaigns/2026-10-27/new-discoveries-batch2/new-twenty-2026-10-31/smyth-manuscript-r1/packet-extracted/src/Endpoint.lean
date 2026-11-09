import Bridges
import Counts
namespace Smyth1512
theorem not_conjecture15 : ¬ Conjecture15 := by
  intro hC
  obtain ⟨γ, hinj, hdom⟩ := hC 3 20 2 19 (by norm_num) (by norm_num)
  -- list image of an element of U^A_a × U^B_b
  let toL : ∀ {A a B b : ℕ}, (U A a × U B b) → List ℕ × List ℕ :=
    fun y => (List.ofFn y.1.1, List.ofFn y.2.1)
  have toL_inj : ∀ {A a B b : ℕ} (y y' : U A a × U B b), toL y = toL y' → y = y' := by
    intro A a B b y y' h
    simp only [toL, Prod.mk.injEq] at h
    exact Prod.ext (Subtype.ext (List.ofFn_injective h.1)) (Subtype.ext (List.ofFn_injective h.2))
  -- realisation of members of XL
  have real : ∀ p ∈ XL, ∃ x : U 3 19 × U 2 20, toL x = p := by
    intro p hp
    change p ∈ (comps 3 19) ×ˢ (comps 2 20) at hp
    have hp := List.mem_product.mp hp
    simp only [mem_comps] at hp
    obtain ⟨⟨h1l, h1s⟩, ⟨h2l, h2s⟩⟩ := hp
    refine ⟨(⟨toFun 3 p.1, (sum_toFun h1l).trans h1s⟩,
             ⟨toFun 2 p.2, (sum_toFun h2l).trans h2s⟩), ?_⟩
    change (List.ofFn (toFun 3 p.1), List.ofFn (toFun 2 p.2)) = p
    rw [ofFn_toFun h1l, ofFn_toFun h2l]
  classical
  -- the comparison map on lists
  let ψ : List ℕ × List ℕ → List ℕ × List ℕ := fun p =>
    if h : p ∈ XL then toL (γ (Classical.choose (real p h))) else ([], [])
  have hψ : ∀ p (h : p ∈ XL), ψ p = toL (γ (Classical.choose (real p h))) := by
    intro p h; simp [ψ, h]
  have maps : ∀ p ∈ SL.toFinset, ψ p ∈ TL.toFinset := by
    intro p hp
    rw [List.mem_toFinset, SL, List.mem_filter] at hp
    obtain ⟨hpX, hpD⟩ := hp
    set x := Classical.choose (real p hpX) with hx
    have hxp : toL x = p := Classical.choose_spec (real p hpX)
    rw [hψ p hpX, ← hx, List.mem_toFinset, TL, List.mem_filter]
    have hlenx : (sortL (p.1 ++ p.2)).length = 5 := by
      change p ∈ (comps 3 19) ×ˢ (comps 2 20) at hpX
      have hpX := List.mem_product.mp hpX
      simp only [mem_comps] at hpX
      rw [length_sortL, List.length_append, hpX.1.1, hpX.2.1]
    have hleny : (sortL ((toL (γ x)).1 ++ (toL (γ x)).2)).length = 5 := by
      simp [toL, length_sortL]
    refine ⟨?_, ?_⟩
    · simp only [YL, List.mem_product, mem_comps, toL, List.length_ofFn, List.sum_ofFn]
      exact ⟨⟨True.intro, (γ x).1.2⟩, ⟨True.intro, (γ x).2.2⟩⟩
    · have hd := hdom x
      unfold Dom at hd
      rw [rearr_concat, rearr_concat] at hd
      have hxp1 : List.ofFn x.1.1 = p.1 := congrArg Prod.fst hxp
      have hxp2 : List.ofFn x.2.1 = p.2 := congrArg Prod.snd hxp
      rw [hxp1, hxp2] at hd
      exact inDB_mono hlenx hleny hpD hd
  have injOn : Set.InjOn ψ (SL.toFinset : Set (List ℕ × List ℕ)) := by
    intro p hp q hq hpq
    simp only [Finset.mem_coe, List.mem_toFinset, SL, List.mem_filter] at hp hq
    rw [hψ p hp.1, hψ q hq.1] at hpq
    have := hinj (toL_inj _ _ hpq)
    rw [← Classical.choose_spec (real p hp.1), ← Classical.choose_spec (real q hq.1), this]
  have hcard := Finset.card_le_card_of_injOn ψ maps injOn
  rw [List.toFinset_card_of_nodup SL_nodup, SL_length] at hcard
  have hT : TL.toFinset.card ≤ 1134 := TL_length ▸ List.toFinset_card_le TL
  omega

end Smyth1512
