import PDTAR.Defs
namespace PDTAR
open Finset
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

theorem subset_closed (S : Finset V) : S ⊆ closed G S := fun _ h => (mem_closed G _ _).mpr (.inl h)
theorem subset_step (O : Finset V) : O ⊆ step G O := fun _ h => (mem_step G _ _).mpr (.inl h)

theorem closed_mono {S T : Finset V} (h : S ⊆ T) : closed G S ⊆ closed G T := by
  intro u hu
  rcases (mem_closed G _ _).mp hu with hu | ⟨v,hv,ha⟩
  · exact (mem_closed G _ _).mpr (.inl (h hu))
  · exact (mem_closed G _ _).mpr (.inr ⟨v,h hv,ha⟩)

theorem step_mono {O Q : Finset V} (h : O ⊆ Q) : step G O ⊆ step G Q := by
  intro u hu
  by_cases hq : u ∈ Q
  · exact subset_step G Q hq
  rcases (mem_step G _ _).mp hu with hu | ⟨v,hv,ha,huniq⟩
  · exact False.elim (hq (h hu))
  · exact (mem_step G _ _).mpr (.inr ⟨v,h hv,ha,fun w hw hn => huniq w hw (fun ho => hn (h ho))⟩)

theorem propagate_mono {O Q : Finset V} (h : O ⊆ Q) (n : ℕ) :
    propagate G O n ⊆ propagate G Q n := by
  induction n with
  | zero => exact h
  | succ n ih => exact step_mono G ih

theorem propagate_increasing (O : Finset V) : Monotone (propagate G O) :=
  monotone_nat_of_le_succ (fun n => subset_step G (propagate G O n))

theorem obs_increasing (S : Finset V) : Monotone (obs G S) := by
  apply monotone_nat_of_le_succ
  intro n
  cases n with
  | zero => exact subset_closed G S
  | succ n => exact subset_step G _

theorem obs_mono {S T : Finset V} (h : S ⊆ T) (n : ℕ) : obs G S n ⊆ obs G T n := by
  cases n with
  | zero => exact h
  | succ n => exact propagate_mono G (closed_mono G h) n

theorem isPD_mono {S T : Finset V} (h : S ⊆ T) (hp : IsPD G S) : IsPD G T := by
  obtain ⟨n,hn⟩ := hp
  exact ⟨n, univ_subset_iff.mp (hn ▸ obs_mono G h n)⟩

theorem isPD_univ : IsPD G univ := ⟨0,rfl⟩

theorem propagate_stable (O : Finset V) :
    ∃ n, n ≤ Fintype.card V ∧ step G (propagate G O n) = propagate G O n := by
  by_contra! hn
  have hc : ∀ n, n ≤ Fintype.card V + 1 → n ≤ (propagate G O n).card := by
    intro n
    induction n with
    | zero => intro _; omega
    | succ n ih =>
      intro hbound
      have he := hn n (by omega)
      have hs := subset_step G (propagate G O n)
      have hlt : (propagate G O n).card < (step G (propagate G O n)).card :=
        card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hs, Ne.symm he⟩)
      have hi := ih (by omega)
      change n + 1 ≤ (step G (propagate G O n)).card
      omega
  have h := hc (Fintype.card V + 1) (by omega)
  have hh := card_le_univ (propagate G O (Fintype.card V + 1))
  omega

theorem propagate_fixed {O : Finset V} (h : step G O = O) (n : ℕ) :
    propagate G O n = O := by
  induction n with
  | zero => rfl
  | succ n ih => simp [propagate, ih, h]

theorem erase_isPD (hG : NoIsolated G) (v : V) : IsPD G (univ.erase v) := by
  refine ⟨1, ?_⟩
  change closed G (univ.erase v) = univ
  apply eq_univ_of_forall
  intro u
  by_cases h : u = v
  · subst u
    obtain ⟨w,hw⟩ := hG v
    exact (mem_closed G _ _).mpr (.inr ⟨w, by simp [G.ne_of_adj hw.symm], hw.symm⟩)
  · exact subset_closed G _ (by simp [h])
end PDTAR
