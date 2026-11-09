import Terminal
import Mathlib.Probability.ProbabilityMassFunction.Constructions
set_option autoImplicit false
set_option linter.unusedSimpArgs false
open scoped ENNReal
namespace LiteralGame
noncomputable def legalTypes (b : Board) : Finset Move := by
 classical
 exact (alphabet (value b)).filter (fun m => input m ≤ b)

theorem mem_legalTypes (b : Board) (m : Move) :
 m ∈ legalTypes b ↔ ∃ c, Step b m c := by
 classical
 simp only [legalTypes,Finset.mem_filter]
 constructor
 · exact fun h => (has_step_iff b m).mpr h.2
 · intro h
   exact ⟨step_in_alphabet h.choose_spec,(has_step_iff b m).mp h⟩

theorem live_types (b : Board) (h : ¬ Terminal b) : (legalTypes b).Nonempty := by
 classical
 simp only [Terminal,not_forall,not_not] at h
 obtain ⟨m,c,hs⟩ := h
 exact ⟨m,(mem_legalTypes b m).mpr ⟨c,hs⟩⟩

noncomputable def next (b : Board) (m : Move) : Board := b - input m + output m
theorem next_step {b : Board} {m : Move} (hm : m ∈ legalTypes b) : Step b m (next b m) := by
 have hl := (has_step_iff b m).mp ((mem_legalTypes b m).mp hm)
 exact ⟨b-input m,(Multiset.sub_add_cancel hl).symm,rfl⟩

noncomputable def typeLaw (b : Board) (h : (legalTypes b).Nonempty) : PMF Move := by
 classical
 exact PMF.ofFinset
   (fun m => if m ∈ legalTypes b then ((legalTypes b).card : ℝ≥0∞)⁻¹ else 0)
   (legalTypes b)
   (by simp only [Finset.sum_ite_mem,Finset.sum_const, nsmul_eq_mul]
       exact ENNReal.mul_inv_cancel (by exact_mod_cast h.card_pos.ne') (by simp))
   (by intro m hm; simp [hm])

theorem typeLaw_apply (b : Board) (h : (legalTypes b).Nonempty) (m : Move) :
 typeLaw b h m = if m ∈ legalTypes b then ((legalTypes b).card : ℝ≥0∞)⁻¹ else 0 := rfl

noncomputable def depthLaw : ℕ → Board → PMF (List Move)
 | 0, _ => PMF.pure []
 | d+1, b => by
   classical
   exact if ht : Terminal b then PMF.pure [] else
     (typeLaw b (live_types b ht)).bind
       (fun m => (depthLaw d (next b m)).map (List.cons m))

noncomputable def P (N : ℕ) : PMF (List Move) :=
 depthLaw (potential (initial N)).toNat (initial N)

theorem P_normalized (N : ℕ) : ∑' ms, P N ms = 1 := (P N).tsum_coe

theorem map_cons_apply (p : PMF (List Move)) (m : Move) (ms : List Move) :
 (p.map (List.cons m)) (m::ms) = p ms := by
 classical
 rw [PMF.map_apply]
 exact (tsum_eq_single ms (by intro x hx; simp [hx])).trans (by simp)

theorem map_cons_other (p : PMF (List Move)) (m k : Move) (ms : List Move)
 (h : k ≠ m) : (p.map (List.cons k)) (m::ms) = 0 := by
 classical
 simp [PMF.map_apply,h,Ne.symm h]

theorem depth_cons (d : ℕ) (b : Board) (ht : ¬ Terminal b) (m : Move) (ms : List Move) :
 depthLaw (d+1) b (m::ms) =
 (if m ∈ legalTypes b then ((legalTypes b).card : ℝ≥0∞)⁻¹ else 0) *
 depthLaw d (next b m) ms := by
 classical
 simp only [depthLaw,dif_neg ht,PMF.bind_apply]
 rw [tsum_eq_single m (by intro k hk; rw [map_cons_other _ _ _ _ hk,mul_zero])]
 rw [map_cons_apply,typeLaw_apply]

theorem depth_nil (d : ℕ) (b : Board) (ht : ¬ Terminal b) :
 depthLaw (d+1) b [] = 0 := by
 classical
 simp [depthLaw,ht,PMF.bind_apply,PMF.map_apply]
end LiteralGame
