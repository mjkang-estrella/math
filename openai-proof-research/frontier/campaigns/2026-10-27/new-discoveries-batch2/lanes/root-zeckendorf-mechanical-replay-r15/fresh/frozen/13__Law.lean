import Terminal
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
set_option autoImplicit false
set_option linter.unusedSimpArgs false
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

noncomputable def continuations : ℕ → Board → Finset (List Move)
 | 0, _ => {[]}
 | d+1, b => by
   classical
   exact if Terminal b then {[]} else
    (legalTypes b).biUnion (fun m => (continuations d (next b m)).image (List.cons m))

noncomputable def depthWeight : ℕ → Board → List Move → ℚ
 | 0, _, ms => if ms=[] then 1 else 0
 | d+1, b, ms => by
   classical
   exact if Terminal b then (if ms=[] then 1 else 0) else
    match ms with
    | [] => 0
    | m::rest => if m ∈ legalTypes b then
       ((legalTypes b).card : ℚ)⁻¹ * depthWeight d (next b m) rest else 0

theorem branches_disjoint (d : ℕ) (b : Board) :
 (legalTypes b : Set Move).PairwiseDisjoint
   (fun m => (continuations d (next b m)).image (List.cons m)) := by
 classical
 intro m hm k hk hmk
 apply Finset.disjoint_left.mpr
 intro ms hms hks
 obtain ⟨x,hx,hxe⟩ := Finset.mem_image.mp hms
 obtain ⟨y,hy,hye⟩ := Finset.mem_image.mp hks
 exact hmk (List.cons.inj (hxe.trans hye.symm)).1

theorem depth_normalized (d : ℕ) (b : Board) :
 ∑ ms ∈ continuations d b, depthWeight d b ms = 1 := by
 classical
 induction d generalizing b with
 | zero => simp [continuations,depthWeight]
 | succ d ih =>
   by_cases ht : Terminal b
   · simp [continuations,depthWeight,ht]
   · simp only [continuations,ite_eq_right ht]
     rw [Finset.sum_biUnion (branches_disjoint d b)]
     have hbranch : ∀ m ∈ legalTypes b,
       ∑ ms ∈ (continuations d (next b m)).image (List.cons m),
         depthWeight (d+1) b ms = ((legalTypes b).card : ℚ)⁻¹ := by
       intro m hm
       rw [Finset.sum_image (by intros x hx y hy h; exact List.cons.inj h |>.2)]
       simp only [depthWeight,ite_eq_right ht,ite_eq_left hm]
       rw [← Finset.mul_sum,ih,mul_one]
     rw [Finset.sum_congr rfl hbranch]
     simp only [Finset.sum_const,nsmul_eq_mul]
     exact mul_inv_cancel₀ (by exact_mod_cast (live_types b ht).card_pos.ne')

theorem depth_nonneg (d : ℕ) (b : Board) (ms : List Move) : 0 ≤ depthWeight d b ms := by
 classical
 induction d generalizing b ms with
 | zero => simp only [depthWeight]; split <;> norm_num
 | succ d ih =>
   by_cases ht : Terminal b
   · simp only [depthWeight,ite_eq_left ht]; split <;> norm_num
   · cases ms with
     | nil => simp [depthWeight,ht]
     | cons m ms =>
       simp only [depthWeight,ite_eq_right ht]
       split
       · exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (ih _ _)
       · exact le_rfl
theorem budget_zero_terminal (b : Board) (hp : Positive b)
 (hz : (potential b).toNat ≤ 0) : Terminal b := by
 intro m c hs
 have hc := potential_nonneg (step_positive hs hp)
 have hb := potential_nonneg hp
 have he := step_potential hs
 have hd : 0 < drop m := by cases m <;> simp [drop]
 omega

theorem next_budget {b : Board} {m : Move} {d : ℕ}
 (hp : Positive b) (hm : m ∈ legalTypes b) (hd : (potential b).toNat ≤ d+1) :
 (potential (next b m)).toNat ≤ d := by
 have hs := next_step hm
 have hc := potential_nonneg (step_positive hs hp)
 have hb := potential_nonneg hp
 have he := step_potential hs
 have hdrop : 0 < drop m := by cases m <;> simp [drop]
 omega

theorem terminal_executes {b c : Board} {ms : List Move} (ht : Terminal b)
 (he : Executes b ms c) : ms=[] ∧ c=b := by
 cases he with
 | nil => exact ⟨rfl,rfl⟩
 | cons hs _ => exact (ht _ _ hs).elim

theorem continuation_iff (d : ℕ) (b : Board) (hp : Positive b)
 (hd : (potential b).toNat ≤ d) (ms : List Move) :
 ms ∈ continuations d b ↔ ∃ c, Executes b ms c ∧ Terminal c := by
 classical
 induction d generalizing b ms with
 | zero =>
   have ht := budget_zero_terminal b hp hd
   simp only [continuations,Finset.mem_singleton]
   constructor
   · rintro rfl; exact ⟨b,Executes.nil b,ht⟩
   · rintro ⟨c,he,hc⟩; exact (terminal_executes ht he).1
 | succ d ih =>
   by_cases ht : Terminal b
   · simp only [continuations,ite_eq_left ht,Finset.mem_singleton]
     constructor
     · rintro rfl; exact ⟨b,Executes.nil b,ht⟩
     · rintro ⟨c,he,hc⟩; exact (terminal_executes ht he).1
   · simp only [continuations,ite_eq_right ht,Finset.mem_biUnion,Finset.mem_image]
     constructor
     · rintro ⟨m,hm,rest,hr,rfl⟩
       obtain ⟨c,he,hc⟩ := (ih (next b m) (step_positive (next_step hm) hp)
         (next_budget hp hm hd) rest).mp hr
       exact ⟨c,Executes.cons (next_step hm) he,hc⟩
     · rintro ⟨c,he,hc⟩
       cases he with
       | nil => exact (ht hc).elim
       | @cons a mid c m rest hs he =>
         have hm := (mem_legalTypes b m).mpr ⟨mid,hs⟩
         have hn := step_deterministic hs (next_step hm)
         subst mid
         exact ⟨m,hm,rest,(ih _ (step_positive (next_step hm) hp)
           (next_budget hp hm hd) rest).mpr ⟨c,he,hc⟩,rfl⟩

noncomputable def reciprocalProduct : Board → List Move → ℚ
 | _, [] => 1
 | b, m::rest => by
   classical
   exact if m ∈ legalTypes b then ((legalTypes b).card : ℚ)⁻¹ *
     reciprocalProduct (next b m) rest else 0

theorem depth_product (d : ℕ) (b : Board) (hp : Positive b)
 (hd : (potential b).toNat ≤ d) {ms : List Move} {c : Board}
 (he : Executes b ms c) (hc : Terminal c) :
 depthWeight d b ms = reciprocalProduct b ms := by
 classical
 induction d generalizing b ms c with
 | zero =>
   obtain ⟨rfl,rfl⟩ := terminal_executes (budget_zero_terminal b hp hd) he
   simp [depthWeight,reciprocalProduct]
 | succ d ih =>
   by_cases ht : Terminal b
   · obtain ⟨rfl,rfl⟩ := terminal_executes ht he
     simp [depthWeight,reciprocalProduct,ht]
   · cases he with
     | nil => exact (ht hc).elim
     | @cons a mid c m rest hs he =>
       have hm := (mem_legalTypes b m).mpr ⟨mid,hs⟩
       have hn := step_deterministic hs (next_step hm)
       subst mid
       simp only [depthWeight,ite_eq_right ht,ite_eq_left hm,reciprocalProduct]
       rw [ih _ (step_positive (next_step hm) hp)
         (next_budget hp hm hd) he hc]

noncomputable def completeDomain (N : ℕ) : Finset (List Move) :=
 continuations (potential (initial N)).toNat (initial N)
noncomputable def P (N : ℕ) (ms : List Move) : ℚ :=
 depthWeight (potential (initial N)).toNat (initial N) ms

theorem domain_exact (N : ℕ) (ms : List Move) :
 ms ∈ completeDomain N ↔ ms ∈ completeWords N :=
 continuation_iff _ _ (initial_positive N) (le_refl _) ms
theorem P_normalized (N : ℕ) : ∑ ms ∈ completeDomain N, P N ms = 1 :=
 depth_normalized _ _
theorem P_nonneg (N : ℕ) (ms : List Move) : 0 ≤ P N ms := depth_nonneg _ _ _
theorem P_product (N : ℕ) {ms : List Move} (h : ms ∈ completeWords N) :
 P N ms = reciprocalProduct (initial N) ms := by
 obtain ⟨c,he,hc⟩ := h
 exact depth_product _ _ (initial_positive N) (le_refl _) he hc
theorem P_zero (ms : List Move) : P 0 ms = if ms=[] then 1 else 0 := by
 simp [P,initial_potential,depthWeight]

theorem depth_outside (d : ℕ) (b : Board) (ms : List Move)
 (h : ms ∉ continuations d b) : depthWeight d b ms = 0 := by
 classical
 induction d generalizing b ms with
 | zero => simpa [continuations,depthWeight] using h
 | succ d ih =>
   by_cases ht : Terminal b
   · simpa [continuations,depthWeight,ht] using h
   · cases ms with
     | nil => simp [depthWeight,ht]
     | cons m rest =>
       by_cases hm : m ∈ legalTypes b
       · have hr : rest ∉ continuations d (next b m) := by
           intro hr
           apply h
           simp only [continuations,ite_eq_right ht,Finset.mem_biUnion,Finset.mem_image]
           exact ⟨m,hm,rest,hr,rfl⟩
         simp [depthWeight,ht,hm,ih _ _ hr]
       · simp [depthWeight,ht,hm]

theorem P_outside (N : ℕ) (ms : List Move) (h : ms ∉ completeWords N) : P N ms = 0 :=
 depth_outside _ _ _ (fun hm => h ((domain_exact N ms).mp hm))

noncomputable def legalCounts : Board → List Move → List ℕ
 | _, [] => []
 | b, m::rest => (legalTypes b).card :: legalCounts (next b m) rest

theorem execution_product {b c : Board} {ms : List Move} (he : Executes b ms c) :
 reciprocalProduct b ms = ((legalCounts b ms).map (fun k => (k:ℚ)⁻¹)).prod := by
 classical
 induction he with
 | nil => rfl
 | @cons b mid c m rest hs he ih =>
   have hm := (mem_legalTypes b m).mpr ⟨mid,hs⟩
   have hn := step_deterministic hs (next_step hm)
   subst mid
   simp [reciprocalProduct,legalCounts,hm,ih]

theorem P_point_mass (N : ℕ) {ms : List Move} (h : ms ∈ completeWords N) :
 P N ms = ((legalCounts (initial N) ms).map (fun k => (k:ℚ)⁻¹)).prod := by
 rw [P_product N h]
 obtain ⟨c,he,hc⟩ := h
 exact execution_product he

theorem completeDomain_zero : completeDomain 0 = {[]} := by
 simp [completeDomain,initial_potential,continuations]

theorem execution_product_pos {b c : Board} {ms : List Move} (he : Executes b ms c) :
 0 < reciprocalProduct b ms := by
 classical
 induction he with
 | nil => norm_num [reciprocalProduct]
 | @cons b mid c m rest hs he ih =>
   have hm := (mem_legalTypes b m).mpr ⟨mid,hs⟩
   have hn := step_deterministic hs (next_step hm)
   subst mid
   simp only [reciprocalProduct,ite_eq_left hm]
   exact mul_pos (inv_pos.mpr (by exact_mod_cast
     (Finset.card_pos.mpr ⟨m,hm⟩))) ih

theorem P_positive_iff (N : ℕ) (ms : List Move) :
 0 < P N ms ↔ ms ∈ completeWords N := by
 classical
 constructor
 · intro hp
   by_contra hn
   rw [P_outside N ms hn] at hp
   exact (lt_irrefl 0 hp)
 · intro hm
   rw [P_product N hm]
   obtain ⟨c,he,hc⟩ := hm
   exact execution_product_pos he
end LiteralGame
