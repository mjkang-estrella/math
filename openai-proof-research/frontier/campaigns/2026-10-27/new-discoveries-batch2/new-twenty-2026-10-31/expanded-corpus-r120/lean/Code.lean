import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
namespace CodeCounterexample
abbrev K := ZMod 2
abbrev W := Fin 12 → K
abbrev M := Fin 6 → K
def enc (x : Nat) : W := fun i => ((x / 2 ^ i.val) % 2 : Nat)
def rows : Fin 6 → W := fun j => enc (#[3833,3574,1422,2637,210,225][j.val]!)
def coeff (t : Fin 64) : M := fun j => ((t.val / 2 ^ j.val) % 2 : Nat)
def G : M →ₗ[K] W :=
 { toFun := fun c => ∑ j, c j • rows j
   map_add' := by intro a b; simp [add_smul, Finset.sum_add_distrib]
   map_smul' := by intro a b; simp [Finset.smul_sum, mul_smul] }
def table : Fin 64 → Nat := fun t => (#[0,3833,3574,783,1422,2935,2168,1665,2637,1204,1979,2370,4035,314,565,3276,210,3627,3364,989,1372,2981,2218,1619,2719,1126,1897,2448,3857,488,743,3102,225,3608,3351,1006,1391,2966,2201,1632,2732,1109,1882,2467,3874,475,724,3117,51,3786,3525,828,1469,2884,2123,1714,2686,1159,1928,2417,4080,265,518,3327][t.val]!)
def word (t : Fin 64) : W := enc (table t)
def words : Finset W := Finset.univ.image word
def C : Submodule K W := G.range
 theorem coeff_surj : Function.Surjective coeff := by decide
 theorem table_correct : ∀ t : Fin 64, G (coeff t) = word t := by decide
 theorem mem_C (w : W) : w ∈ C ↔ w ∈ words := by
  constructor
  · rintro ⟨c, rfl⟩
    obtain ⟨t, rfl⟩ := coeff_surj c
    exact Finset.mem_image.mpr ⟨t, Finset.mem_univ _, (table_correct t).symm⟩
  · intro h
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp h
    exact ⟨coeff t, table_correct t⟩
#print axioms mem_C

def act (p : Equiv.Perm (Fin 12)) (w : W) : W := fun i => w (p.symm i)
def weight (w : W) : Nat := ∑ i, if w i = 1 then 1 else 0
def sig (i : Fin 12) (k : Fin 13) : Nat :=
 (words.filter (fun w => weight w = k.val ∧ w i = 1)).card
def Auto (p : Equiv.Perm (Fin 12)) : Prop := ∀ w, w ∈ C ↔ act p w ∈ C
 theorem act_weight (p : Equiv.Perm (Fin 12)) (w : W) : weight (act p w) = weight w := by
  unfold weight act
  exact Fintype.sum_equiv p.symm _ _ (fun _ => rfl)
 theorem act_inv (p : Equiv.Perm (Fin 12)) (w : W) : act p.symm (act p w) = w := by
  funext i
  simp [act]
 theorem signature_invariant (p : Equiv.Perm (Fin 12)) (h : Auto p) (i : Fin 12) : sig i = sig (p i) := by
  funext k
  unfold sig
  apply Finset.card_bij (fun w _ => act p w)
  · intro w hw
    simp only [Finset.mem_filter] at hw ⊢
    refine ⟨(mem_C _).mp ((h w).mp ((mem_C _).mpr hw.1)), ?_⟩
    simpa [act_weight, act] using hw.2
  · intro a _ b _ hab
    have := congrArg (act p.symm) hab
    simpa [act_inv] using this
  · intro w hw
    simp only [Finset.mem_filter] at hw
    refine ⟨act p.symm w, ?_, ?_⟩
    · simp only [Finset.mem_filter]
      refine ⟨(mem_C _).mp ((h _).mpr ?_), ?_⟩
      · have hc : act p (act p.symm w) = w := by funext j; simp [act]
        rw [hc]
        exact (mem_C _).mpr hw.1
      · simpa [act_weight, act] using hw.2
    · funext j
      simp [act]
 theorem sig_distinguishes : ∀ i j : Fin 12, sig i = sig j → i.val / 2 = j.val / 2 := by decide
 theorem preserves_pairs (p : Equiv.Perm (Fin 12)) (h : Auto p) (i : Fin 12) :
  (p i).val / 2 = i.val / 2 := (sig_distinguishes i (p i) (signature_invariant p h i)).symm
#print axioms preserves_pairs

def partner (i : Fin 12) : Fin 12 := ⟨if i.val % 2 = 0 then i.val+1 else i.val-1, by split <;> omega⟩
def even (j : Fin 6) : Fin 12 := ⟨2*j.val, by omega⟩
def pair (i : Fin 12) : Fin 6 := ⟨i.val/2, by omega⟩
def candidate (b : Fin 6 → Bool) (i : Fin 12) : Fin 12 := if b (pair i) then partner i else i
 theorem partner_pair : ∀ i : Fin 12, pair (partner i) = pair i := by decide
 theorem partner_twice : ∀ i : Fin 12, partner (partner i) = i := by decide
 theorem candidate_twice (b : Fin 6 → Bool) (i : Fin 12) : candidate b (candidate b i) = i := by
  unfold candidate
  split <;> simp_all [partner_pair, partner_twice]
def candidatePerm (b : Fin 6 → Bool) : Equiv.Perm (Fin 12) :=
 { toFun := candidate b, invFun := candidate b,
   left_inv := candidate_twice b, right_inv := candidate_twice b }
 theorem pair_options : ∀ i j : Fin 12, pair i = pair j → i = j ∨ i = partner j := by decide
 theorem even_options : ∀ i : Fin 12, i = even (pair i) ∨ i = partner (even (pair i)) := by decide
 theorem no_fixed : ∀ i : Fin 12, partner i ≠ i := by decide
 theorem perm_classify (p : Equiv.Perm (Fin 12))
  (h : ∀ i, pair (p i) = pair i) :
  ∃ b : Fin 6 → Bool, p = candidatePerm b := by
  let b : Fin 6 → Bool := fun j => decide (p (even j) = partner (even j))
  refine ⟨b, ?_⟩
  apply Equiv.ext
  intro i
  change p i = candidate b i
  obtain hi | hi := even_options i
  · have opts := pair_options (p i) i (h i)
    rcases opts with hp | hp
    · have hb : b (pair i) = false := by
        simp only [b, ← hi, hp, decide_eq_false_iff_not]
        exact (no_fixed i).symm
      simp [candidate, hb, hp]
    · have hb : b (pair i) = true := by simp [b, ← hi, hp]
      simp [candidate, hb, hp]
  · have he := h (even (pair i))
    obtain hp | hp := pair_options (p (even (pair i))) (even (pair i)) he
    · have hb : b (pair i) = false := by
        simp only [b, hp, decide_eq_false_iff_not]
        exact (no_fixed _).symm
      have opts := pair_options (p i) i (h i)
      rcases opts with hpi | hpi
      · simp [candidate, hb, hpi]
      · have hic : partner i = even (pair i) := (congrArg partner hi).trans (partner_twice _)
        have hbad : i = even (pair i) := p.injective (by rw [hpi, hic, hp])
        exact False.elim ((no_fixed (even (pair i))) (hi.symm.trans hbad))
    · have hb : b (pair i) = true := by simp [b, hp]
      have opts := pair_options (p i) i (h i)
      rcases opts with hpi | hpi
      · have hbad : i = even (pair i) := p.injective (by rw [hpi, hp, ← hi])
        exact False.elim ((no_fixed (even (pair i))) (hi.symm.trans hbad))
      · simp [candidate, hb, hpi]
#print axioms perm_classify

def sigma : Equiv.Perm (Fin 12) := candidatePerm (fun _ => true)
 theorem generators_mem : ∀ j : Fin 6, rows j ∈ words := by decide
 theorem swap_test : ∀ b : Fin 6 → Bool,
  (∀ j : Fin 6, act (candidatePerm b) (rows j) ∈ words) →
  b = (fun _ => false) ∨ b = (fun _ => true) := by decide
 theorem auto_classification (p : Equiv.Perm (Fin 12)) (h : Auto p) : p = 1 ∨ p = sigma := by
  obtain ⟨b, rfl⟩ := perm_classify p (fun i => Fin.ext (preserves_pairs p h i))
  have hb := swap_test b (fun j => (mem_C _).mp ((h _).mp ((mem_C _).mpr (generators_mem j))))
  rcases hb with hb | hb
  · left
    subst b
    apply Equiv.ext
    intro i
    rfl
  · right
    exact congrArg candidatePerm hb
 theorem sigma_words : ∀ t : Fin 64, act sigma (word t) ∈ words := by decide
 theorem sigma_twice (w : W) : act sigma (act sigma w) = w := by
  funext i
  change w (candidate (fun _ => true) (candidate (fun _ => true) i)) = w i
  rw [candidate_twice]
 theorem sigma_auto : Auto sigma := by
  have hforward : ∀ w, w ∈ C → act sigma w ∈ C := by
    intro w hw
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp ((mem_C _).mp hw)
    exact (mem_C _).mpr (sigma_words t)
  intro w
  constructor
  · exact hforward w
  · intro hw
    have hh := hforward _ hw
    simpa [sigma_twice] using hh
 theorem identity_auto : Auto 1 := by intro w; rfl
 theorem sigma_nontrivial : sigma ≠ 1 := by decide
 theorem sigma_free : ∀ i : Fin 12, sigma i ≠ i := no_fixed
 theorem sigma_square : sigma * sigma = 1 := by
  apply Equiv.ext
  exact partner_twice
#print axioms auto_classification
#print axioms sigma_auto

def paut (D : Submodule K W) : Subgroup (Equiv.Perm (Fin 12)) where
 carrier := {p | ∀ w, w ∈ D ↔ act p w ∈ D}
 one_mem' := by intro w; rfl
 mul_mem' := by
  intro p q hp hq w
  change (w ∈ D ↔ act (p*q) w ∈ D)
  have hc : act (p*q) w = act p (act q w) := rfl
  rw [hc]
  exact (hq w).trans (hp (act q w))
 inv_mem' := by
  intro p hp w
  have hh := hp (act p.symm w)
  have hc : act p (act p.symm w) = w := by funext i; simp [act]
  rw [hc] at hh
  exact hh.symm
 theorem paut_mem (p : Equiv.Perm (Fin 12)) : p ∈ paut C ↔ Auto p := Iff.rfl
 def s : paut C := ⟨sigma, sigma_auto⟩
 theorem s_square : s*s = 1 := Subtype.ext sigma_square
 theorem s_ne : s ≠ 1 := fun h => sigma_nontrivial (congrArg Subtype.val h)
 theorem K_options : ∀ x : K, x=0 ∨ x=1 := by decide
 theorem K_two : (1:K)+1=0 := by decide
 def theta : Multiplicative K →* paut C where
 toFun x := if x.toAdd = 0 then 1 else s
 map_one' := by rfl
 map_mul' := by
  intro a b
  change (if a.toAdd + b.toAdd = 0 then 1 else s) =
    (if a.toAdd = 0 then 1 else s) * (if b.toAdd = 0 then 1 else s)
  have ha : a.toAdd = 0 ∨ a.toAdd = 1 := K_options _
  have hb : b.toAdd = 0 ∨ b.toAdd = 1 := K_options _
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb, s_square, K_two]
 theorem theta_bijective : Function.Bijective theta := by
  constructor
  · intro a b hab
    change (if a.toAdd = 0 then (1:paut C) else s) = (if b.toAdd = 0 then 1 else s) at hab
    have ha : a.toAdd = 0 ∨ a.toAdd = 1 := K_options _
    have hb : b.toAdd = 0 ∨ b.toAdd = 1 := K_options _
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact congrArg Multiplicative.ofAdd (ha.trans hb.symm)
    · have he : (1 : paut C) = s := by simpa [ha, hb] using hab
      exact False.elim (s_ne he.symm)
    · have he : s = (1 : paut C) := by simpa [ha, hb] using hab
      exact False.elim (s_ne he)
    · exact congrArg Multiplicative.ofAdd (ha.trans hb.symm)
  · intro p
    obtain hp | hp := auto_classification p.val p.property
    · refine ⟨Multiplicative.ofAdd 0, ?_⟩
      apply Subtype.ext
      exact hp.symm
    · refine ⟨Multiplicative.ofAdd 1, ?_⟩
      apply Subtype.ext
      change (if (1:K)=0 then (1:Equiv.Perm (Fin 12)) else sigma) = p.val
      simpa using hp.symm
 noncomputable def codeIso : paut C ≃* Multiplicative K := (MulEquiv.ofBijective theta theta_bijective).symm
 theorem free_action : ∀ p : paut C, p ≠ 1 → ∀ i, p.val i ≠ i := by
  intro p hp i
  obtain h | h := auto_classification p.val p.property
  · exact False.elim (hp (Subtype.ext h))
  · rw [h]
    exact sigma_free i
 /-- A binary linear code of length 12 = 2*6 > 2 whose permutation automorphism
 group is C2 and itself acts freely on coordinates, hence a quasi-group code. -/
 theorem literal_counterexample :
  ∃ D : Submodule (ZMod 2) (Fin 12 → ZMod 2),
   Nonempty (paut D ≃* Multiplicative (ZMod 2)) ∧
   ∀ p : paut D, p ≠ 1 → ∀ i, p.val i ≠ i :=
  ⟨C, ⟨codeIso⟩, free_action⟩
#print axioms literal_counterexample

 /-- The source definition: a nontrivial free subgroup of the permutation automorphism group. -/
 def QuasiGroupCode (D : Submodule K W) : Prop :=
  ∃ H : Subgroup (Equiv.Perm (Fin 12)), H ≤ paut D ∧
   (∃ p : H, p ≠ 1) ∧ ∀ p : H, p ≠ 1 → ∀ i, p.val i ≠ i
 theorem source_conjecture_refuted :
  12 = 2*6 ∧ 2 < 12 ∧
  ∃ D : Submodule (ZMod 2) (Fin 12 → ZMod 2),
   QuasiGroupCode D ∧ Nonempty (paut D ≃* Multiplicative (ZMod 2)) := by
  refine ⟨rfl, by decide, C, ?_, ⟨codeIso⟩⟩
  exact ⟨paut C, le_rfl, ⟨s, s_ne⟩, free_action⟩
#print axioms source_conjecture_refuted
end CodeCounterexample
