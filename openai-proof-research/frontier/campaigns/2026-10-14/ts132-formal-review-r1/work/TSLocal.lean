import Mathlib

/- Copyright 2026 Myeongjin Kang. MIT.
Scoped finite and scalar support for TS132; not the full Boolean theorem. -/
namespace TSLocal

theorem tournament_card_le_three {α : Type*} (S : Finset α) (R : α → α → Prop)
    (hirr : ∀ a ∈ S, ¬ R a a)
    (htotal : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → R a b ∨ R b a)
    (hin : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, R a c → R b c → a = b) :
    S.card ≤ 3 := by
  classical
  obtain hS | ⟨a, ha⟩ := S.eq_empty_or_nonempty
  · simp [hS]
  let I := S.filter fun b => R b a
  let O := S.filter fun b => R a b
  have hI : I.card ≤ 1 := Finset.card_le_one.mpr (by
    intro b hb c hc
    exact hin b (Finset.mem_filter.mp hb).1 c (Finset.mem_filter.mp hc).1 a ha
      (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp hc).2)
  have hO : O.card ≤ 1 := Finset.card_le_one.mpr (by
    intro b hb c hc
    obtain ⟨hbS, hab⟩ := Finset.mem_filter.mp hb
    obtain ⟨hcS, hac⟩ := Finset.mem_filter.mp hc
    by_contra hbc
    rcases htotal b hbS c hcS hbc with hbcR | hcbR
    · have habEq := hin a ha b hbS c hcS hac hbcR
      exact hirr b hbS (habEq ▸ hab)
    · have hacEq := hin a ha c hcS b hbS hab hcbR
      exact hirr c hcS (hacEq ▸ hac))
  have hsub : S ⊆ insert a (I ∪ O) := by
    intro b hb
    by_cases hba : b = a
    · simp [hba]
    · rcases htotal b hb a ha hba with hbaR | habR
      · exact Finset.mem_insert_of_mem (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hb, hbaR⟩))
      · exact Finset.mem_insert_of_mem (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hb, habR⟩))
  have hcard := Finset.card_le_card hsub
  have hstep := Finset.card_insert_le a (I ∪ O)
  have hunion := Finset.card_union_le I O
  omega

theorem fiber_card_bound {α β : Type*} (S : Finset α) (f : α → β) (a b : ℕ)
    [DecidableEq β] (himage : (S.image f).card ≤ a)
    (hfiber : ∀ y ∈ S.image f, (S.filter fun x => f x = y).card ≤ b) :
    S.card ≤ a * b := by
  calc
    S.card = ∑ y ∈ S.image f, (S.filter fun x => f x = y).card :=
      Finset.card_eq_sum_card_image f S
    _ ≤ ∑ _y ∈ S.image f, b := Finset.sum_le_sum hfiber
    _ = (S.image f).card * b := by simp
    _ ≤ a*b := Nat.mul_le_mul_right b himage

universe u

def Word (K : Type u) : ℕ → Type u
  | 0 => PUnit
  | h+1 => K × Word K h

instance wordDecidableEq {K : Type u} [DecidableEq K] (h : ℕ) : DecidableEq (Word K h) := by
  induction h with
  | zero => exact inferInstanceAs (DecidableEq PUnit)
  | succ h ih =>
      change DecidableEq (K × Word K h)
      letI := ih
      infer_instance

def edgeLabel {K : Type*} [Sub K] [DecidableEq K] (R : K → K → Prop)
    [DecidableRel R] : (h : ℕ) → Word K h → Word K h → Option K
  | 0, _, _ => none
  | h+1, u, v => if u.1 = v.1 then edgeLabel R h u.2 v.2
      else if R u.1 v.1 then some (v.1-u.1) else none

def HeadConstant {K : Type*} [Sub K] [DecidableEq K] (R : K → K → Prop)
    [DecidableRel R] (h : ℕ) (S : Finset (Word K h)) : Prop :=
  ∃ m : Word K h → K, ∀ u ∈ S, ∀ v ∈ S, ∀ c,
    edgeLabel R h u v = some c → c = m v

theorem head_fiber_constant {K : Type*} [Sub K] [DecidableEq K]
    (R : K → K → Prop) [DecidableRel R] (h : ℕ)
    (S : Finset (Word K (h+1))) (hc : HeadConstant R (h+1) S) (a : K) :
    HeadConstant R h ((S.filter fun v => v.1 = a).image Prod.snd) := by
  classical
  obtain ⟨m, hm⟩ := hc
  refine ⟨fun v => m (a,v), ?_⟩
  intro u hu v hv c he
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨hxS, hxa⟩ := Finset.mem_filter.mp hx
  obtain ⟨hyS, hya⟩ := Finset.mem_filter.mp hy
  have hxy : x.1 = y.1 := hxa.trans hya.symm
  have he' : edgeLabel R (h+1) x y = some c := by
    simpa only [edgeLabel, hxy, ite_true] using he
  have hh := hm x hxS y hyS c he'
  simpa only [← hya, Prod.eta] using hh

theorem head_image_indegree {K : Type*} [AddGroup K] [DecidableEq K]
    (R : K → K → Prop) [DecidableRel R] (hirr : ∀ a, ¬ R a a) (h : ℕ)
    (S : Finset (Word K (h+1))) (hc : HeadConstant R (h+1) S) :
    ∀ a ∈ S.image Prod.fst, ∀ b ∈ S.image Prod.fst, ∀ c ∈ S.image Prod.fst,
      R a c → R b c → a = b := by
  classical
  obtain ⟨m, hm⟩ := hc
  intro a ha b hb c hc hac hbc
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hc
  have huw : u.1 ≠ w.1 := by intro he; exact hirr w.1 (he ▸ hac)
  have hvw : v.1 ≠ w.1 := by intro he; exact hirr w.1 (he ▸ hbc)
  have h1 := hm u hu w hw (w.1-u.1) (by simp [edgeLabel, huw, hac])
  have h2 := hm v hv w hw (w.1-v.1) (by simp [edgeLabel, hvw, hbc])
  exact sub_right_inj.mp (h1.trans h2.symm)

theorem head_constant_card {K : Type*} [AddGroup K] [DecidableEq K]
    (R : K → K → Prop) [DecidableRel R] (hirr : ∀ a, ¬ R a a)
    (htotal : ∀ a b, a ≠ b → R a b ∨ R b a)
    (h : ℕ) (S : Finset (Word K h)) (hc : HeadConstant R h S) :
    S.card ≤ 3^h := by
  classical
  induction h with
  | zero =>
      have hS : S.card ≤ 1 := Finset.card_le_one.mpr (by
        intro a _ b _
        exact @Subsingleton.elim PUnit inferInstance a b)
      simpa using hS
  | succ h ih =>
      have hhead : (S.image Prod.fst).card ≤ 3 :=
        tournament_card_le_three _ R (fun a _ => hirr a)
          (fun a _ b _ hn => htotal a b hn) (head_image_indegree R hirr h S hc)
      have hfiber : ∀ a ∈ S.image Prod.fst, (S.filter fun v => v.1 = a).card ≤ 3^h := by
        intro a _
        have htail := ih ((S.filter fun v => v.1 = a).image Prod.snd)
          (head_fiber_constant R h S hc a)
        have hinj : Set.InjOn Prod.snd (↑(S.filter fun v => v.1 = a) : Set (Word K (h+1))) := by
          intro u hu v hv he
          exact Prod.ext ((Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm) he
        rw [Finset.card_image_of_injOn hinj] at htail
        exact htail
      simpa [pow_succ, Nat.mul_comm] using fiber_card_bound S Prod.fst 3 (3^h) hhead hfiber

theorem head_constant_four {K : Type*} [AddGroup K] [DecidableEq K]
    (R : K → K → Prop) [DecidableRel R] (hirr : ∀ a, ¬ R a a)
    (htotal : ∀ a b, a ≠ b → R a b ∨ R b a)
    (S : Finset (Word K 4)) (hc : HeadConstant R 4 S) : S.card < 82 := by
  have hh := head_constant_card R hirr htotal 4 S hc
  norm_num at hh
  omega

def affineVector {K ι : Type*} [Mul K] [Add K] (a : K) (b v : ι → K) : ι → K :=
  fun i => a * v i + b i

theorem affine_difference {K ι : Type*} [CommRing K] (a : K) (b v w : ι → K) (i : ι) :
    affineVector a b w i - affineVector a b v i = a * (w i - v i) := by
  simp only [affineVector]
  ring

theorem affine_coordinate_eq_iff {K ι : Type*} [Field K] (a : K) (ha : a ≠ 0)
    (b v w : ι → K) (i : ι) :
    affineVector a b v i = affineVector a b w i ↔ v i = w i := by
  simp [affineVector, ha]

theorem affine_first_difference {K ι : Type*} [Field K] [Preorder ι]
    (a : K) (ha : a ≠ 0) (b v w : ι → K) (j : ι)
    (hbefore : ∀ i < j, v i = w i) (hat : v j ≠ w j) :
    (∀ i < j, affineVector a b v i = affineVector a b w i) ∧
    affineVector a b v j ≠ affineVector a b w j ∧
    affineVector a b w j - affineVector a b v j = a*(w j-v j) := by
  refine ⟨?_, ?_, affine_difference a b v w j⟩
  · intro i hi
    exact (affine_coordinate_eq_iff a ha b v w i).mpr (hbefore i hi)
  · exact fun he => hat ((affine_coordinate_eq_iff a ha b v w j).mp he)

def rowPositionMap {K ι : Type*} [Field K] (H : Subgroup Kˣ)
    (a : H) (b : ι → K) (x : (ι → K) × H) : (ι → K) × H :=
  (affineVector (a : Kˣ) b x.1, a*x.2)

theorem rowPosition_injective {K ι : Type*} [Field K] (H : Subgroup Kˣ)
    (a : H) (b : ι → K) : Function.Injective (rowPositionMap H a b) := by
  intro x y he
  apply Prod.ext
  · funext i
    have hi := congrFun (congrArg Prod.fst he) i
    exact (affine_coordinate_eq_iff ((a : Kˣ) : K) (Units.ne_zero _) b x.1 y.1 i).mp hi
  · exact mul_left_cancel (congrArg Prod.snd he)

theorem rowPosition_transitive {K ι : Type*} [Field K] (H : Subgroup Kˣ)
    (x y : (ι → K) × H) :
    ∃ a : H, ∃ b : ι → K, rowPositionMap H a b x = y := by
  let a : H := y.2*x.2⁻¹
  refine ⟨a, fun i => y.1 i - (a : Kˣ)*x.1 i, ?_⟩
  apply Prod.ext
  · funext i
    simp [rowPositionMap, affineVector]
  · simp [rowPositionMap, a]

theorem rowPosition_comp {K ι : Type*} [Field K] (H : Subgroup Kˣ)
    (a c : H) (b d : ι → K) (x : (ι → K) × H) :
    rowPositionMap H a b (rowPositionMap H c d x) =
      rowPositionMap H (a*c) (affineVector (a : Kˣ) b d) x := by
  apply Prod.ext
  · funext i
    simp only [rowPositionMap, affineVector, Subgroup.coe_mul, Units.val_mul]
    ring
  · simp [rowPositionMap, mul_assoc]

theorem rowPosition_one {K ι : Type*} [Field K] (H : Subgroup Kˣ)
    (x : (ι → K) × H) : rowPositionMap H 1 (fun _ => 0) x = x := by
  apply Prod.ext
  · funext i
    simp [rowPositionMap, affineVector]
  · simp [rowPositionMap]

theorem rowPosition_left_inverse {K ι : Type*} [Field K] (H : Subgroup Kˣ)
    (a : H) (b : ι → K) :
    Function.LeftInverse
      (rowPositionMap H a⁻¹ (fun i => -((a⁻¹ : H) : Kˣ)*b i))
      (rowPositionMap H a b) := by
  intro x
  rw [rowPosition_comp]
  have hz : affineVector (((a⁻¹ : H) : Kˣ) : K)
      (fun i => -((a⁻¹ : H) : Kˣ)*b i) b = fun _ => 0 := by
    funext i
    simp [affineVector]
  rw [hz, inv_mul_cancel]
  exact rowPosition_one H x

noncomputable def profileEnvelope (L ε : ℝ) (n : ℕ) : ℝ :=
  L + ε*L*((3/2:ℝ)*(3^n-1)-n)

theorem envelope_le_two {L ε : ℝ} {n d : ℕ} (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (hnd : n ≤ d) (hsmall : ε*3^(d+1) ≤ 2) :
    profileEnvelope L ε n ≤ 2*L := by
  have hp : (3:ℝ)^(n+1) ≤ 3^(d+1) := by
    gcongr
    norm_num
  have hnsmall : ε*3^(n+1) ≤ 2 :=
    (mul_le_mul_of_nonneg_left hp hε).trans hsmall
  have hh := mul_le_mul_of_nonneg_right hnsmall hL
  have hεL : 0 ≤ ε*L := mul_nonneg hε hL
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
  have hprod := mul_nonneg hεL hn
  rw [pow_succ] at hh
  unfold profileEnvelope
  nlinarith

theorem coupled_profiles {L ε : ℝ} {d : ℕ} (u v : ℕ → ℝ)
    (hL : 0 ≤ L) (hε : 0 ≤ ε) (hsmall : ε*3^(d+1) ≤ 2)
    (hu0 : u 0 ≤ L) (hv0 : v 0 ≤ 0)
    (hu : ∀ n < d, u (n+1) ≤ (1+ε)*u n + 3*v n)
    (hv : ∀ n < d, v (n+1) ≤ ε*u n + 3*v n) :
    ∀ n ≤ d, u n ≤ profileEnvelope L ε n ∧
      v n ≤ ε*L*(3^n-1) ∧ u n ≤ 2*L := by
  intro n
  induction n with
  | zero =>
      intro _
      exact ⟨by simpa [profileEnvelope] using hu0, by simpa using hv0, by linarith⟩
  | succ n ih =>
      intro hn
      obtain ⟨huE, hvE, huTwo⟩ := ih (by omega)
      have hmul := mul_le_mul_of_nonneg_left huTwo hε
      have hun := hu n (by omega)
      have hvn := hv n (by omega)
      have hnext : u (n+1) ≤ profileEnvelope L ε (n+1) := by
        simp only [profileEnvelope, pow_succ, Nat.cast_add, Nat.cast_one] at huE ⊢
        nlinarith
      refine ⟨hnext, ?_, hnext.trans (envelope_le_two hL hε hn hsmall)⟩
      simp only [pow_succ]
      nlinarith

theorem normalize_one_side {A r M ε u v s j : ℝ}
    (hM : 0 < M) (hA : A ≤ M^2)
    (hrε : r/M ≤ ε) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : s ≤ A*u/M^2 + r*u/M) (hj : j ≤ A*v/M^2 + r*u/M) :
    s ≤ (1+ε)*u ∧ j ≤ v+ε*u := by
  have hM2 : 0 < M^2 := sq_pos_of_pos hM
  have hAM : A/M^2 ≤ 1 := (div_le_one hM2).mpr hA
  have hfirst := mul_le_mul_of_nonneg_right hAM hu
  have hsecond := mul_le_mul_of_nonneg_right hAM hv
  have hthird := mul_le_mul_of_nonneg_right hrε hu
  simp only [div_eq_mul_inv] at hs hj hfirst hsecond hthird
  constructor <;> nlinarith [hfirst, hsecond, hthird]

theorem normalized_zero_side {t M ε u v s j : ℝ}
    (htε : t/M ≤ ε) (hu : 0 ≤ u)
    (hs : s ≤ (t/M)*u + u + 3*v) (hj : j ≤ (t/M)*u + 3*v) :
    s ≤ (1+ε)*u+3*v ∧ j ≤ ε*u+3*v := by
  have hh := mul_le_mul_of_nonneg_right htε hu
  constructor <;> nlinarith

theorem strict_seed_numbers : (2:ℕ)^20 * 1936 < 3^20 := by norm_num

theorem strict_seed_ratio : (1:ℝ) < (3/2:ℝ)^20 / (4*(20+2)^2) := by norm_num

theorem strict_seed_from_ratio {A B : ℝ} (hA : 0 < A)
    (h : (3/2:ℝ)^20 / (4*(20+2)^2) ≤ B/A^2) : A^2 < B := by
  have hh := lt_of_lt_of_le strict_seed_ratio h
  exact (one_lt_div (sq_pos_of_pos hA)).mp hh

theorem strict_seed_parameters {M k : ℝ} (hM : 0 < M) (hk : 3*M^2 ≤ 2*k) :
    (44*M^21)^2 < M^2*k^20 := by
  have hbase : (3/2:ℝ)*M^2 ≤ k := by linarith
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (3/2:ℝ)*M^2) hbase 20
  have hmul := mul_le_mul_of_nonneg_left hp (sq_nonneg M)
  have hpos : 0 < M^42 := pow_pos hM 42
  norm_num [mul_pow, pow_mul] at hmul
  nlinarith

end TSLocal
