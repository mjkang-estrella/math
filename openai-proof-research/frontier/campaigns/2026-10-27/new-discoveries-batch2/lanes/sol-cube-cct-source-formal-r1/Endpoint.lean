import Cube
import Mathlib.Data.Finset.Grade
namespace Cube
def gfun (v : V) : V := ⟨(if bit v 0 then 0 else 1) + (if bit v 4 then 2 else 0) +
    (if bit v 3 then 4 else 0) + (if bit v 1 then 8 else 0) + (if bit v 2 then 16 else 0), by
  split <;> split <;> split <;> split <;> split <;> decide⟩
theorem gfun_bijective : Function.Bijective gfun := by decide
noncomputable def g : V ≃ V := Equiv.ofBijective gfun gfun_bijective
def afun (x : Fin 5 → ℝ) : Fin 5 → ℝ := ![-x 0,x 4,x 3,x 1,x 2]
def bfun (x : Fin 5 → ℝ) : Fin 5 → ℝ := ![-x 0,x 3,x 4,x 2,x 1]
def A : (Fin 5 → ℝ) ≃ₗ[ℝ] (Fin 5 → ℝ) where
  toFun := afun
  invFun := bfun
  left_inv x := by ext i; fin_cases i <;> simp [afun,bfun]
  right_inv x := by ext i; fin_cases i <;> simp [afun,bfun]
  map_add' x y := by ext i; fin_cases i <;> simp [afun,add_comm]
  map_smul' c x := by ext i; fin_cases i <;> simp [afun]
theorem A_realizes : ∀ v, A (point v) = point (g v) := by
  have h : ∀ (v : V) (i : Fin 5), zcoord (gfun v) i =
      (![ -zcoord v 0,zcoord v 4,zcoord v 3,zcoord v 1,zcoord v 2] : Fin 5 → ℤ) i := by decide
  intro v
  ext i
  have hi := h v i
  change afun (point v) i = (zcoord (gfun v) i : ℝ)
  fin_cases i <;> dsimp [afun,point] at * <;> exact_mod_cast hi.symm
theorem orbit_witness : X.image g = Y := by
  change X.image gfun = Y
  decide
def IsCubeSymmetry (e : V ≃ V) : Prop :=
  ∃ A : (Fin 5 → ℝ) ≃ₗ[ℝ] (Fin 5 → ℝ), ∀ v, A (point v) = point (e v)
def SignCube (x : Fin 5 → ℝ) : Prop := ∀ i, x i = -1 ∨ x i = 1
theorem point_sign (v : V) : SignCube (point v) := by
  intro i
  simp only [point,zcoord]
  split <;> simp
theorem cube_encoding (x : Fin 5 → ℝ) : SignCube x ↔ ∃ v, point v = x := by
  constructor
  · intro hx
    classical
    have hs : Function.Surjective bit := by decide
    obtain ⟨v,hv⟩ := hs (fun i => decide (x i = -1))
    refine ⟨v, ?_⟩
    ext i
    have hi := congrFun hv i
    rcases hx i with h|h
    · simp [point,zcoord,hi,h]
    · norm_num [point,zcoord,hi,h]
  · rintro ⟨v,rfl⟩
    exact point_sign v
theorem full_group_bridge (B : (Fin 5 → ℝ) ≃ₗ[ℝ] (Fin 5 → ℝ))
    (hb : ∀ x, SignCube (B x) ↔ SignCube x) :
    ∃ e : V ≃ V, ∀ v, B (point v) = point (e v) := by
  classical
  have h : ∀ v, ∃ w, point w = B (point v) := fun v =>
    (cube_encoding _).mp ((hb _).mpr (point_sign v))
  choose f hf using h
  have hinj : Function.Injective f := by
    intro v w he
    apply point_injective
    apply B.injective
    rw [← hf v,← hf w,he]
  let e := Equiv.ofBijective f ⟨hinj,Finite.surjective_of_injective hinj⟩
  exact ⟨e,fun v => (hf v).symm⟩
theorem image_group_exact (e : V ≃ V) (he : IsCubeSymmetry e) :
    ∃ B : (Fin 5 → ℝ) ≃ₗ[ℝ] (Fin 5 → ℝ),
      (∀ x, SignCube (B x) ↔ SignCube x) ∧ ∀ v, B (point v) = point (e v) := by
  obtain ⟨B,hB⟩ := he
  refine ⟨B,?_,hB⟩
  intro x
  constructor
  · intro hx
    obtain ⟨w,hw⟩ := (cube_encoding _).mp hx
    apply (cube_encoding _).mpr
    refine ⟨e.symm w,B.injective ?_⟩
    simpa only [hB,Equiv.apply_symm_apply] using hw
  · rintro hx
    obtain ⟨v,rfl⟩ := (cube_encoding _).mp hx
    rw [hB]
    exact point_sign _
def CCT : Prop := ∀ U W T : Finset V, U ⋖ T → W ⋖ T →
    (∃ e : V ≃ V, IsCubeSymmetry e ∧ U.image e = W) →
    ∃ e : V ≃ V, IsCubeSymmetry e ∧ T.image e = T ∧ U.image e = W
theorem source_not_CCT : ¬ CCT := by
  intro hc
  obtain ⟨e,⟨B,hB⟩,hz,hxy⟩ := hc X Y Z (Finset.erase_covBy (by decide))
    (Finset.erase_covBy (by decide)) ⟨g,⟨A,A_realizes⟩,orbit_witness⟩
  exact obstruction e (weight_preserved e (rel_preserved e B hB)) hz hxy
def PreservesCube (B : (Fin 5 → ℝ) ≃ₗ[ℝ] (Fin 5 → ℝ)) : Prop :=
  ∀ x, SignCube (B x) ↔ SignCube x
def Transports (B : (Fin 5 → ℝ) ≃ₗ[ℝ] (Fin 5 → ℝ)) (U W : Finset V) : Prop :=
  ∀ v, v ∈ W ↔ ∃ u ∈ U, B (point u) = point v
theorem transports_iff (B : (Fin 5 → ℝ) ≃ₗ[ℝ] (Fin 5 → ℝ)) (e : V ≃ V)
    (hB : ∀ v, B (point v) = point (e v)) (U W : Finset V) :
    Transports B U W ↔ U.image e = W := by
  simp only [Transports,hB,point_injective.eq_iff]
  constructor
  · intro h
    ext v
    simpa only [Finset.mem_image] using (h v).symm
  · intro h v
    rw [← h]
    exact Finset.mem_image
def LiteralQuestion66AtFive : Prop := ∀ U W T : Finset V, U ⋖ T → W ⋖ T →
    (∃ B : (Fin 5 → ℝ) ≃ₗ[ℝ] (Fin 5 → ℝ), PreservesCube B ∧ Transports B U W) →
    ∃ B : (Fin 5 → ℝ) ≃ₗ[ℝ] (Fin 5 → ℝ),
      PreservesCube B ∧ Transports B T T ∧ Transports B U W
theorem literal_question66_false : ¬ LiteralQuestion66AtFive := by
  intro hc
  apply source_not_CCT
  intro U W T hU hW horb
  obtain ⟨e,he,hxy⟩ := horb
  obtain ⟨B,hcube,hB⟩ := image_group_exact e he
  obtain ⟨D,hD,hT,hUW⟩ := hc U W T hU hW
    ⟨B,hcube,(transports_iff B e hB U W).mpr hxy⟩
  obtain ⟨f,hf⟩ := full_group_bridge D hD
  exact ⟨f,⟨D,hf⟩,(transports_iff D f hf T T).mp hT,
    (transports_iff D f hf U W).mp hUW⟩
end Cube
