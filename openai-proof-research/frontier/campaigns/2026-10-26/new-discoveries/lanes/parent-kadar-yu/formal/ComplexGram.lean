import GramModel

namespace KadarYu

open Polynomial

theorem real_complex_normalized_gcd (p q : Polynomial ℝ) (hq : q ≠ 0) :
    (GCDMonoid.gcd p q).map Complex.ofRealHom =
      GCDMonoid.gcd (p.map Complex.ofRealHom) (q.map Complex.ofRealHom) := by
  classical
  let g := GCDMonoid.gcd p q
  let m := GCDMonoid.gcd (p.map Complex.ofRealHom) (q.map Complex.ofRealHom)
  have hg0 : g ≠ 0 := gcd_ne_zero_of_right hq
  have hgm : g.Monic := by
    have hh := Polynomial.monic_normalize (p := g) hg0
    simpa only [g, _root_.normalize_gcd] using hh
  have hqmap : q.map Complex.ofRealHom ≠ 0 := Polynomial.map_ne_zero hq
  have hmm : m.Monic := by
    have hh := Polynomial.monic_normalize (p := m) (gcd_ne_zero_of_right hqmap)
    simpa only [m, _root_.normalize_gcd] using hh
  have hpg : g * (p / g) = p :=
    EuclideanDomain.mul_div_cancel' hg0 (gcd_dvd_left _ _)
  have hqg : g * (q / g) = q :=
    EuclideanDomain.mul_div_cancel' hg0 (gcd_dvd_right _ _)
  obtain ⟨u, v, huv⟩ := isCoprime_div_gcd_div_gcd hq
  have hcomb : g = u * p + v * q := by
    calc
      _ = g * (u * (p / g) + v * (q / g)) := by rw [huv, mul_one]
      _ = u * (g * (p / g)) + v * (g * (q / g)) := by ring
      _ = _ := by rw [hpg, hqg]
  have hcombmap : g.map Complex.ofRealHom =
      u.map Complex.ofRealHom * p.map Complex.ofRealHom +
      v.map Complex.ofRealHom * q.map Complex.ofRealHom := by
    simpa only [Polynomial.map_add, Polynomial.map_mul] using
      congrArg (Polynomial.map Complex.ofRealHom) hcomb
  have hmd : m ∣ g.map Complex.ofRealHom := by
    rw [hcombmap]
    exact dvd_add (dvd_mul_of_dvd_right (gcd_dvd_left _ _) _)
      (dvd_mul_of_dvd_right (gcd_dvd_right _ _) _)
  have hgd : g.map Complex.ofRealHom ∣ m := by
    apply dvd_gcd
    · exact ⟨(p / g).map Complex.ofRealHom, by
        rw [← Polynomial.map_mul, hpg]⟩
    · exact ⟨(q / g).map Complex.ofRealHom, by
        rw [← Polynomial.map_mul, hqg]⟩
  exact Polynomial.eq_of_monic_of_associated (hgm.map _) hmm
    (associated_of_dvd_dvd hgd hmd)

noncomputable def gramModelReducedComplex (h : ℕ)
    (G : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ) (s : ℕ) : Polynomial ℂ :=
  (gramModelDeterminant h G s).map Complex.ofRealHom /
    GCDMonoid.gcd ((gramModelDeterminant h G 0).map Complex.ofRealHom)
      ((gramModelDeterminant h G 1).map Complex.ofRealHom)

theorem gramModelReducedComplex_eq (h : ℕ)
    (G : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ) (s : ℕ) :
    gramModelReducedComplex h G s = (gramModelReduced h G s).map Complex.ofRealHom := by
  have hn : gramModelDeterminant h G 1 ≠ 0 := by
    rw [gramModelDeterminant_eq]
    exact (Matrix.charpoly_monic _).ne_zero
  simp only [gramModelReducedComplex, gramModelReduced, Polynomial.map_div,
    real_complex_normalized_gcd _ _ hn]

theorem gramModelReducedComplex_eval_real (h : ℕ)
    (G : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ) (s : ℕ) (x : ℝ) :
    (gramModelReducedComplex h G s).eval (x : ℂ) =
      Complex.ofReal ((gramModelReduced h G s).eval x) := by
  rw [gramModelReducedComplex_eq]
  exact Polynomial.eval_map_apply Complex.ofRealHom x

theorem gramModelReducedComplex_squarefree (h : ℕ)
    {G : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ} (hG : G.IsHermitian) (s : ℕ) :
    Squarefree (gramModelReducedComplex h G s) := by
  rw [gramModelReducedComplex_eq]
  exact (PerfectField.separable_iff_squarefree.mpr
    ((gramModelReduced_root_distribution h hG).2.1 s)).map.squarefree

theorem gramModelReducedComplex_roots (h : ℕ)
    {G : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ} (hG : G.IsHermitian) (s : ℕ) :
    (gramModelReducedComplex h G s).roots =
      (gramModelReduced h G s).roots.map Complex.ofRealHom := by
  rw [gramModelReducedComplex_eq]
  exact (Polynomial.roots_map_of_injective_of_card_eq_natDegree Complex.ofReal_injective
    (gramModelReduced_splits h hG s).natDegree_eq_card_roots.symm).symm

theorem gramModelReducedComplex_roots_real (h : ℕ)
    {G : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ} (hG : G.IsHermitian)
    (s : ℕ) (z : ℂ) (hz : z ∈ (gramModelReducedComplex h G s).roots) : z.im = 0 := by
  rw [gramModelReducedComplex_roots h hG] at hz
  obtain ⟨x, _, rfl⟩ := Multiset.mem_map.mp hz
  rfl

theorem gramModelBoundaryComplex_squarefree (h : ℕ)
    {G : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ} (hG : G.IsHermitian) :
    Squarefree (X * gramModelReducedComplex h G 0 - gramModelReducedComplex h G 1) := by
  have he : X * gramModelReducedComplex h G 0 - gramModelReducedComplex h G 1 =
      (X * gramModelReduced h G 0 - gramModelReduced h G 1).map Complex.ofRealHom := by
    simp [gramModelReducedComplex_eq]
  rw [he]
  exact (PerfectField.separable_iff_squarefree.mpr
    (gramModelReduced_root_distribution h hG).1).map.squarefree

noncomputable def complexExteriorRootCount (p : Polynomial ℂ) : ℕ := by
  classical
  exact (p.roots.filter fun z => z ∉ Complex.ofReal '' Set.Icc (-2 : ℝ) 2).card

theorem gramModelReducedComplex_exterior (h : ℕ)
    {G : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ} (hG : G.IsHermitian) (s : ℕ) :
    complexExteriorRootCount (gramModelReducedComplex h G s) =
      exteriorRootCount (gramModelReduced h G s) := by
  classical
  rw [complexExteriorRootCount, gramModelReducedComplex_roots h hG, Multiset.filter_map,
    Multiset.card_map]
  unfold exteriorRootCount
  congr 1
  apply Multiset.filter_congr
  intro x _
  simp only [Function.comp_apply, Complex.ofRealHom_eq_coe, Set.mem_image,
    Complex.ofReal_inj, exists_eq_right]

theorem gramModelReducedComplex_root_distribution (h : ℕ)
    {G : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ} (hG : G.IsHermitian) :
    Squarefree (X * gramModelReducedComplex h G 0 - gramModelReducedComplex h G 1) ∧
    (∀ s, Squarefree (gramModelReducedComplex h G s)) ∧
    (∀ s z, z ∈ (gramModelReducedComplex h G s).roots → z.im = 0) ∧
    (∃ N C : ℕ, C ≤ 2 * (h + 1) ∧ ∀ s, N ≤ s →
      complexExteriorRootCount (gramModelReducedComplex h G s) = C) ∧
    Set.Icc (-2 : ℝ) 2 ⊆ closure
      {y : ℝ | y ∈ Set.Icc (-2 : ℝ) 2 ∧ ∃ s : ℕ,
        (gramModelReducedComplex h G s).eval (y : ℂ) = 0} := by
  refine ⟨gramModelBoundaryComplex_squarefree h hG,
    gramModelReducedComplex_squarefree h hG, gramModelReducedComplex_roots_real h hG, ?_, ?_⟩
  · obtain ⟨N, C, hC, hstab⟩ := (gramModelReduced_root_distribution h hG).2.2.1
    exact ⟨N, C, hC, fun s hs => (gramModelReducedComplex_exterior h hG s).trans (hstab s hs)⟩
  · simpa only [gramModelReducedComplex_eval_real, Complex.ofReal_eq_zero] using
      (gramModelReduced_root_distribution h hG).2.2.2

theorem common_factor_dvd_field {K : Type*} [Field K] {F a b d : Polynomial K}
    (hab : IsCoprime a b) (ha : d ∣ F * a) (hb : d ∣ F * b) : d ∣ F := by
  obtain ⟨u, v, huv⟩ := hab
  have he : F = u * (F * a) + v * (F * b) := by
    calc
      F = F * (u * a + v * b) := by rw [huv, mul_one]
      _ = _ := by ring
  rw [he]
  exact dvd_add (dvd_mul_of_dvd_right ha u) (dvd_mul_of_dvd_right hb v)

theorem common_monic_factor_field {K : Type*} [Field K]
    {F g p0 p1 q0 q1 : Polynomial K} (hF : F.Monic) (hg : g.Monic)
    (hp : IsCoprime p0 p1) (hq : IsCoprime q0 q1)
    (h0 : F * p0 = g * q0) (h1 : F * p1 = g * q1) : F = g := by
  have hgd : g ∣ F := common_factor_dvd_field hp ⟨q0, h0⟩ ⟨q1, h1⟩
  have hFd : F ∣ g := common_factor_dvd_field hq ⟨p0, h0.symm⟩ ⟨p1, h1.symm⟩
  exact Polynomial.eq_of_monic_of_associated hF hg (associated_of_dvd_dvd hFd hgd)

theorem gramModelReducedComplex_identification (h : ℕ)
    (G : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ)
    (F : Polynomial ℂ) (p : ℕ → Polynomial ℂ) (hF : F.Monic)
    (hcop : IsCoprime (p 0) (p 1))
    (hfac : ∀ s, (gramModelDeterminant h G s).map Complex.ofRealHom = F * p s) :
    ∀ s, p s = gramModelReducedComplex h G s := by
  have hdet : ∀ s, F * p s =
      (headTailCommonFactor h (-G) (-1)).map Complex.ofRealHom *
        (headTailReduced h (-G) (-1) s).map Complex.ofRealHom := by
    intro s
    rw [← hfac s, gramModelDeterminant_eq, headTailReduced_factor, Polynomial.map_mul]
  have he := common_monic_factor_field hF
    ((headTailCommonFactor_monic h (-G) (-1)).map Complex.ofRealHom) hcop
    ((headTailReduced_coprime h (-G) (-1) (by norm_num) 0).map
      (Polynomial.mapRingHom Complex.ofRealHom)) (hdet 0) (hdet 1)
  intro s
  rw [gramModelReducedComplex_eq, gramModelReduced_eq]
  have hh := hdet s
  rw [← he] at hh
  exact mul_left_cancel₀ hF.ne_zero hh

end KadarYu
