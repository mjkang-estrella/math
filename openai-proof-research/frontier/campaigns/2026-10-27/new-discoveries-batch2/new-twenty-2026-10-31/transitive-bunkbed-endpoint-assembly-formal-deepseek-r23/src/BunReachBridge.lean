/-
# Bunkbed E7 (r20): the literal Reach/state membership bridge

Main theorem `Bun.stf_reach_strong`: for `j < n`, a full outcome `ω`, a vertex
`i : Fin n` and a layer `σ`, membership of `i.val` in the layer-`σ` component of
the prefix state `stf n u.val j (wres n j ω)` is equivalent to
`u.val ≤ i.val ∧ i.val ≤ j ∧ Reach n ω (u,false) (i,σ)`.

The proof is the joint prefix induction prescribed by the review: state→Reach
uses the closed indicator forms `X ∨ (Z ∧ Y)` / `Y ∨ (Z ∧ X)`; Reach→state uses
an inner `ReflTransGen` derivation induction for endpoints at the new index
`j+1`, where a final vertical arc consumes the shorter derivation's
opposite-layer membership through the coupled `ind` equations.  No cyclic
rewriting of `reach_char` is used.
-/
import BunkbedBase
import BunState
import BunBridge
import BunReach
import BunOldStable
import BunNewIndicators
import BunHorWitness
import BunUpperSupport
import BunLowerSupport
import BunReachSupport

namespace Bun

/-- The joint prefix bridge, strong form with the lower-endpoint guard. -/
theorem stf_reach_strong (n : Nat) (u : Fin n) :
    ∀ (j : Nat), j < n → ∀ (ω : Out n) (i : Fin n) (σ : Bool),
      ((i : Nat) ∈ sval σ (stf n (u : Nat) j (wres n j ω))) ↔
        ((u : Nat) ≤ (i : Nat) ∧ (i : Nat) ≤ j ∧ Reach n ω (u, false) (i, σ)) := by
  intro j
  induction j with
  | zero =>
      intro hj ω i σ
      by_cases hu : (u : Nat) = 0
      · have hstf : stf n (u : Nat) 0 (wres n 0 ω) = startST n 0 (wres n 0 ω) := by
          simp only [stf]
          rw [ite_eq_left hu]
        cases σ with
        | false =>
            rw [hstf]
            have hs : sval false (startST n 0 (wres n 0 ω)) = (startST n 0 (wres n 0 ω)).1 := rfl
            rw [hs, startST_mem_fst]
            constructor
            · intro hk
              have hi : i = u := Fin.ext (hk.trans hu.symm)
              exact ⟨by omega, by omega, by rw [hi]; exact Relation.ReflTransGen.refl⟩
            · rintro ⟨-, hle, -⟩
              omega
        | true =>
            rw [hstf]
            have hs : sval true (startST n 0 (wres n 0 ω)) = (startST n 0 (wres n 0 ω)).2 := rfl
            rw [hs, startST_mem_snd]
            have hbit0 : wres n 0 ω (fresV (n := n) (m := 0) hj) = ω (vtok u) := by
              rw [wres_fresV]
              have hf : (⟨0, hj⟩ : Fin n) = u := Fin.ext (by simpa using hu.symm)
              rw [hf]
            have hex : (∃ h : 0 < n, wres n 0 ω (fresV (n := n) (m := 0) h) = true) ↔
                ω (vtok u) = true := by
              constructor
              · rintro ⟨h, hb⟩
                rw [fresV_bit_congr (wres n 0 ω) h hj] at hb
                rw [hbit0] at hb
                exact hb
              · intro hb
                exact ⟨hj, by rw [hbit0]; exact hb⟩
            rw [hex]
            constructor
            · rintro ⟨h0, hb⟩
              have hi : i = u := Fin.ext (h0.trans hu.symm)
              refine ⟨by omega, by omega, ?_⟩
              rw [hi]
              exact (reach_same_index n ω u true).mpr (Or.inr hb)
            · rintro ⟨-, hle, hreach⟩
              have hi : i = u := Fin.ext (by rw [hu]; omega)
              have hreach' : Reach n ω (u, false) (u, true) := by
                rw [hi] at hreach
                exact hreach
              have hb : ω (vtok u) = true := by
                rcases (reach_same_index n ω u true).mp hreach' with hf | hv
                · exact absurd hf (by simp)
                · exact hv
              exact ⟨by omega, hb⟩
      · have hstf : stf n (u : Nat) 0 (wres n 0 ω) = (∅, ∅) := by
          simp only [stf]
          rw [ite_eq_right hu]
        have hmem : ¬ ((i : Nat) ∈ sval σ (stf n (u : Nat) 0 (wres n 0 ω))) := by
          rw [hstf, sval_pair_empty]
          exact Finset.notMem_empty _
        constructor
        · intro h; exact absurd h hmem
        · rintro ⟨h1, h2, -⟩
          omega
  | succ j ih =>
      intro hj ω i σ
      have hjn : j < n := by omega
      by_cases hlt : j + 1 < (u : Nat)
      · have hstf : stf n (u : Nat) (j + 1) (wres n (j + 1) ω) = (∅, ∅) := by
          simp only [stf]
          rw [dite_eq_left hlt]
        have hmem : ¬ ((i : Nat) ∈ sval σ (stf n (u : Nat) (j + 1) (wres n (j + 1) ω))) := by
          rw [hstf, sval_pair_empty]
          exact Finset.notMem_empty _
        constructor
        · intro h; exact absurd h hmem
        · rintro ⟨h1, h2, -⟩
          omega
      · by_cases heq : j + 1 = (u : Nat)
        · have hstf : stf n (u : Nat) (j + 1) (wres n (j + 1) ω) =
              startST n (j + 1) (wres n (j + 1) ω) := by
            simp only [stf]
            rw [dite_eq_right (by omega : ¬ (j + 1 < (u : Nat))), dite_eq_left heq]
          have hbit : ∀ h : j + 1 < n,
              wres n (j + 1) ω (fresV (n := n) (m := j + 1) h) = ω (vtok u) := by
            intro h
            rw [wres_fresV]
            have hf : (⟨j + 1, h⟩ : Fin n) = u := Fin.ext (by simpa using heq)
            rw [hf]
          have hex : (∃ h : j + 1 < n,
              wres n (j + 1) ω (fresV (n := n) (m := j + 1) h) = true) ↔ ω (vtok u) = true := by
            constructor
            · rintro ⟨h, hb⟩
              rw [hbit h] at hb
              exact hb
            · intro hb
              exact ⟨hj, by rw [hbit hj]; exact hb⟩
          rw [hstf]
          by_cases hieq : (i : Nat) = j + 1
          · have hi : i = u := Fin.ext (hieq.trans heq)
            rw [hi]
            rw [show (u : Nat) = j + 1 from heq.symm]
            rw [startST_mem]
            simp only [true_and, le_refl]
            rw [reach_same_index (n := n) (ω := ω) (u := u) (σ := σ)]
            cases σ <;> simp [hex]
          · have hmem : ¬ ((i : Nat) ∈ sval σ (startST n (j + 1) (wres n (j + 1) ω))) := by
              rw [startST_mem]
              intro h
              exact hieq h.1
            constructor
            · intro h; exact absurd h hmem
            · rintro ⟨h1, h2, -⟩
              omega
        · have hu : (u : Nat) < j + 1 := by omega
          set R : Finset Nat := (stf n (u : Nat) j (wres n j ω)).1 with hRdef
          set S : Finset Nat := (stf n (u : Nat) j (wres n j ω)).2 with hSdef
          set X : Bool := hor (m := j + 1) hj R false (wres n (j + 1) ω) with hXdef
          set Y : Bool := hor (m := j + 1) hj S true (wres n (j + 1) ω) with hYdef
          set Z : Bool := wres n (j + 1) ω (fresV (n := n) (m := j + 1) hj) with hZdef
          have hC : stf n (u : Nat) (j + 1) (wres n (j + 1) ω) = stepU (j + 1) R S X Y Z := by
            have hbase : stf n (u : Nat) (j + 1) (wres n (j + 1) ω) =
                stepU (j + 1) (stf n (u : Nat) j (res n j (wres n (j + 1) ω))).1
                  (stf n (u : Nat) j (res n j (wres n (j + 1) ω))).2
                  (hor (m := j + 1) hj (stf n (u : Nat) j (res n j (wres n (j + 1) ω))).1 false
                    (wres n (j + 1) ω))
                  (hor (m := j + 1) hj (stf n (u : Nat) j (res n j (wres n (j + 1) ω))).2 true
                    (wres n (j + 1) ω))
                  (wres n (j + 1) ω (fresV (n := n) (m := j + 1) hj)) := by
              simp only [stf]
              rw [dite_eq_right (by omega : ¬ (j + 1 < (u : Nat))),
                dite_eq_right (by omega : ¬ (j + 1 = (u : Nat))), dite_eq_left hj]
            rw [hbase, show res n j (wres n (j + 1) ω) = wres n j ω from
              (wres_res (n := n) (j := j) ω).symm]
          have hnotR : ¬ (j + 1) ∈ R := by
            rw [hRdef]
            intro hh
            have := stf_upper_support n (u : Nat) j (j + 1) (wres n j ω) false hh
            omega
          have hnotS : ¬ (j + 1) ∈ S := by
            rw [hSdef]
            intro hh
            have := stf_upper_support n (u : Nat) j (j + 1) (wres n j ω) true hh
            omega
          have hconv : ∀ (τ : Bool) (k : Nat),
              k ∈ sval τ (R, S) ↔ k ∈ sval τ (stf n (u : Nat) j (wres n j ω)) := by
            intro τ k
            rw [hRdef, hSdef]
          have key : ∀ b : Vert n, Reach n ω (u, false) b → (b.1 : Nat) ≤ j + 1 →
              (b.1 : Nat) ∈ sval b.2 (stepU (j + 1) R S X Y Z) := by
            intro b hb
            induction hb with
            | refl =>
                intro _
                show (u : Nat) ∈ sval false (stepU (j + 1) R S X Y Z)
                rw [stepU_old_mem_iff (j + 1) (u : Nat) R S X Y Z false (by omega)]
                rw [hconv false (u : Nat)]
                exact (ih hjn ω u false).mpr ⟨le_refl _, by omega, Relation.ReflTransGen.refl⟩
            | @tail b c h1 h2 ihh =>
                obtain ⟨b1, b2⟩ := b
                obtain ⟨c1, c2⟩ := c
                intro hcle
                have hcle' : (c1 : Nat) ≤ j + 1 := hcle
                have ihh' : (b1 : Nat) ≤ j + 1 →
                    (b1 : Nat) ∈ sval b2 (stepU (j + 1) R S X Y Z) := ihh
                have h1le : (u : Nat) ≤ (b1 : Nat) := reach_ge h1
                have hbc : (b1 : Nat) ≤ (c1 : Nat) := arc_fst_le h2
                show (c1 : Nat) ∈ sval c2 (stepU (j + 1) R S X Y Z)
                by_cases hclt : (c1 : Nat) < j + 1
                · have hcne : (c1 : Nat) ≠ j + 1 := by omega
                  rw [stepU_old_mem_iff (j + 1) (c1 : Nat) R S X Y Z c2 hcne]
                  rw [hconv c2 (c1 : Nat)]
                  exact (ih hjn ω c1 c2).mpr
                    ⟨le_trans h1le hbc, by omega, Relation.ReflTransGen.tail h1 h2⟩
                · have hceq : (c1 : Nat) = j + 1 := by omega
                  rw [hceq]
                  rcases arc_cases h2 with ⟨hb2, hlt, hbit⟩ | ⟨hb1, hne, hbit⟩
                  · have hb2' : b2 = c2 := hb2
                    have hlt' : (b1 : Nat) < (c1 : Nat) := hlt
                    have hbit0 : ω (htok b1 c1 hlt' b2) = true := hbit
                    have hbm : (b1 : Nat) < j + 1 := by rw [← hceq]; exact hlt'
                    have hbne : (b1 : Nat) ≠ j + 1 := by omega
                    have hib : (b1 : Nat) ∈ sval b2 (stepU (j + 1) R S X Y Z) := ihh' (by omega)
                    rw [stepU_old_mem_iff (j + 1) (b1 : Nat) R S X Y Z b2 hbne] at hib
                    rw [hconv b2 (b1 : Nat)] at hib
                    rw [hb2'] at hib
                    have hbit' : wres n (j + 1) ω (fresH hj (b1 : Nat) hbm c2) = true := by
                      rw [wres_fresH]
                      have e : htok b1 c1 hlt' c2 =
                          htok ⟨(b1 : Nat), Nat.lt_trans hbm hj⟩ ⟨j + 1, hj⟩ hbm c2 :=
                        htok_congr rfl hceq hlt' hbm c2
                      rw [← e]
                      have hbitc : ω (htok b1 c1 hlt' c2) = true := by
                        rw [hb2'] at hbit0
                        exact hbit0
                      exact hbitc
                    cases c2 with
                    | false =>
                        have hX : X = true := by
                          rw [hXdef, hRdef]
                          exact (hor_iff hj (stf n (u : Nat) j (wres n j ω)).1 false
                            (wres n (j + 1) ω)).mpr ⟨(b1 : Nat), hbm, hib, hbit'⟩
                        exact (stepU_new_ind_fst (j + 1) R S X Y Z hnotR).mpr (ind_fst_or hX)
                    | true =>
                        have hY : Y = true := by
                          rw [hYdef, hSdef]
                          exact (hor_iff hj (stf n (u : Nat) j (wres n j ω)).2 true
                            (wres n (j + 1) ω)).mpr ⟨(b1 : Nat), hbm, hib, hbit'⟩
                        exact (stepU_new_ind_snd (j + 1) R S X Y Z hnotS).mpr (ind_snd_or hY)
                  · have hb1' : b1 = c1 := hb1
                    have hbit0 : ω (vtok b1) = true := hbit
                    have hbm : (b1 : Nat) = j + 1 := by rw [hb1']; exact hceq
                    have hib : (b1 : Nat) ∈ sval b2 (stepU (j + 1) R S X Y Z) := ihh' (by omega)
                    have hZ : Z = true := by
                      rw [hZdef, wres_fresV]
                      have hf : b1 = (⟨j + 1, hj⟩ : Fin n) := Fin.ext hbm
                      rw [← hf]
                      exact hbit0
                    cases b2 with
                    | false =>
                        have hc2 : c2 = true := by cases c2 <;> simp_all
                        rw [hbm] at hib
                        have hind1 : (ind X Y Z).1 = true :=
                          (stepU_new_ind_fst (j + 1) R S X Y Z hnotR).mp hib
                        rw [hc2]
                        exact (stepU_new_ind_snd (j + 1) R S X Y Z hnotS).mpr
                          (ind_snd_vert hZ hind1)
                    | true =>
                        have hc2 : c2 = false := by cases c2 <;> simp_all
                        rw [hbm] at hib
                        have hind2 : (ind X Y Z).2 = true :=
                          (stepU_new_ind_snd (j + 1) R S X Y Z hnotS).mp hib
                        rw [hc2]
                        exact (stepU_new_ind_fst (j + 1) R S X Y Z hnotR).mpr
                          (ind_fst_vert hZ hind2)
          by_cases hile : (i : Nat) ≤ j
          · have hstab : (i : Nat) ∈ sval σ (stf n (u : Nat) (j + 1) (wres n (j + 1) ω)) ↔
                (i : Nat) ∈ sval σ (stf n (u : Nat) j (wres n j ω)) := by
              rw [hC]
              rw [stepU_old_mem_iff (j + 1) (i : Nat) R S X Y Z σ (by omega)]
            rw [hstab, ih hjn ω i σ]
            constructor
            · rintro ⟨h1, -, h3⟩
              exact ⟨h1, by omega, h3⟩
            · rintro ⟨h1, -, h3⟩
              exact ⟨h1, by omega, h3⟩
          · by_cases hile2 : (i : Nat) ≤ j + 1
            · have hieq : (i : Nat) = j + 1 := by omega
              have hi : i = (⟨j + 1, hj⟩ : Fin n) := Fin.ext hieq
              rw [hi]
              constructor
              · intro hmem
                refine ⟨by omega, le_refl _, ?_⟩
                cases σ with
                | false =>
                    have hiff := stf_new_mem_fst_iff n (u : Nat) j (wres n (j + 1) ω) hu hj
                    rw [show res n j (wres n (j + 1) ω) = wres n j ω from
                      (wres_res (n := n) (j := j) ω).symm] at hiff
                    have hmem' : (j + 1) ∈ (stf n (u : Nat) (j + 1) (wres n (j + 1) ω)).1 := hmem
                    rcases hiff.mp hmem' with hx | ⟨hz, hy⟩
                    · rw [hor_iff] at hx
                      obtain ⟨k, hk, hkR, hkbit⟩ := hx
                      have hkreach : Reach n ω (u, false) (⟨k, Nat.lt_trans hk hj⟩, false) :=
                        ((ih hjn ω ⟨k, Nat.lt_trans hk hj⟩ false).mp hkR).2.2
                      have hbit : ω (htok ⟨k, Nat.lt_trans hk hj⟩ ⟨j + 1, hj⟩ hk false) = true := by
                        rwa [wres_fresH] at hkbit
                      exact Relation.ReflTransGen.trans hkreach
                        (Relation.ReflTransGen.single (arc_horiz' rfl hk hbit))
                    · have hvt : ω (vtok ⟨j + 1, hj⟩) = true := by
                        rwa [wres_fresV] at hz
                      rw [hor_iff] at hy
                      obtain ⟨k, hk, hkS, hkbit⟩ := hy
                      have hkreach : Reach n ω (u, false) (⟨k, Nat.lt_trans hk hj⟩, true) :=
                        ((ih hjn ω ⟨k, Nat.lt_trans hk hj⟩ true).mp hkS).2.2
                      have hbit : ω (htok ⟨k, Nat.lt_trans hk hj⟩ ⟨j + 1, hj⟩ hk true) = true := by
                        rwa [wres_fresH] at hkbit
                      have hstep1 : Reach n ω (u, false) (⟨j + 1, hj⟩, true) :=
                        Relation.ReflTransGen.trans hkreach
                          (Relation.ReflTransGen.single (arc_horiz' rfl hk hbit))
                      have hstep2 : Arc n ω (⟨j + 1, hj⟩, true) (⟨j + 1, hj⟩, false) :=
                        arc_vert (l := true) hvt
                      exact Relation.ReflTransGen.trans hstep1 (Relation.ReflTransGen.single hstep2)
                | true =>
                    have hiff := stf_new_mem_snd_iff n (u : Nat) j (wres n (j + 1) ω) hu hj
                    rw [show res n j (wres n (j + 1) ω) = wres n j ω from
                      (wres_res (n := n) (j := j) ω).symm] at hiff
                    have hmem' : (j + 1) ∈ (stf n (u : Nat) (j + 1) (wres n (j + 1) ω)).2 := hmem
                    rcases hiff.mp hmem' with hy | ⟨hz, hx⟩
                    · rw [hor_iff] at hy
                      obtain ⟨k, hk, hkS, hkbit⟩ := hy
                      have hkreach : Reach n ω (u, false) (⟨k, Nat.lt_trans hk hj⟩, true) :=
                        ((ih hjn ω ⟨k, Nat.lt_trans hk hj⟩ true).mp hkS).2.2
                      have hbit : ω (htok ⟨k, Nat.lt_trans hk hj⟩ ⟨j + 1, hj⟩ hk true) = true := by
                        rwa [wres_fresH] at hkbit
                      exact Relation.ReflTransGen.trans hkreach
                        (Relation.ReflTransGen.single (arc_horiz' rfl hk hbit))
                    · have hvt : ω (vtok ⟨j + 1, hj⟩) = true := by
                        rwa [wres_fresV] at hz
                      rw [hor_iff] at hx
                      obtain ⟨k, hk, hkR, hkbit⟩ := hx
                      have hkreach : Reach n ω (u, false) (⟨k, Nat.lt_trans hk hj⟩, false) :=
                        ((ih hjn ω ⟨k, Nat.lt_trans hk hj⟩ false).mp hkR).2.2
                      have hbit : ω (htok ⟨k, Nat.lt_trans hk hj⟩ ⟨j + 1, hj⟩ hk false) = true := by
                        rwa [wres_fresH] at hkbit
                      have hstep1 : Reach n ω (u, false) (⟨j + 1, hj⟩, false) :=
                        Relation.ReflTransGen.trans hkreach
                          (Relation.ReflTransGen.single (arc_horiz' rfl hk hbit))
                      have hstep2 : Arc n ω (⟨j + 1, hj⟩, false) (⟨j + 1, hj⟩, true) :=
                        arc_vert (l := false) hvt
                      exact Relation.ReflTransGen.trans hstep1 (Relation.ReflTransGen.single hstep2)
              · rintro ⟨-, -, hreach⟩
                rw [hC]
                exact key (⟨j + 1, hj⟩, σ) hreach (le_refl _)
            · have hmem : ¬ ((i : Nat) ∈ sval σ (stf n (u : Nat) (j + 1) (wres n (j + 1) ω))) := by
                intro h
                have := stf_upper_support n (u : Nat) (j + 1) (i : Nat) (wres n (j + 1) ω) σ h
                omega
              constructor
              · intro h; exact absurd h hmem
              · rintro ⟨-, hle, -⟩
                omega

/-- The literal bridge, without the redundant lower-endpoint guard. -/
theorem stf_reach_iff (n : Nat) (u : Fin n) (i : Fin n) (j : Nat) (hj : j < n) (σ : Bool)
    (ω : Out n) :
    ((i : Nat) ∈ sval σ (stf n (u : Nat) j (wres n j ω))) ↔
      ((i : Nat) ≤ j ∧ Reach n ω (u, false) (i, σ)) := by
  by_cases hui : (u : Nat) ≤ (i : Nat)
  · constructor
    · intro h
      have hs := (stf_reach_strong n u j hj ω i σ).mp h
      exact ⟨hs.2.1, hs.2.2⟩
    · intro h
      exact (stf_reach_strong n u j hj ω i σ).mpr ⟨hui, h.1, h.2⟩
  · have hlt : (i : Nat) < (u : Nat) := Nat.lt_of_not_le hui
    have hmem : ¬ ((i : Nat) ∈ sval σ (stf n (u : Nat) j (wres n j ω))) := by
      intro h
      have := stf_lower_support n (u : Nat) j (i : Nat) (wres n j ω) σ h
      omega
    have hreach : ¬ Reach n ω (u, false) (i, σ) := by
      intro h
      have hle : (u : Nat) ≤ (i : Nat) := reach_ge h
      omega
    constructor
    · intro h; exact absurd h hmem
    · intro h; exact absurd h.2 hreach

/-- Endpoint specialization `i = j`: at the window boundary, membership in the
layer-`σ` component of the prefix state is exactly literal Reach. -/
theorem stf_reach_endpoint (n : Nat) (u v : Fin n) (σ : Bool) (ω : Out n) :
    ((v : Nat) ∈ sval σ (stf n (u : Nat) (v : Nat) (wres n (v : Nat) ω))) ↔
      Reach n ω (u, false) (v, σ) := by
  have h := stf_reach_iff n u v (v : Nat) v.isLt σ ω
  simpa using h

/-- `v < u`: neither event can hold, by index monotonicity of `Reach`. -/
theorem reach_of_lt (n : Nat) (ω : Out n) (u v : Fin n) (σ : Bool)
    (h : (v : Nat) < (u : Nat)) :
    ¬ Reach n ω (u, false) (v, σ) := by
  intro hh
  have hle : (u : Nat) ≤ (v : Nat) := reach_ge hh
  omega

/-- `v = u`: the same-layer copy is always reachable, and the opposite-layer
copy exactly when the shared vertical token is retained. -/
theorem reach_self (n : Nat) (ω : Out n) (u : Fin n) (σ : Bool) :
    Reach n ω (u, false) (u, σ) ↔ (σ = false ∨ ω (vtok u) = true) :=
  reach_same_index n ω u σ

end Bun
