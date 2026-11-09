import Chord6Final
namespace Chord.Round7
open Comb4 Model2
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

/-- The six new half-edges, in the order Pp,Np,Cp,Pq,Nq,Cq. -/
def endDart {n : Nat} (k : Fin 6) : Fin (6*(n+1)) := ⟨6*n+k.val, by omega⟩

def oldDart {n : Nat} (i : Fin (6*n)) : Fin (6*(n+1)) := ⟨i.val, by omega⟩

private theorem side_old {n} (c : Sides n) (p q : Bool) (i : Nat) (hi : i < 2*n) :
    side (appendSides c p q) i = side c i := by
  simp [side, appendSides, hi, show i < 2*(n+1) by omega]

private theorem side_p {n} (c : Sides n) (p q : Bool) :
    side (appendSides c p q) (2*n) = p := by simp [side, appendSides, show 2*n+1 < 2*(n+1) by omega]
private theorem side_q {n} (c : Sides n) (p q : Bool) :
    side (appendSides c p q) (2*n+1) = q := by simp [side, appendSides, show 2*n+1 < 2*(n+1) by omega]

private theorem rho_at {n} (c : Sides n) (i k : Nat) (hk : k < 3) :
    rho c (3*i+k) = 3*i + if side c i then
      (match k with | 0 => 2 | 1 => 0 | _ => 1)
      else (match k with | 0 => 1 | 1 => 2 | _ => 0) := by
  simp only [rho, show (3*i+k)/3 = i by omega, show (3*i+k)%3 = k by omega]
  have hh : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hh with rfl | rfl | rfl <;> rfl

/-- The two old outgoing end-edge transitions land at the new endpoints. -/
theorem append_face_zero (n) (hn : 3 ≤ n) (c : Sides n) (p q : Bool) :
    face (r3Block (n+1) (by omega)) (appendSides c p q) 0 =
      6*n + if q then 3 else 5 := by
  unfold face theta
  simp only [Nat.zero_div, Nat.zero_mod]
  rw [show (0+2*(n+1)-1)%(2*(n+1)) = 2*n+1 by rw [show 0+2*(n+1)-1 = 2*n+1 by omega]; exact Nat.mod_eq_of_lt (by omega)]
  rw [show 3*(2*n+1)+1 = 3*(2*n+1)+1 by rfl, rho_at _ _ _ (by decide), side_q]
  cases q <;> simp <;> omega

theorem append_face_last (n) (hn : 3 ≤ n) (c : Sides n) (p q : Bool) :
    face (r3Block (n+1) (by omega)) (appendSides c p q) (6*n-2) =
      6*n + if p then 2 else 1 := by
  have hv : (6*n-2)/3 = 2*n-1 := by omega
  have hm : (6*n-2)%3 = 1 := by omega
  simp only [face, theta, hv, hm]
  rw [show (2*n-1+1)%(2*(n+1)) = 2*n by rw [show 2*n-1+1 = 2*n by omega]; exact Nat.mod_eq_of_lt (by omega)]
  rw [show 3*(2*n) = 3*(2*n)+0 by omega, rho_at _ _ _ (by decide), side_p]
  cases p <;> simp <;> omega

/-- The interior four transitions are independent of the old side assignment. -/
theorem append_face_new (n) (hn : 3 ≤ n) (c : Sides n) (p q : Bool) :
    (face (r3Block (n+1) (by omega)) (appendSides c p q) (6*n+1) =
      6*n + if q then 5 else 4) ∧
    (face (r3Block (n+1) (by omega)) (appendSides c p q) (6*n+2) =
      6*n + if q then 4 else 3) ∧
    (face (r3Block (n+1) (by omega)) (appendSides c p q) (6*n+3) =
      6*n + if p then 0 else 2) ∧
    (face (r3Block (n+1) (by omega)) (appendSides c p q) (6*n+5) =
      6*n + if p then 1 else 0) := by
  have hp : mate (r3Block (n+1) (by omega)) (2*n) = 2*n+1 := by
    simp [mate, r3Block, blockMate, show ¬2*n < 3 by omega,
      show ¬2*n < 6 by omega, Nat.mul_mod]
  have hq : mate (r3Block (n+1) (by omega)) (2*n+1) = 2*n := by
    simp [mate, r3Block, blockMate, show ¬2*n+1 < 3 by omega,
      show ¬2*n+1 < 6 by omega, show 2*n+1 < 2*(n+1) by omega, Nat.add_mod, Nat.mul_mod]
  have divs : (6*n+1)/3 = 2*n ∧ (6*n+2)/3 = 2*n ∧
      (6*n+3)/3 = 2*n+1 ∧ (6*n+5)/3 = 2*n+1 := by omega
  have mods : (6*n+1)%3 = 1 ∧ (6*n+2)%3 = 2 ∧
      (6*n+3)%3 = 0 ∧ (6*n+5)%3 = 2 := by omega
  simp only [face, theta, divs.1, divs.2.1, divs.2.2.1, divs.2.2.2,
    mods.1, mods.2.1, mods.2.2.1, mods.2.2.2, hp, hq]
  rw [show (2*n+1)%(2*(n+1)) = 2*n+1 by exact Nat.mod_eq_of_lt (by omega),
    show (2*n+1+2*(n+1)-1)%(2*(n+1)) = 2*n by rw [show 2*n+1+2*(n+1)-1 = 2*n+2*(n+1) by omega, Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)]
  rw [show rho (appendSides c p q) (3*(2*n+1)) = 3*(2*n+1) + if q then 2 else 1 by simp [rho, show (3*(2*n+1))/3 = 2*n+1 by omega, show (3*(2*n+1))%3 = 0 by omega, side_q]]
  simp only [
    rho_at _ _ _ (by decide : 0 < 3), rho_at _ _ _ (by decide : 1 < 3),
    rho_at _ _ _ (by decide : 2 < 3), side_p, side_q]
  cases p <;> cases q <;> simp <;> omega

/-- Opposite attachment sides always make the new end edge a single face.
This is the connectivity conjunct of the frozen EndEdgeSurgery obligation. -/
theorem endSame_append_opposite (n) (hn : 3 ≤ n) (c : Sides n)
    (p q : Bool) (hpq : p ≠ q) :
    EndSame (n+1) (by omega) (appendSides c p q) := by
  let f := faceEquiv (r3Block (n+1) (by omega)) (appendSides c p q)
  let z : Fin (6*(n+1)) := ⟨0, by omega⟩
  have step (i j : Fin (6*(n+1))) (h : face (r3Block (n+1) (by omega))
      (appendSides c p q) i.val = j.val) : Equiv.Perm.SameCycle f i j := by
    have hh : f i = j := Fin.ext h
    rw [← hh]
    exact (Equiv.Perm.SameCycle.refl f _).apply_right
  have hs : Equiv.Perm.SameCycle f z (endDart (n:=n) 4) := by
    have hz := append_face_zero n hn c p q
    have hi := append_face_new n hn c p q
    cases p <;> cases q
    · exact False.elim (hpq rfl)
    · exact (step z (endDart 3) hz).trans
        ((step (endDart 3) (endDart 2) hi.2.2.1).trans
          (step (endDart 2) (endDart 4) hi.2.1))
    · exact (step z (endDart 5) hz).trans
        ((step (endDart 5) (endDart 1) hi.2.2.2).trans
          (step (endDart 1) (endDart 4) hi.1))
    · exact False.elim (hpq rfl)
  apply (Round5.endSame_iff_sameCycle (n+1) (by omega) _).mpr
  have hv : (endDart (n:=n) 4) = (⟨3*(2*(n+1)-1)+1, by omega⟩ : Fin (6*(n+1))) := by
    apply Fin.ext
    simp only [endDart, Fin.val_ofNat]
    omega
  rw [← hv]
  exact hs.symm


/-- All old transitions other than the two end-edge inputs are unchanged. -/
theorem append_face_unchanged (n) (hn : 3 ≤ n) (c : Sides n) (p q : Bool)
    (h : Nat) (hh : h < 6*n) (hz : h ≠ 0) (hl : h ≠ 6*n-2) :
    face (r3Block (n+1) (by omega)) (appendSides c p q) h =
      face (r3Block n hn) c h := by
  have hi : h/3 < 2*n := by omega
  have ht : theta (r3Block (n+1) (by omega)) h = theta (r3Block n hn) h := by
    have hr : h%3 = 0 ∨ h%3 = 1 ∨ h%3 = 2 := by omega
    rcases hr with hr | hr | hr
    · have hp : 0 < h/3 := by omega
      simp only [theta, hr]
      rw [show h/3+2*(n+1)-1 = (h/3-1)+2*(n+1) by omega,
        show h/3+2*n-1 = (h/3-1)+2*n by omega,
        Nat.add_mod_right, Nat.add_mod_right,
        Nat.mod_eq_of_lt (show h/3-1 < 2*(n+1) by omega),
        Nat.mod_eq_of_lt (show h/3-1 < 2*n by omega)]
    · have hp : h/3+1 < 2*n := by omega
      simp only [theta, hr, Nat.mod_eq_of_lt hp,
        Nat.mod_eq_of_lt (show h/3+1 < 2*(n+1) by omega)]
    · simp only [theta, hr, mate, dite_eq_left hi,
        dite_eq_left (show h/3 < 2*(n+1) by omega), r3Block]
  unfold face
  rw [ht]
  have hb := theta_lt (r3Block n hn) h hh
  unfold rho
  rw [side_old c p q _ (by omega)]

/-- The two exit darts return to the old outgoing destinations. -/
theorem append_face_exits (n) (hn : 3 ≤ n) (c : Sides n) (p q : Bool) :
    face (r3Block (n+1) (by omega)) (appendSides c p q) (6*n) =
      face (r3Block n hn) c 0 ∧
    face (r3Block (n+1) (by omega)) (appendSides c p q) (6*n+4) =
      face (r3Block n hn) c (6*n-2) := by
  have hp : theta (r3Block (n+1) (by omega)) (6*n) = theta (r3Block n hn) 0 := by
    simp only [theta, show (6*n)/3 = 2*n by omega, show (6*n)%3 = 0 by omega,
      Nat.zero_div, Nat.zero_mod]
    rw [show 2*n+2*(n+1)-1 = (2*n-1)+2*(n+1) by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (show 2*n-1 < 2*(n+1) by omega),
      show 0+2*n-1 = 2*n-1 by omega, Nat.mod_eq_of_lt (show 2*n-1 < 2*n by omega)]
  have hq : theta (r3Block (n+1) (by omega)) (6*n+4) = theta (r3Block n hn) (6*n-2) := by
    simp only [theta, show (6*n+4)/3 = 2*n+1 by omega,
      show (6*n+4)%3 = 1 by omega, show (6*n-2)/3 = 2*n-1 by omega,
      show (6*n-2)%3 = 1 by omega]
    rw [show 2*n+1+1 = 2*(n+1) by omega, Nat.mod_self,
      show 2*n-1+1 = 2*n by omega, Nat.mod_self]
  constructor
  · unfold face
    rw [hp]
    unfold rho
    rw [side_old c p q _ (by have := theta_lt (r3Block n hn) 0 (by omega); omega)]
  · unfold face
    rw [hq]
    unfold rho
    rw [side_old c p q _ (by have := theta_lt (r3Block n hn) (6*n-2) (by omega); omega)]

#print axioms append_face_zero
#print axioms append_face_last
#print axioms append_face_new
#print axioms append_face_unchanged
#print axioms append_face_exits
#print axioms endSame_append_opposite
end Chord.Round7
