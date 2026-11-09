import ChordModel2Orbit
namespace Chord.Model2

private theorem prev_next (L i : Nat) (hi : i < L) :
    (((i+L-1)%L)+1)%L = i := by
  by_cases h : i = 0
  · subst i
    have hp : 0 < L := by omega
    have hlt : L-1 < L := by omega
    rw [show 0+L-1 = L-1 by omega, Nat.mod_eq_of_lt hlt]
    rw [show L-1+1 = L by omega, Nat.mod_self]
  · have hl : L ≤ i+L-1 := by omega
    have he : i+L-1 = (i-1)+L := by omega
    rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (show i-1 < L by omega)]
    rw [show i-1+1 = i by omega, Nat.mod_eq_of_lt hi]

private theorem next_prev (L i : Nat) (hi : i < L) :
    (((i+1)%L)+L-1)%L = i := by
  by_cases h : i+1 = L
  · rw [h, Nat.mod_self]
    rw [show 0+L-1 = i by omega, Nat.mod_eq_of_lt hi]
  · rw [Nat.mod_eq_of_lt (show i+1 < L by omega)]
    rw [show i+1+L-1 = i+L by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hi]

theorem mate_lt {n} (D : Diagram n) (i : Nat) (hi : i < 2*n) : mate D i < 2*n := by
  simp only [mate, dite_eq_left hi]
  exact (D.partner ⟨i,hi⟩).isLt

theorem mate_mate {n} (D : Diagram n) (i : Nat) (hi : i < 2*n) :
    mate D (mate D i) = i := by
  rw [mate, dite_eq_left (mate_lt D i hi)]
  simp only [mate, dite_eq_left hi]
  exact congrArg Fin.val (D.involutive ⟨i,hi⟩)

theorem theta_lt {n} (D : Diagram n) (h : Nat) (hh : h < 6*n) :
    theta D h < 6*n := by
  have hi : h/3 < 2*n := by omega
  have hp : 0 < 2*n := by omega
  have ha := Nat.mod_lt (h/3+2*n-1) hp
  have hb := Nat.mod_lt (h/3+1) hp
  have hc := mate_lt D (h/3) hi
  unfold theta
  split <;> dsimp only <;> omega

theorem theta_involutive {n} (D : Diagram n) (h : Nat) (hh : h < 6*n) :
    theta D (theta D h) = h := by
  have hi : h/3 < 2*n := by omega
  have hr : h%3 = 0 ∨ h%3 = 1 ∨ h%3 = 2 := by omega
  rcases hr with hr | hr | hr
  · simp only [theta, hr]
    simp only [show (3*((h/3+2*n-1)%(2*n))+1)/3 = (h/3+2*n-1)%(2*n) by omega,
      show (3*((h/3+2*n-1)%(2*n))+1)%3 = 1 by omega]
    rw [prev_next (2*n) (h/3) hi]
    omega
  · simp only [theta, hr]
    simp only [show (3*((h/3+1)%(2*n)))/3 = (h/3+1)%(2*n) by omega,
      show (3*((h/3+1)%(2*n)))%3 = 0 by omega]
    rw [next_prev (2*n) (h/3) hi]
    omega
  · simp only [theta, hr]
    simp only [show (3*mate D (h/3)+2)/3 = mate D (h/3) by omega,
      show (3*mate D (h/3)+2)%3 = 2 by omega]
    rw [mate_mate D (h/3) hi]
    omega

theorem rho_lt {n} (c : Sides n) (h : Nat) (hh : h < 6*n) :
    rho c h < 6*n := by
  unfold rho
  split <;> split <;> omega

private theorem rho_vertex {n} (c : Sides n) (i r : Nat) (hr : r < 3) :
    rho c (3*i+r) = 3*i + if side c i then
      (match r with | 0 => 2 | 1 => 0 | _ => 1)
    else (match r with | 0 => 1 | 1 => 2 | _ => 0) := by
  unfold rho
  rw [show (3*i+r)/3 = i by omega, show (3*i+r)%3 = r by omega]
  have hh : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  rcases hh with rfl | rfl | rfl <;> rfl

theorem rho_cube {n} (c : Sides n) (h : Nat) :
    rho c (rho c (rho c h)) = h := by
  have he : h = 3*(h/3)+h%3 := by omega
  have hr : h%3 = 0 ∨ h%3 = 1 ∨ h%3 = 2 := by omega
  generalize hi : h/3 = i at he hr ⊢
  rcases hr with hr | hr | hr <;> rw [hr] at he <;> rw [he]
  all_goals cases hs : side c i <;>
    simp only [rho_vertex c i 0 (by decide), rho_vertex c i 1 (by decide),
      rho_vertex c i 2 (by decide), hs, Bool.false_eq_true, ↓reduceIte]
/-- Explicit inverse: theta after two vertex rotations. -/
def faceEquiv {n} (D : Diagram n) (c : Sides n) : Fin (6*n) ≃ Fin (6*n) where
  toFun i := ⟨face D c i.val, rho_lt c _ (theta_lt D _ i.isLt)⟩
  invFun i := ⟨theta D (rho c (rho c i.val)), theta_lt D _ (rho_lt c _ (rho_lt c _ i.isLt))⟩
  left_inv i := by
    apply Fin.ext
    change theta D (rho c (rho c (rho c (theta D i.val)))) = i.val
    rw [rho_cube, theta_involutive D _ i.isLt]
  right_inv i := by
    apply Fin.ext
    change rho c (theta D (theta D (rho c (rho c i.val)))) = i.val
    rw [theta_involutive D _ (rho_lt c _ (rho_lt c _ i.isLt)), rho_cube]

theorem facePermutationCorrect : FacePermutationCorrect := by
  intro n D c
  exact ⟨faceEquiv D c, fun _ => rfl⟩
end Chord.Model2
