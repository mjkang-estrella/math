import GlobalLabel
namespace Nut8
/-- The canonical representative formula for a periodic integral character. -/
def character (m : ℕ) (ε : ℤ) (b : ZMod m) : ℤ := ε ^ b.val

lemma character_natCast (m : ℕ) [NeZero m] (ε : ℤ) (hp : ε ^ m = 1) (n : ℕ) :
    character m ε (n : ZMod m) = ε ^ n := by
  unfold character
  rw [ZMod.val_natCast, ← pow_eq_pow_mod n hp]

lemma character_add (m : ℕ) [NeZero m] (ε : ℤ) (hp : ε ^ m = 1)
    (a b : ZMod m) : character m ε (a+b) = character m ε a * character m ε b := by
  unfold character
  rw [ZMod.val_add, ← pow_eq_pow_mod (a.val+b.val) hp, pow_add]

lemma character_zero (m : ℕ) (ε : ℤ) : character m ε 0 = 1 := by
  simp [character]

lemma character_sign (m : ℕ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (b : ZMod m) :
    character m ε b = 1 ∨ character m ε b = -1 := by
  rcases hε with rfl | rfl
  · simp [character]
  · exact neg_one_pow_eq_or ℤ b.val

lemma character_neg (m : ℕ) [NeZero m] (ε : ℤ) (hp : ε ^ m = 1)
    (hε : ε = 1 ∨ ε = -1) (b : ZMod m) :
    character m ε (-b) = character m ε b := by
  have h := character_add m ε hp b (-b)
  rw [add_neg_cancel, character_zero] at h
  rcases character_sign m ε hε b with hb | hb <;> rw [hb] at h ⊢ <;> linarith

/-- Raw signed quotient on globally labelled vertices. Symmetry and the graph bridge
are separate obligations, not fields assumed in this definition. -/
def signedQuotient (m : ℕ) [NeZero m]
    (G : SimpleGraph (Fin 8 × ZMod m)) [DecidableRel G.Adj] (ε : ℤ) :
    Matrix (Fin 8) (Fin 8) ℤ :=
  fun i j => ∑ b : ZMod m, if G.Adj (i,0) (j,b) then character m ε b else 0
end Nut8
