import PackedRows
set_option autoImplicit false
namespace Polyomino57.Diagonal.FiniteProof.Packed
 def rep : ℕ → ℕ
 | 0 => 0
 | n+1 => 1 + 64 * rep n
 def bounded : ℕ → ℕ → Prop
 | 0, a => a = 0
 | n+1, a => a % 64 ≤ 12 ∧ bounded n (a / 64)
 theorem bounded_le {n a : ℕ} (h : bounded n a) : a ≤ 12 * rep n := by
  induction n generalizing a with
  | zero => exact Nat.le_of_eq h
  | succ n ih =>
    have hl := h.1
    have ht := ih h.2
    have hr := Nat.mod_add_div a 64
    simp only [rep]
    omega
 def slack (n a b c : ℕ) : ℕ := a+b+32*rep n-c-rep n
 theorem slack_step {n a b c : ℕ}
     (ha : bounded (n+1) a) (hb : bounded (n+1) b) (hc : bounded (n+1) c) :
     slack (n+1) a b c = a%64+b%64+31-c%64 + 64*slack n (a/64) (b/64) (c/64) := by
   have hct := bounded_le hc.2
   have hca := hc.1
   have haa := ha.1
   have hba := hb.1
   have ea := Nat.mod_add_div a 64
   have eb := Nat.mod_add_div b 64
   have ec := Nat.mod_add_div c 64
   simp only [slack, rep]
   omega
 theorem low_test (a b c : ℕ) (ha : a ≤ 12) (hb : b ≤ 12) (hc : c ≤ 12) :
     (a+b+31-c &&& 32) = 32 → c+1 ≤ a+b := by
   intro h
   have hbit := congrArg (fun x : ℕ => x.testBit 5) h
   simp only [Nat.testBit_and] at hbit
   have ht : Nat.testBit 32 5 = true := by decide
   rw [ht, Bool.and_true] at hbit
   rw [Nat.testBit_eq_decide_div_mod_eq] at hbit
   have : (a+b+31-c) / 32 % 2 = 1 := of_decide_eq_true hbit
   omega
 theorem bits_sound {n a b c : ℕ}
     (ha : bounded n a) (hb : bounded n b) (hc : bounded n c)
     (h : (slack n a b c &&& (32*rep n)) = 32*rep n) :
     mergeCheck n a b c = true := by
   induction n generalizing a b c with
   | zero => rfl
   | succ n ih =>
     have es := slack_step ha hb hc
     have elo : a%64+b%64+31-c%64 < 64 := by
       have := ha.1; have := hb.1; have := hc.1; omega
     have hmod := congrArg (fun x => x % 64) h
     have hdiv := congrArg (fun x => x / 64) h
     have em : 32*rep (n+1) % 64 = 32 := by simp only [rep]; omega
     have ed : 32*rep (n+1) / 64 = 32*rep n := by simp only [rep]; omega
     have sm : slack (n+1) a b c % 64 = a%64+b%64+31-c%64 := by omega
     have sd : slack (n+1) a b c / 64 = slack n (a/64) (b/64) (c/64) := by omega
     rw [show 64=2^6 from rfl, Nat.and_mod_two_pow] at hmod
     rw [show 64=2^6 from rfl, Nat.and_div_two_pow] at hdiv
     change (slack (n+1) a b c % 64 &&& (32*rep (n+1) % 64)) = 32*rep (n+1) % 64 at hmod
     change (slack (n+1) a b c / 64 &&& (32*rep (n+1) / 64)) = 32*rep (n+1) / 64 at hdiv
     rw [em, sm] at hmod
     rw [ed, sd] at hdiv
     simp only [mergeCheck, Bool.and_eq_true, decide_eq_true_eq]
     exact ⟨low_test _ _ _ ha.1 hb.1 hc.1 hmod, ih ha.2 hb.2 hc.2 hdiv⟩
def boundCheck : ℕ → ℕ → Bool
  | 0, a => decide (a = 0)
  | n+1, a => decide (a % 64 ≤ 12) && boundCheck n (a / 64)
theorem boundCheck_sound {n a : ℕ} (h : boundCheck n a = true) : bounded n a := by
  induction n generalizing a with
  | zero =>
    change a = 0
    exact of_decide_eq_true h
  | succ n ih =>
    simp only [boundCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1, ih h.2⟩
def bitCheck (n a b c : ℕ) : Bool := decide ((slack n a b c &&& (32*rep n)) = 32*rep n)
def checkedPairs (n c : ℕ) (pairs : List (ℕ × ℕ)) : Bool :=
  boundCheck n c && pairs.all (fun ab =>
    boundCheck n ab.1 && boundCheck n ab.2 && bitCheck n ab.1 ab.2 c)
theorem checkedPairs_sound {n c : ℕ} {pairs : List (ℕ × ℕ)}
    (h : checkedPairs n c pairs = true) {a b : ℕ} (hm : (a,b) ∈ pairs) :
    ∀ i < n, digit c i + 1 ≤ digit a i + digit b i := by
  simp only [checkedPairs, Bool.and_eq_true, List.all_eq_true] at h
  have hp := h.2 (a,b) hm
  exact mergeCheck_sound (bits_sound (boundCheck_sound hp.1.1)
    (boundCheck_sound hp.1.2) (boundCheck_sound h.1) (of_decide_eq_true hp.2))
theorem bits_certificate {V I : Type*} [DecidableEq V] [DecidableEq I]
    (n : ℕ) (idx : V → ℕ) (D : Finset V) (M : Finset I)
    (E : V → V → Prop) (H : I → V → Prop) (row : Finset I → ℕ)
    (hi : ∀ v ∈ D, idx v < n)
    (hr : ∀ A, A ⊆ M → A.Nonempty → bounded n (row A))
    (hb : ∀ A, A ⊆ M → A.Nonempty → ∀ v ∈ D,
      (∀ i ∈ A, H i v) → digit (row A) (idx v) ≤ 1)
    (he : ∀ A, A ⊆ M → A.Nonempty → ∀ v ∈ D, ∀ w ∈ D,
      E v w → digit (row A) (idx v) ≤ digit (row A) (idx w) + 1)
    (hm : ∀ A B, A ⊆ M → B ⊆ M → A.Nonempty → B.Nonempty → Disjoint A B →
      bitCheck n (row A) (row B) (row (A ∪ B)) = true) :
    GraphPotential.Certificate E D M H (fun A v => digit (row A) (idx v)) := by
  apply certificate n idx D M E H row hi hb he
  intro A B hA hB hneA hneB hd
  exact bits_sound (hr A hA hneA) (hr B hB hneB)
    (hr (A ∪ B) (Finset.union_subset hA hB) (hneA.mono Finset.subset_union_left))
    (of_decide_eq_true (hm A B hA hB hneA hneB hd))
end Polyomino57.Diagonal.FiniteProof.Packed
