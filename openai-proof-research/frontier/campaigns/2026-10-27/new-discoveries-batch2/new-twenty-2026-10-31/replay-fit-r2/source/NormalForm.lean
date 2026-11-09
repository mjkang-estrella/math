import GroupSemantics
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/- Provenance: GroupSemantics is copied byte-for-byte from frozen coxeter-spectral-r2.
The definitions below are syntactic; `Clean` is not a definition of group reducedness. -/
namespace RACGNormal330264
open RACGSemantics330264
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A letter that can move to the front by commuting swaps. -/
noncomputable def Movable (a : V) : List V → Prop
  | [] => False
  | b :: w => a = b ∨ (G.Adj a b ∧ Movable a w)

instance (a : V) (w : List V) : Decidable (Movable G a w) := by
  induction w with
  | nil => exact isFalse id
  | cons b w ih => unfold Movable; infer_instance

/-- No repeated letter separated entirely by commuting letters. -/
noncomputable def Clean : List V → Prop
  | [] => True
  | a :: w => Clean w ∧ ¬ Movable G a w

@[simp] theorem movable_nil (a : V) : ¬ Movable G a [] := id
@[simp] theorem movable_cons (a b : V) (w : List V) :
    Movable G a (b :: w) ↔ a = b ∨ G.Adj a b ∧ Movable G a w := Iff.rfl
@[simp] theorem clean_nil : Clean G [] := trivial
@[simp] theorem clean_cons (a : V) (w : List V) :
    Clean G (a :: w) ↔ Clean G w ∧ ¬ Movable G a w := Iff.rfl

 theorem movable_iff (a : V) (w : List V) : Movable G a w ↔
    ∃ p q, w = p ++ a :: q ∧ ∀ b ∈ p, G.Adj a b := by
  induction w with
  | nil => simp
  | cons b w ih =>
    constructor
    · rintro (rfl | ⟨hab, h⟩)
      · exact ⟨[], w, rfl, by simp⟩
      · obtain ⟨p, q, rfl, hp⟩ := ih.mp h
        exact ⟨b :: p, q, rfl, by simpa using And.intro hab hp⟩
    · rintro ⟨p, q, he, hp⟩
      cases p with
      | nil => simp only [List.nil_append, List.cons.injEq] at he; exact Or.inl he.1.symm
      | cons c p =>
        simp only [List.cons_append, List.cons.injEq] at he
        rcases he with ⟨rfl, he⟩
        exact Or.inr ⟨hp b (by simp), ih.mpr ⟨p, q, he, by
          intro d hd; exact hp d (by simp [hd])⟩⟩

 theorem clean_append_left {p q : List V} (h : Clean G (p ++ q)) : Clean G p := by
  induction p with
  | nil => trivial
  | cons a p ih =>
    obtain ⟨ht, ha⟩ := h
    refine ⟨ih ht, fun hm => ha ?_⟩
    obtain ⟨r, s, he, hr⟩ := (movable_iff G a p).mp hm
    exact (movable_iff G a (p ++ q)).mpr ⟨r, s ++ q, by simp [he], hr⟩

 theorem clean_append_right {p q : List V} (h : Clean G (p ++ q)) : Clean G q := by
  induction p with
  | nil => exact h
  | cons a p ih => exact ih h.1

 theorem clean_iff_no_pair (w : List V) : Clean G w ↔
    ∀ p m q a, w = p ++ a :: (m ++ a :: q) → ¬ (∀ b ∈ m, G.Adj a b) := by
  constructor
  · intro h p m q a he hm
    subst w
    have ha := (clean_append_right G h).2
    exact ha ((movable_iff G a _).mpr ⟨m, q, rfl, hm⟩)
  · induction w with
    | nil => simp
    | cons a w ih =>
      intro h
      constructor
      · apply ih
        intro p m q b he
        apply h (a :: p) m q b
        simp [he]
      · intro hm
        obtain ⟨p, q, he, hp⟩ := (movable_iff G a w).mp hm
        exact h [] p q a (by simp [he]) hp

/-- The already proved actual-group shortening direction, with precisely this predicate. -/
 theorem reduced_implies_clean (w : List V) (h : (system G).IsReduced w) : Clean G w := by
  apply (clean_iff_no_pair G w).mpr
  intro p m q a he hm
  subst w
  exact forbidden_pair_not_shortest G p m q a hm h

/-- Movable letters always form a clique, without any reducedness hypothesis. -/
 theorem movable_clique (w : List V) {a b : V} (ha : Movable G a w)
    (hb : Movable G b w) (hne : a ≠ b) : G.Adj a b := by
  induction w with
  | nil => exact False.elim ha
  | cons c w ih =>
    rcases ha with rfl | ⟨hac, ha⟩
    · rcases hb with h | ⟨hbc, _⟩
      · exact False.elim (hne h.symm)
      · exact hbc.symm
    · rcases hb with rfl | ⟨_, hb⟩
      · exact hac
      · exact ih ha hb

/-- Delete the first occurrence if it is movable; stop at the first blocker. -/
noncomputable def pluck (a : V) : List V → List V
  | [] => []
  | b :: w => if a = b then w else if G.Adj a b then b :: pluck a w else b :: w

 theorem pluck_of_not_movable (a : V) (w : List V) (h : ¬ Movable G a w) :
    pluck G a w = w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    have hn : a ≠ b := fun he => h (Or.inl he)
    by_cases hab : G.Adj a b
    · simp only [pluck, ite_eq_right hn, ite_eq_left hab]
      rw [ih (fun hm => h (Or.inr ⟨hab, hm⟩))]
    · simp [pluck, hn, hab]

 theorem pluck_decomposition (a : V) (w : List V) (h : Movable G a w) :
    ∃ p q, w = p ++ a :: q ∧ pluck G a w = p ++ q ∧ ∀ b ∈ p, G.Adj a b := by
  induction w with
  | nil => exact False.elim h
  | cons b w ih =>
    by_cases he : a = b
    · subst b; exact ⟨[], w, rfl, by simp [pluck], by simp⟩
    · obtain ⟨hab, hw⟩ := h.resolve_left he
      obtain ⟨p, q, hwp, hp, hc⟩ := ih hw
      refine ⟨b :: p, q, by simp [hwp], by simp [pluck, he, hab, hp], ?_⟩
      simpa using And.intro hab hc

 theorem pluck_length (a : V) (w : List V) (h : Movable G a w) :
    (pluck G a w).length + 1 = w.length := by
  obtain ⟨p, q, rfl, hp, _⟩ := pluck_decomposition G a w h
  simp [hp, Nat.add_assoc]

 theorem pluck_product (a : V) (w : List V) (h : Movable G a w) :
    (system G).wordProd (pluck G a w) = (system G).simple a * (system G).wordProd w := by
  obtain ⟨p, q, rfl, hp, hc⟩ := pluck_decomposition G a w h
  rw [hp]
  simp only [CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_cons]
  rw [← mul_assoc, commute_word G a p hc, mul_assoc,
    CoxeterSystem.simple_mul_simple_cancel_left]

theorem movable_pluck_of_adj {a b : V} (hab : G.Adj b a) (w : List V)
    (h : Movable G b (pluck G a w)) : Movable G b w := by
  induction w with
  | nil => exact False.elim h
  | cons c w ih =>
    by_cases he : a = c
    · subst c
      simp only [pluck] at h
      exact Or.inr ⟨hab, h⟩
    · by_cases hac : G.Adj a c
      · simp only [pluck, ite_eq_right he, ite_eq_left hac] at h
        rcases h with rfl | ⟨hbc, hb⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hbc, ih hb⟩
      · simpa [pluck, he, hac] using h

theorem clean_pluck (a : V) (w : List V) (hw : Clean G w) : Clean G (pluck G a w) := by
  induction w with
  | nil => trivial
  | cons b w ih =>
    by_cases he : a = b
    · subst b; simpa [pluck] using hw.1
    · by_cases hab : G.Adj a b
      · simp only [pluck, ite_eq_right he, ite_eq_left hab, clean_cons]
        exact ⟨ih hw.1, fun hm => hw.2 (movable_pluck_of_adj G hab.symm w hm)⟩
      · simpa [pluck, he, hab] using hw

theorem not_movable_pluck_self (a : V) (w : List V) (hw : Clean G w) :
    ¬ Movable G a (pluck G a w) := by
  induction w with
  | nil => exact id
  | cons b w ih =>
    by_cases he : a = b
    · subst b; simpa [pluck] using hw.2
    · by_cases hab : G.Adj a b
      · simp only [pluck, ite_eq_right he, ite_eq_left hab, movable_cons]
        exact fun h => h.elim he (fun h => ih hw.1 h.2)
      · simp [pluck, he, hab]

/-- Left multiplication on syntactically reduced words, pending descent to traces. -/
def toggle (a : V) (w : List V) : List V :=
  if Movable G a w then pluck G a w else a :: w

theorem clean_toggle (a : V) (w : List V) (hw : Clean G w) : Clean G (toggle G a w) := by
  unfold toggle
  split
  · exact clean_pluck G a w hw
  · exact ⟨hw, by assumption⟩

theorem toggle_product (a : V) (w : List V) :
    (system G).wordProd (toggle G a w) = (system G).simple a * (system G).wordProd w := by
  unfold toggle
  split
  · exact pluck_product G a w (by assumption)
  · rfl

theorem toggle_length (a : V) (w : List V) :
    (toggle G a w).length + 1 = w.length ∨ (toggle G a w).length = w.length + 1 := by
  unfold toggle
  split
  · exact Or.inl (pluck_length G a w (by assumption))
  · exact Or.inr rfl

/-- Equivalence generated solely by adjacent commuting swaps. No cancellations. -/
inductive Shuffle : List V → List V → Prop
  | refl (w) : Shuffle w w
  | cons (a) {w z} : Shuffle w z → Shuffle (a :: w) (a :: z)
  | swap (a b) (w) : G.Adj a b → Shuffle (a :: b :: w) (b :: a :: w)
  | trans {u w z} : Shuffle u w → Shuffle w z → Shuffle u z

 theorem Shuffle.symm {w z : List V} (h : Shuffle G w z) : Shuffle G z w := by
  induction h with
  | refl w => exact .refl w
  | cons a h ih => exact .cons a ih
  | swap a b w hab => exact .swap b a w hab.symm
  | trans h k ih ik => exact .trans ik ih

 theorem Shuffle.length {w z : List V} (h : Shuffle G w z) : w.length = z.length := by
  induction h with
  | refl w => rfl
  | cons a h ih => simp [ih]
  | swap a b w hab => rfl
  | trans h k ih ik => exact ih.trans ik

 theorem shuffle_prefix (a : V) (p q : List V) (hp : ∀ b ∈ p, G.Adj a b) :
    Shuffle G (a :: (p ++ q)) (p ++ a :: q) := by
  induction p with
  | nil => exact .refl _
  | cons b p ih =>
    exact .trans (.swap a b (p ++ q) (hp b (by simp)))
      (.cons b (ih (by intro c hc; exact hp c (by simp [hc]))))

 theorem toggle_involutive_shuffle (a : V) (w : List V) (hw : Clean G w) :
    Shuffle G (toggle G a (toggle G a w)) w := by
  by_cases hm : Movable G a w
  · have hn := not_movable_pluck_self G a w hw
    simp only [toggle, ite_eq_left hm, ite_eq_right hn]
    obtain ⟨p, q, he, hp, hc⟩ := pluck_decomposition G a w hm
    rw [hp, he]
    exact shuffle_prefix G a p q hc
  · simp only [toggle, ite_eq_right hm]
    have hm' : Movable G a (a :: w) := Or.inl rfl
    simp only [ite_eq_left hm', pluck]
    exact .refl _

theorem movable_shuffle {w z : List V} (h : Shuffle G w z) (a : V) :
    Movable G a w ↔ Movable G a z := by
  induction h with
  | refl w => rfl
  | cons b h ih => simp only [movable_cons, ih]
  | swap b c w hbc =>
    by_cases hab : a = b
    · subst b
      simp [hbc, hbc.ne, hbc.symm]
    · by_cases hac : a = c
      · subst c
        simp [hbc, hbc.ne, hbc.symm]
      · simp only [movable_cons, hab, hac, false_or]
        tauto
  | trans h k ih ik => exact ih.trans ik

 theorem clean_shuffle {w z : List V} (h : Shuffle G w z) : Clean G w ↔ Clean G z := by
  induction h with
  | refl w => rfl
  | cons b h ih => simp only [clean_cons, ih, movable_shuffle G h b]
  | swap b c w hbc =>
    simp only [clean_cons, movable_cons, hbc.ne, hbc.ne.symm, hbc, hbc.symm,
      false_or, true_and]
    tauto
  | trans h k ih ik => exact ih.trans ik

 theorem pluck_shuffle {w z : List V} (h : Shuffle G w z) (a : V) :
    Shuffle G (pluck G a w) (pluck G a z) := by
  induction h with
  | refl w => exact .refl _
  | cons b h ih =>
    by_cases he : a = b
    · subst b; simpa [pluck] using h
    · by_cases hab : G.Adj a b
      · simpa only [pluck, ite_eq_right he, ite_eq_left hab] using Shuffle.cons b ih
      · simpa only [pluck, ite_eq_right he, ite_eq_right hab] using Shuffle.cons b h
  | swap b c w hbc =>
    by_cases hab : a = b
    · subst b
      simp only [pluck, ite_eq_left rfl, ite_eq_right hbc.ne, ite_eq_left hbc]
      exact .refl _
    · by_cases hac : a = c
      · subst c
        simp only [pluck, ite_eq_right hab, ite_eq_left hbc.symm, ite_eq_left rfl]
        exact .refl _
      · by_cases hb : G.Adj a b <;> by_cases hc : G.Adj a c
        · simp only [pluck, ite_eq_right hab, ite_eq_right hac, ite_eq_left hb, ite_eq_left hc]
          exact .swap b c _ hbc
        · simp only [pluck, ite_eq_right hab, ite_eq_right hac, ite_eq_left hb, ite_eq_right hc]
          exact .swap b c _ hbc
        · simp only [pluck, ite_eq_right hab, ite_eq_right hac, ite_eq_right hb, ite_eq_left hc]
          exact .swap b c _ hbc
        · simp only [pluck, ite_eq_right hab, ite_eq_right hac, ite_eq_right hb, ite_eq_right hc]
          exact .swap b c _ hbc
  | trans h k ih ik => exact .trans ih ik

 theorem toggle_shuffle {w z : List V} (h : Shuffle G w z) (a : V) :
    Shuffle G (toggle G a w) (toggle G a z) := by
  have hm := movable_shuffle G h a
  unfold toggle
  by_cases hw : Movable G a w
  · rw [ite_eq_left hw, ite_eq_left (hm.mp hw)]
    exact pluck_shuffle G h a
  · rw [ite_eq_right hw, ite_eq_right (fun hz => hw (hm.mpr hz))]
    exact .cons a h

 theorem movable_pluck_iff_of_adj {a b : V} (hab : G.Adj b a) (w : List V) :
    Movable G b (pluck G a w) ↔ Movable G b w := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    by_cases he : a = c
    · subst c
      simp [pluck, hab, hab.ne]
    · by_cases hac : G.Adj a c
      · simp only [pluck, ite_eq_right he, ite_eq_left hac, movable_cons, ih]
      · simp [pluck, he, hac]

 theorem movable_toggle_iff_of_adj {a b : V} (hab : G.Adj b a) (w : List V) :
    Movable G b (toggle G a w) ↔ Movable G b w := by
  unfold toggle
  split
  · exact movable_pluck_iff_of_adj G hab w
  · simp [hab, hab.ne]

 theorem pluck_commute {a b : V} (hab : G.Adj a b) (w : List V) :
    pluck G a (pluck G b w) = pluck G b (pluck G a w) := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    by_cases ha : a = c
    · subst c
      simp [pluck, hab, hab.symm, hab.ne, hab.ne.symm]
    · by_cases hb : b = c
      · subst c
        simp [pluck, hab, hab.symm, hab.ne, hab.ne.symm]
      · by_cases hac : G.Adj a c <;> by_cases hbc : G.Adj b c <;>
          simp [pluck, ha, hb, hac, hbc, ih]

 theorem toggle_commute_shuffle {a b : V} (hab : G.Adj a b) (w : List V) :
    Shuffle G (toggle G a (toggle G b w)) (toggle G b (toggle G a w)) := by
  have ha := movable_toggle_iff_of_adj G hab w
  have hb := movable_toggle_iff_of_adj G hab.symm w
  by_cases hma : Movable G a w <;> by_cases hmb : Movable G b w
  · change Shuffle G (if Movable G a (toggle G b w) then _ else _)
      (if Movable G b (toggle G a w) then _ else _)
    rw [ite_eq_left (ha.mpr hma), ite_eq_left (hb.mpr hmb)]
    simp only [toggle, ite_eq_left hma, ite_eq_left hmb]
    rw [pluck_commute G hab w]
    exact .refl _
  · change Shuffle G (if Movable G a (toggle G b w) then _ else _)
      (if Movable G b (toggle G a w) then _ else _)
    rw [ite_eq_left (ha.mpr hma), ite_eq_right (fun h => hmb (hb.mp h))]
    simp only [toggle, ite_eq_left hma, ite_eq_right hmb, pluck,
      ite_eq_right hab.ne, ite_eq_left hab]
    exact .refl _
  · change Shuffle G (if Movable G a (toggle G b w) then _ else _)
      (if Movable G b (toggle G a w) then _ else _)
    rw [ite_eq_right (fun h => hma (ha.mp h)), ite_eq_left (hb.mpr hmb)]
    simp only [toggle, ite_eq_right hma, ite_eq_left hmb, pluck,
      ite_eq_right hab.ne.symm, ite_eq_left hab.symm]
    exact .refl _
  · change Shuffle G (if Movable G a (toggle G b w) then _ else _)
      (if Movable G b (toggle G a w) then _ else _)
    rw [ite_eq_right (fun h => hma (ha.mp h)), ite_eq_right (fun h => hmb (hb.mp h))]
    simp only [toggle, ite_eq_right hma, ite_eq_right hmb]
    exact .swap a b w hab

end RACGNormal330264
