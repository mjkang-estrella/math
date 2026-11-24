# Lean source appendix for MathDB 343104

### `StabInsertion.lean`

```lean
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort

set_option autoImplicit false

namespace TableauStabilization
open scoped List

abbrev Tableau := List (List ℕ)

/-- Replace the first entry strictly larger than the new letter, or append. -/
def insertRow (x : ℕ) : List ℕ → List ℕ × Option ℕ
  | [] => ([x], none)
  | y :: ys =>
      if x < y then (x :: ys, some y)
      else
        let (r, b) := insertRow x ys
        (y :: r, b)

/-- Insert into the top row and propagate the bumped letter to the next row. -/
def insert (x : ℕ) : Tableau → Tableau
  | [] => [[x]]
  | r :: rs =>
      let (r', b) := insertRow x r
      r' :: (match b with | none => rs | some y => insert y rs)

def insertionTableau (w : List ℕ) : Tableau :=
  w.foldl (fun T x => insert x T) []

def readingWord (T : Tableau) : List ℕ := T.reverse.flatten

def rowAt (T : Tableau) (j : ℕ) : List ℕ := T[j]?.getD []

def rowLength (T : Tableau) (j : ℕ) : ℕ := (rowAt T j).length

/-- The zero-based row index from the top, if the letter occurs. -/
def rowOf (T : Tableau) (x : ℕ) : Option ℕ :=
  match T with
  | [] => none
  | r :: rs => if x ∈ r then some 0 else (rowOf rs x).map Nat.succ

theorem insertRow_perm (x : ℕ) (r : List ℕ) :
    (insertRow x r).2.toList ++ (insertRow x r).1 ~ x :: r := by
  induction r with
  | nil => simp [insertRow]
  | cons y ys ih =>
    by_cases h : x < y
    · simpa [insertRow, h] using (List.Perm.swap x y ys)
    · cases hp : insertRow x ys with
      | mk r b =>
        rw [hp] at ih
        cases b with
        | none =>
          simpa [insertRow, h, hp] using
            (ih.cons y).trans (List.Perm.swap x y ys)
        | some z =>
          simpa [insertRow, h, hp] using
            (List.Perm.swap y z r).trans
              ((ih.cons y).trans (List.Perm.swap x y ys))

theorem insert_perm (x : ℕ) (T : Tableau) :
    (insert x T).flatten ~ x :: T.flatten := by
  induction T generalizing x with
  | nil => simp [insert]
  | cons r rs ih =>
    have hp := insertRow_perm x r
    cases h : insertRow x r with
    | mk r' b =>
      rw [h] at hp
      cases b with
      | none =>
        simpa [insert, h] using hp.append_right rs.flatten
      | some y =>
        simp only [insert, h, List.flatten_cons]
        exact ((ih y).append_left r').trans
          (by
            simpa [List.append_assoc] using
              ((List.perm_append_comm (l₁ := r') (l₂ := [y])).append_right rs.flatten).trans
                (by simpa using hp.append_right rs.flatten))

theorem foldInsert_perm (T : Tableau) (w : List ℕ) :
    (w.foldl (fun T x => insert x T) T).flatten ~ w.reverse ++ T.flatten := by
  induction w generalizing T with
  | nil => simp
  | cons x xs ih =>
    simpa [List.reverse_cons, List.append_assoc] using
      (ih (insert x T)).trans ((insert_perm x T).append_left xs.reverse)

theorem insertionTableau_perm (w : List ℕ) :
    (insertionTableau w).flatten ~ w := by
  exact (by simpa [insertionTableau] using foldInsert_perm [] w :
    (insertionTableau w).flatten ~ w.reverse).trans (List.reverse_perm _)

theorem readingWord_perm (T : Tableau) :
    readingWord T ~ T.flatten := (List.reverse_perm _).flatten

theorem rowOf_eq_some_iff {T : Tableau} {x j : ℕ} (h : T.flatten.Nodup) :
    rowOf T x = some j ↔ x ∈ rowAt T j := by
  induction T generalizing j with
  | nil => simp [rowOf, rowAt]
  | cons r rs ih =>
    have hd := List.nodup_append.mp h
    cases j with
    | zero =>
      by_cases hm : x ∈ r <;> simp [rowOf, rowAt, hm]
    | succ j =>
      by_cases hm : x ∈ r
      · have hnot : x ∉ rs.flatten := fun hx => hd.2.2 x hm x hx rfl
        have hsub : ∀ i, rowAt rs i ⊆ rs.flatten := by
          intro i z hz
          apply List.mem_flatten.mpr
          cases e : rs[i]? with
          | none => simp [rowAt, e] at hz
          | some row => exact ⟨row, List.mem_of_getElem? e, by simpa [rowAt, e] using hz⟩
        simp [rowOf, rowAt, hm, show x ∉ rs[j]?.getD [] from fun hx => hnot (hsub j hx)]
      · simpa [rowOf, rowAt, hm] using (ih (j := j) hd.2.1)

#print axioms insertionTableau_perm
#print axioms rowOf_eq_some_iff

end TableauStabilization
```

### `StabTableau.lean`

```lean
import StabInsertion

set_option autoImplicit false

namespace TableauStabilization

/-- Adjacent rows satisfy the partition condition and strict column inequalities. -/
inductive Above : List ℕ → List ℕ → Prop
  | nil (r : List ℕ) : Above r []
  | cons {a b : ℕ} {r s : List ℕ} : a < b → Above r s → Above (a :: r) (b :: s)

def Valid : Tableau → Prop
  | [] => True
  | r :: rs => r ≠ [] ∧ r.Pairwise (· < ·) ∧ Above r (rowAt rs 0) ∧ Valid rs

theorem insertRow_nonempty (x : ℕ) (r : List ℕ) : (insertRow x r).1 ≠ [] := by
  cases r with
  | nil => simp [insertRow]
  | cons y ys => by_cases h : x < y <;> simp [insertRow, h]

theorem insertRow_mem {x z : ℕ} {r : List ℕ} (h : z ∈ (insertRow x r).1) :
    z = x ∨ z ∈ r := by
  simpa using (insertRow_perm x r).mem_iff.mp (List.mem_append_right _ h)

theorem bump_gt {x y : ℕ} {r : List ℕ} (h : (insertRow x r).2 = some y) : x < y := by
  induction r with
  | nil => simp [insertRow] at h
  | cons z zs ih =>
    by_cases hx : x < z
    · simp [insertRow, hx] at h
      simpa [← h] using hx
    · exact ih (by simpa [insertRow, hx] using h)

theorem insertRow_sorted {x : ℕ} {r : List ℕ} (hs : r.Pairwise (· < ·))
    (hn : x ∉ r) : (insertRow x r).1.Pairwise (· < ·) := by
  induction r with
  | nil => simp [insertRow]
  | cons a as ih =>
    obtain ⟨ha, ht⟩ := List.pairwise_cons.mp hs
    have hne : x ≠ a := fun h => hn (h ▸ List.mem_cons_self)
    by_cases hx : x < a
    · simp only [insertRow, ite_eq_left hx, List.pairwise_cons]
      exact ⟨fun b hb => hx.trans (ha b hb), ht⟩
    · simp only [insertRow, ite_eq_right hx, List.pairwise_cons]
      refine ⟨?_, ih ht (fun h => hn (List.mem_cons_of_mem a h))⟩
      intro b hb
      rcases insertRow_mem hb with rfl | hb
      · omega
      · exact ha b hb

theorem above_insertRow_left {r s : List ℕ} (h : Above r s) (x : ℕ) :
    Above (insertRow x r).1 s := by
  induction h with
  | nil => exact Above.nil _
  | @cons a b r s hab _ ih =>
    by_cases hx : x < a
    · simpa [insertRow, hx] using Above.cons (hx.trans hab) ‹Above r s›
    · simpa [insertRow, hx] using Above.cons hab ih

theorem above_insertRow_bump {r s : List ℕ} {x y : ℕ}
    (hr : r.Pairwise (· < ·)) (ha : Above r s) (hb : (insertRow x r).2 = some y) :
    Above (insertRow x r).1 (insertRow y s).1 := by
  induction r generalizing s with
  | nil => simp [insertRow] at hb
  | cons a r ih =>
    obtain ⟨hrs, hrt⟩ := List.pairwise_cons.mp hr
    by_cases hx : x < a
    · simp only [insertRow, ite_eq_left hx, Option.some.injEq] at hb
      subst y
      cases ha with
      | nil => simpa [insertRow, hx] using Above.cons hx (Above.nil r)
      | cons hab hrest =>
        simpa [insertRow, hx, hab] using Above.cons hx hrest
    · have hb' : (insertRow x r).2 = some y := by simpa [insertRow, hx] using hb
      have hay : a < y := (Nat.le_of_not_gt hx).trans_lt (bump_gt hb')
      cases ha with
      | nil => simpa [insertRow, hx] using Above.cons hay (Above.nil (insertRow x r).1)
      | @cons _ b _ s hab hrest =>
        by_cases hy : y < b
        · simpa [insertRow, hx, hy] using Above.cons hay (above_insertRow_left hrest x)
        · simpa [insertRow, hx, hy] using Above.cons hab (ih hrt hrest hb')

theorem valid_insert {T : Tableau} {x : ℕ} (hv : Valid T) (hn : (x :: T.flatten).Nodup) :
    Valid (insert x T) := by
  induction T generalizing x with
  | nil => exact ⟨by simp, by simp, Above.nil _, trivial⟩
  | cons r rs ih =>
    obtain ⟨_, hrs, ha, hv'⟩ := hv
    have hnd := List.nodup_cons.mp hn
    have hx : x ∉ r := fun hx => hnd.1 (List.mem_append_left _ hx)
    have hne := insertRow_nonempty x r
    have hsort := insertRow_sorted hrs hx
    cases hb : (insertRow x r).2 with
    | none =>
      have ht := above_insertRow_left ha x
      exact by simpa [insert, hb, Valid] using And.intro hne (And.intro hsort ⟨ht, hv'⟩)
    | some y =>
      have hsub : y ∈ x :: r := (insertRow_perm x r).mem_iff.mp (by simp [hb])
      have hyn : (y :: rs.flatten).Nodup := by
        refine List.nodup_cons.mpr ⟨?_, (List.nodup_append.mp hnd.2).2.1⟩
        intro hym
        rcases List.mem_cons.mp hsub with rfl | hmem
        · exact hnd.1 (List.mem_append_right _ hym)
        · exact (List.nodup_append.mp hnd.2).2.2 y hmem y hym rfl
      have ht := above_insertRow_bump hrs ha hb
      have he : rowAt (insert y rs) 0 = (insertRow y (rowAt rs 0)).1 := by
        cases rs <;> simp [rowAt, insert, insertRow]
      rw [← he] at ht
      exact by simpa [insert, hb, Valid] using And.intro hne (And.intro hsort ⟨ht, ih hv' hyn⟩)

theorem valid_foldInsert {T : Tableau} {w : List ℕ} (hv : Valid T)
    (hn : (w.reverse ++ T.flatten).Nodup) :
    Valid (w.foldl (fun T x => insert x T) T) := by
  induction w generalizing T with
  | nil => exact hv
  | cons x xs ih =>
    have hnd : (xs.reverse ++ (x :: T.flatten)).Nodup := by
      simpa [List.reverse_cons, List.append_assoc] using hn
    exact ih (valid_insert hv (List.nodup_append.mp hnd).2.1)
      (((insert_perm x T).append_left xs.reverse).nodup_iff.mpr hnd)

theorem valid_insertionTableau {w : List ℕ} (hn : w.Nodup) :
    Valid (insertionTableau w) := by
  exact valid_foldInsert (T := []) trivial (by simpa using hn)

theorem Above.length_le {r s : List ℕ} (h : Above r s) : s.length ≤ r.length := by
  induction h with
  | nil => simp
  | cons _ _ ih => simpa using ih

theorem Above.getElem_lt {r s : List ℕ} (h : Above r s)
    (j : ℕ) (hj : j < s.length) : r[j]'(hj.trans_le h.length_le) < s[j] := by
  induction h generalizing j with
  | nil => simp at hj
  | cons hab _ ih =>
    cases j with
    | zero => exact hab
    | succ j => exact ih j (by simpa using hj)

#print axioms valid_insertionTableau
#print axioms Above.getElem_lt

end TableauStabilization
```

### `StabKnuth.lean`

```lean
import StabTableau

set_option autoImplicit false

namespace TableauStabilization

/-- The equivalence generated by the two distinct-letter Knuth moves. -/
inductive Knuth : List ℕ → List ℕ → Prop
  | first (p q : List ℕ) {x y z : ℕ} (hxy : x < y) (hyz : y < z) :
      Knuth (p ++ [x,z,y] ++ q) (p ++ [z,x,y] ++ q)
  | second (p q : List ℕ) {x y z : ℕ} (hxy : x < y) (hyz : y < z) :
      Knuth (p ++ [y,x,z] ++ q) (p ++ [y,z,x] ++ q)
  | refl (w : List ℕ) : Knuth w w
  | symm {u v : List ℕ} : Knuth u v → Knuth v u
  | trans {u v w : List ℕ} : Knuth u v → Knuth v w → Knuth u w

theorem Knuth.context {u v : List ℕ} (h : Knuth u v) (p q : List ℕ) :
    Knuth (p ++ u ++ q) (p ++ v ++ q) := by
  induction h with
  | first l r hxy hyz => simpa [List.append_assoc] using Knuth.first (p ++ l) (r ++ q) hxy hyz
  | second l r hxy hyz => simpa [List.append_assoc] using Knuth.second (p ++ l) (r ++ q) hxy hyz
  | refl => exact Knuth.refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem Knuth.perm {u v : List ℕ} (h : Knuth u v) : List.Perm u v := by
  induction h with
  | @first p q x y z _ _ =>
    exact ((List.Perm.swap z x [y]).append_left p).append_right q
  | @second p q x y z _ _ =>
    exact (((List.Perm.swap z x []).cons y).append_left p).append_right q
  | refl => exact List.Perm.refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem move_to_second {x a : ℕ} {v : List ℕ}
    (hx : x < a) (h : (a :: v).Pairwise (· < ·)) :
    Knuth ((a :: v) ++ [x]) (a :: x :: v) := by
  induction v generalizing a with
  | nil => exact Knuth.refl _
  | cons b bs ih =>
    obtain ⟨hab, hbs⟩ := List.pairwise_cons.mp h
    have hab' := hab b List.mem_cons_self
    have hs : Knuth ((a :: b :: bs) ++ [x]) (a :: b :: x :: bs) := by
      simpa using (ih (hx.trans hab') hbs).context [a] []
    have ht := (Knuth.second [] bs hx hab').symm
    exact hs.trans (by simpa using ht)

private theorem head_lt_bump {r : List ℕ} {x y b : ℕ} {bs : List ℕ}
    (hb : (insertRow x r).2 = some y) (he : (insertRow x r).1 = b :: bs) :
    b < y := by
  cases r with
  | nil => simp [insertRow] at hb
  | cons a as =>
    by_cases ha : x < a
    · simp [insertRow, ha] at hb he
      omega
    · simp [insertRow, ha] at he
      exact he.1 ▸ (Nat.le_of_not_gt ha).trans_lt (bump_gt hb)

theorem knuth_insertRow {x : ℕ} {r : List ℕ} (hr : r.Pairwise (· < ·)) (hx : x ∉ r) :
    Knuth (r ++ [x]) ((insertRow x r).2.toList ++ (insertRow x r).1) := by
  induction r with
  | nil => simpa [insertRow] using Knuth.refl [x]
  | cons a as ih =>
    by_cases ha : x < a
    · simpa [insertRow, ha] using move_to_second ha hr
    · obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hr
      have hne : x ≠ a := fun h => hx (h ▸ List.mem_cons_self)
      have hxs : x ∉ as := fun hm => hx (List.mem_cons_of_mem a hm)
      have hk := (ih htail hxs).context [a] []
      cases hb : (insertRow x as).2 with
      | none => simpa [insertRow, ha, hb] using hk
      | some y =>
        cases he : (insertRow x as).1 with
        | nil => exact (insertRow_nonempty x as he).elim
        | cons b bs =>
          have hby := head_lt_bump hb he
          have hab : a < b := by
            have hbmem : b ∈ (insertRow x as).1 := by simp [he]
            rcases insertRow_mem hbmem with rfl | hbmem
            · omega
            · exact hhead b hbmem
          have hmove : Knuth (a :: y :: b :: bs) (y :: a :: b :: bs) :=
            Knuth.first [] bs hab hby
          exact (by simpa [hb, he] using hk : Knuth ((a :: as) ++ [x]) _).trans
            (by simpa [insertRow, ha, he, hb] using hmove)

theorem knuth_insert {x : ℕ} {T : Tableau} (hv : Valid T)
    (hn : (x :: T.flatten).Nodup) :
    Knuth (readingWord T ++ [x]) (readingWord (insert x T)) := by
  induction T generalizing x with
  | nil => exact Knuth.refl _
  | cons r rs ih =>
    have hd := List.nodup_cons.mp hn
    have hnd := List.nodup_append.mp hd.2
    have hr : x ∉ r := fun h => hd.1 (List.mem_append_left _ h)
    have hk := (knuth_insertRow hv.2.1 hr).context (readingWord rs) []
    cases hb : (insertRow x r).2 with
    | none => simpa [readingWord, insert, hb, List.append_assoc] using hk
    | some y =>
      have hy : y ∈ r := by
        have hm := (insertRow_perm x r).mem_iff.mp (by simp [hb] :
          y ∈ (insertRow x r).2.toList ++ (insertRow x r).1)
        exact (List.mem_cons.mp hm).resolve_left (Nat.ne_of_gt (bump_gt hb))
      have hyn : (y :: rs.flatten).Nodup :=
        List.nodup_cons.mpr ⟨fun h => hnd.2.2 y hy y h rfl, hnd.2.1⟩
      have ht := (ih hv.2.2.2 hyn).context [] (insertRow x r).1
      exact (by simpa [readingWord, hb, List.append_assoc] using hk :
        Knuth (readingWord (r :: rs) ++ [x]) ((readingWord rs ++ [y]) ++ (insertRow x r).1)).trans
        (by simpa [readingWord, insert, hb] using ht)

theorem knuth_foldInsert {T : Tableau} {w : List ℕ} (hv : Valid T)
    (hn : (w.reverse ++ T.flatten).Nodup) :
    Knuth (readingWord T ++ w) (readingWord (w.foldl (fun T x => insert x T) T)) := by
  induction w generalizing T with
  | nil => simpa using Knuth.refl (readingWord T)
  | cons x xs ih =>
    have hnd : (xs.reverse ++ (x :: T.flatten)).Nodup := by
      simpa [List.reverse_cons, List.append_assoc] using hn
    have hx := (List.nodup_append.mp hnd).2.1
    have h₁ := (knuth_insert hv hx).context [] xs
    have h₂ := ih (valid_insert hv hx)
      (((insert_perm x T).append_left xs.reverse).nodup_iff.mpr hnd)
    simpa [List.append_assoc] using h₁.trans h₂

theorem knuth_insertionTableau {w : List ℕ} (hn : w.Nodup) :
    Knuth w (readingWord (insertionTableau w)) := by
  simpa [readingWord, insertionTableau] using
    knuth_foldInsert (T := []) trivial (by simpa using hn)

#print axioms knuth_insertionTableau

end TableauStabilization
```

### `StabWord.lean`

```lean
import StabInsertion
import Mathlib.Data.List.FinRange
import Mathlib.Algebra.Group.Equiv.Defs

set_option autoImplicit false

namespace TableauStabilization

/-- The letter in reading row i and copy c. Entries are one-based. -/
def letter {n : ℕ} (w : Equiv.Perm (Fin n)) (i : Fin n) (c : ℕ) : ℕ :=
  (w i).val + 1 + c * n

def block {n : ℕ} (w : Equiv.Perm (Fin n)) (i : Fin n) (k : ℕ) : List ℕ :=
  (List.range k).map (letter w i)

/-- The reading word of the k-fold skew tableau, read bottom to top. -/
def kFoldWord {n : ℕ} (w : Equiv.Perm (Fin n)) (k : ℕ) : List ℕ :=
  (List.finRange n).flatMap fun i => block w i k

def lastCopy {n : ℕ} (w : Equiv.Perm (Fin n)) (k : ℕ) (i : Fin n) : ℕ :=
  letter w i (k - 1)

/-- Each entry of the last copy is still in its original row. -/
def stabilizesAt {n : ℕ} (w : Equiv.Perm (Fin n)) (k : ℕ) : Prop :=
  0 < k ∧ ∀ i : Fin n,
    rowOf (insertionTableau (kFoldWord w k)) (lastCopy w k i) = some (n - 1 - i.val)

theorem letter_lt_of_copy_lt {n : ℕ} {w : Equiv.Perm (Fin n)} {i j : Fin n} {c d : ℕ}
    (h : c < d) : letter w i c < letter w j d := by
  have hmul := Nat.mul_le_mul_right n (Nat.succ_le_of_lt h)
  have hwi := (w i).isLt
  rw [Nat.succ_mul] at hmul
  unfold letter
  omega

theorem letter_lt_iff {n : ℕ} (w : Equiv.Perm (Fin n)) (i j : Fin n) (c d : ℕ) :
    letter w i c < letter w j d ↔ c < d ∨ (c = d ∧ w i < w j) := by
  rcases lt_trichotomy c d with h | rfl | h
  · simp [h, letter_lt_of_copy_lt (i := i) (j := j) (w := w) h]
  · change (w i).val + 1 + c * n < (w j).val + 1 + c * n ↔
      c < c ∨ (c = c ∧ (w i).val < (w j).val)
    omega
  · have he : c ≠ d := (Nat.ne_of_lt h).symm
    simp [Nat.not_lt_of_ge h.le, he, Nat.not_lt_of_ge
      (letter_lt_of_copy_lt (i := j) (j := i) (w := w) h).le]

theorem letter_injective {n : ℕ} (w : Equiv.Perm (Fin n)) {i j : Fin n} {c d : ℕ}
    (h : letter w i c = letter w j d) : i = j ∧ c = d := by
  have he : c = d := by
    rcases lt_trichotomy c d with hcd | hcd | hcd
    · exact ((letter_lt_of_copy_lt hcd).ne h).elim
    · exact hcd
    · exact ((letter_lt_of_copy_lt hcd).ne h.symm).elim
  subst d
  refine ⟨w.injective (Fin.ext ?_), rfl⟩
  unfold letter at h
  omega

theorem block_sorted {n : ℕ} (w : Equiv.Perm (Fin n)) (i : Fin n) (k : ℕ) :
    (block w i k).Pairwise (· < ·) := by
  rw [block, List.pairwise_map]
  exact (List.pairwise_lt_range (n := k)).imp fun h => letter_lt_of_copy_lt h

theorem kFoldWord_nodup {n : ℕ} (w : Equiv.Perm (Fin n)) (k : ℕ) :
    (kFoldWord w k).Nodup := by
  rw [kFoldWord, List.nodup_flatMap]
  refine ⟨fun i _ => (block_sorted w i k).imp Nat.ne_of_lt, ?_⟩
  · apply (List.nodup_finRange n).imp
    intro i j hij x hx hy
    rcases List.mem_map.mp hx with ⟨c, _, rfl⟩
    rcases List.mem_map.mp hy with ⟨d, _, hd⟩
    exact hij (letter_injective w hd.symm).1

theorem kFoldWord_length {n : ℕ} (w : Equiv.Perm (Fin n)) (k : ℕ) :
    (kFoldWord w k).length = n * k := by
  simp [kFoldWord, block, List.length_flatMap]

@[simp] theorem kFoldWord_zero {n : ℕ} (w : Equiv.Perm (Fin n)) :
    kFoldWord w 0 = [] := by
  apply List.length_eq_zero_iff.mp
  rw [kFoldWord_length, Nat.mul_zero]

theorem lastCopy_mem {n : ℕ} (w : Equiv.Perm (Fin n)) (k : ℕ) (hk : 0 < k) (i : Fin n) :
    lastCopy w k i ∈ kFoldWord w k := by
  exact List.mem_flatMap.mpr ⟨i, by simp, List.mem_map.mpr ⟨k - 1, List.mem_range.mpr (by omega), rfl⟩⟩

theorem letter_lt_cutoff {n : ℕ} (w : Equiv.Perm (Fin n)) (i : Fin n) (c k : ℕ) :
    letter w i c ≤ k * n ↔ c < k := by
  have hp := (w i).isLt
  constructor
  · intro h
    by_contra! hc
    have hmul := Nat.mul_le_mul_right n hc
    unfold letter at h
    omega
  · intro h
    have hmul := Nat.mul_le_mul_right n (Nat.succ_le_of_lt h)
    rw [Nat.succ_mul] at hmul
    unfold letter
    omega

theorem kFoldWord_filter_succ {n : ℕ} (w : Equiv.Perm (Fin n)) (k : ℕ) :
    (kFoldWord w (k + 1)).filter (fun a => decide (a ≤ k * n)) = kFoldWord w k := by
  unfold kFoldWord
  rw [List.filter_flatMap]
  apply List.flatMap_congr
  intro i _
  simp [block, List.range_succ, List.filter_append, List.filter_map, Function.comp_def,
    letter_lt_cutoff, List.filter_eq_self.mpr (fun c hc => decide_eq_true (List.mem_range.mp hc))]

#print axioms kFoldWord_nodup
#print axioms kFoldWord_filter_succ

end TableauStabilization
```

### `StabRestriction.lean`

```lean
import StabTableau
import StabWord

set_option autoImplicit false

namespace TableauStabilization

def small (b : ℕ) (x : ℕ) : Bool := decide (x ≤ b)

@[simp] theorem small_eq_true {b x : ℕ} : small b x = true ↔ x ≤ b := by simp [small]
@[simp] theorem small_eq_false {b x : ℕ} : small b x = false ↔ b < x := by simp [small]

def restrictRows (b : ℕ) (T : Tableau) : Tableau := T.map (List.filter (small b))

/-- Padded tableaux are equal when the rows agree at all indices. -/
def SameRows (T U : Tableau) : Prop := ∀ j, rowAt T j = rowAt U j

@[simp] theorem rowAt_cons_zero (r : List ℕ) (rs : Tableau) : rowAt (r :: rs) 0 = r := rfl

@[simp] theorem rowAt_cons_succ (r : List ℕ) (rs : Tableau) (j : ℕ) :
    rowAt (r :: rs) (j + 1) = rowAt rs j := rfl

@[simp] theorem rowAt_nil (j : ℕ) : rowAt [] j = [] := rfl

@[simp] theorem rowAt_restrictRows (b : ℕ) (T : Tableau) (j : ℕ) :
    rowAt (restrictRows b T) j = (rowAt T j).filter (small b) := by
  induction T generalizing j with
  | nil => rfl
  | cons r rs ih => cases j <;> simp [restrictRows, ← ih]

theorem SameRows.insert {T U : Tableau} (h : SameRows T U) (x : ℕ) :
    SameRows (TableauStabilization.insert x T) (TableauStabilization.insert x U) := by
  induction T generalizing U x with
  | nil =>
    cases U with
    | nil => exact fun _ => rfl
    | cons r rs =>
      have e : r = [] := (h 0).symm
      subst r
      intro j
      cases j with
      | zero => rfl
      | succ j => exact h (j + 1)
  | cons r rs ih =>
    cases U with
    | nil =>
      have e : r = [] := h 0
      subst r
      intro j
      cases j with
      | zero => rfl
      | succ j => exact h (j + 1)
    | cons s ss =>
      have e : r = s := h 0
      subst s
      have ht : SameRows rs ss := fun j => h (j + 1)
      intro j
      cases j with
      | zero =>
        simp [TableauStabilization.insert]
      | succ j =>
        cases hb : (insertRow x r).2 with
        | none => simpa [TableauStabilization.insert, hb] using ht j
        | some y => simpa [TableauStabilization.insert, hb] using ih ht y j

private theorem insertRow_filter_high {b x : ℕ} (h : b < x) (r : List ℕ) :
    (insertRow x r).1.filter (small b) = r.filter (small b) := by
  induction r with
  | nil => simp [insertRow, small, Nat.not_le_of_gt h]
  | cons y ys ih =>
    by_cases hx : x < y
    · simp [insertRow, hx, small, Nat.not_le_of_gt h, Nat.not_le_of_gt (h.trans hx)]
    · simp [insertRow, hx, List.filter_cons, ih]

theorem restrict_insert_high {b x : ℕ} (h : b < x) (T : Tableau) :
    SameRows (restrictRows b (insert x T)) (restrictRows b T) := by
  induction T generalizing x with
  | nil =>
    intro j
    cases j <;> simp [insert, small, Nat.not_le_of_gt h]
  | cons r rs ih =>
    intro j
    cases j with
    | zero => simpa [insert] using insertRow_filter_high h r
    | succ j =>
      cases hb : (insertRow x r).2 with
      | none => simp [insert, hb]
      | some y =>
        have ht := ih (h.trans (bump_gt hb)) j
        simpa [insert, hb] using ht

private theorem insertRow_filter_low {b x : ℕ} {r : List ℕ}
    (hx : x ≤ b) (hr : r.Pairwise (· < ·)) :
    ((insertRow x r).1.filter (small b), (insertRow x r).2.filter (small b)) =
      insertRow x (r.filter (small b)) := by
  induction r with
  | nil => simp [insertRow, small, hx]
  | cons y ys ih =>
    obtain ⟨hys, hs⟩ := List.pairwise_cons.mp hr
    by_cases hy : y ≤ b
    · by_cases hxy : x < y
      · have h1 := small_eq_true.mpr hx
        have h2 := small_eq_true.mpr hy
        simp [insertRow, hxy, h1, h2, Option.filter]
      · have h2 := small_eq_true.mpr hy
        simpa [insertRow, hxy, h2] using
          congrArg (fun p : List ℕ × Option ℕ => (y :: p.1, p.2)) (ih hs)
    · have hxy : x < y := by omega
      have hf : ys.filter (small b) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro a ha
        exact fun ha' => (Nat.not_le_of_gt ((Nat.lt_of_not_ge hy).trans (hys a ha))) (small_eq_true.mp ha')
      have h1 := small_eq_true.mpr hx
      have h2 := small_eq_false.mpr (Nat.lt_of_not_ge hy)
      simp [insertRow, hxy, h1, h2, hf, Option.filter]

theorem restrict_insert_low {b x : ℕ} {T : Tableau}
    (h : x ≤ b) (hv : Valid T) :
    SameRows (restrictRows b (insert x T)) (insert x (restrictRows b T)) := by
  induction T generalizing x with
  | nil =>
    intro j
    cases j <;> simp [insert, restrictRows, small, h]
  | cons r rs ih =>
    have he := insertRow_filter_low h hv.2.1
    have hrow := congrArg Prod.fst he
    have hbump := congrArg Prod.snd he
    intro j
    cases j with
    | zero =>
      simpa [insert, restrictRows] using hrow
    | succ j =>
      change rowAt ((insert x (r :: rs)).map (List.filter (small b))) (j + 1) =
        rowAt (insert x (r.filter (small b) :: restrictRows b rs)) (j + 1)
      cases hb : (insertRow x r).2 with
      | none =>
        have hb' : (insertRow x (r.filter (small b))).2 = none := by simpa [hb] using hbump.symm
        simp [insert, hb, hb', restrictRows]
      | some y =>
        by_cases hy : y ≤ b
        · have hb' : (insertRow x (r.filter (small b))).2 = some y := by
            simpa [hb, small, hy, Option.filter] using hbump.symm
          simpa [insert, hb, hb', restrictRows] using ih hy hv.2.2.2 j
        · have hb' : (insertRow x (r.filter (small b))).2 = none := by
            simpa [hb, small, hy, Option.filter] using hbump.symm
          simpa [insert, hb, hb', restrictRows] using restrict_insert_high (Nat.lt_of_not_ge hy) rs j

theorem restrict_foldInsert {b : ℕ} {T : Tableau} {w : List ℕ}
    (hv : Valid T) (hn : (w.reverse ++ T.flatten).Nodup) :
    SameRows (restrictRows b (w.foldl (fun U x => insert x U) T))
      ((w.filter (small b)).foldl (fun U x => insert x U) (restrictRows b T)) := by
  induction w generalizing T with
  | nil => exact fun _ => rfl
  | cons x xs ih =>
    have hnd : (xs.reverse ++ (x :: T.flatten)).Nodup := by
      simpa [List.reverse_cons, List.append_assoc] using hn
    have hx := (List.nodup_append.mp hnd).2.1
    have ht := ih (valid_insert hv hx)
      (((insert_perm x T).append_left xs.reverse).nodup_iff.mpr hnd)
    have hfold {A B : Tableau} (h : SameRows A B) :
        SameRows ((xs.filter (small b)).foldl (fun U y => insert y U) A)
          ((xs.filter (small b)).foldl (fun U y => insert y U) B) := by
      generalize xs.filter (small b) = ys
      induction ys generalizing A B with
      | nil => exact h
      | cons y ys ih' => exact ih' (h.insert y)
    intro j
    by_cases h : x ≤ b
    · simpa [small, h] using (ht j).trans (hfold (restrict_insert_low h hv) j)
    · simpa [small, h] using (ht j).trans (hfold (restrict_insert_high (Nat.lt_of_not_ge h) T) j)

theorem restrict_insertionTableau {w : List ℕ} (b : ℕ) (hn : w.Nodup) :
    SameRows (restrictRows b (insertionTableau w)) (insertionTableau (w.filter (small b))) := by
  exact restrict_foldInsert (T := []) trivial (by simpa using hn)

theorem kFoldWord_row_restriction {n : ℕ} (w : Equiv.Perm (Fin n)) (k j : ℕ) :
    (rowAt (insertionTableau (kFoldWord w (k + 1))) j).filter (small (k * n)) =
      rowAt (insertionTableau (kFoldWord w k)) j := by
  have h := restrict_insertionTableau (k * n) (kFoldWord_nodup w (k + 1)) j
  rw [rowAt_restrictRows] at h
  have he : (kFoldWord w (k + 1)).filter (small (k * n)) = kFoldWord w k :=
    kFoldWord_filter_succ w k
  rwa [he] at h

#print axioms kFoldWord_row_restriction

end TableauStabilization
```

### `StabCovers.lean`

```lean
import StabKnuth

set_option autoImplicit false

namespace TableauStabilization

/-- The color of a letter is its increasing chain, or absent if it is unused. -/
abbrev Coloring (t : ℕ) := ℕ → Option (Fin t)

def Good {t : ℕ} (r : ℕ → ℕ → Prop) (f : Coloring t) (a b : ℕ) : Prop :=
  ∀ c, f a = some c → f b = some c → r a b

def covered {t : ℕ} (f : Coloring t) (w : List ℕ) : ℕ :=
  (w.filter (fun a => (f a).isSome)).length

/-- There are t disjoint (possibly empty) chains of total size m. -/
def Attains (r : ℕ → ℕ → Prop) (t : ℕ) (w : List ℕ) (m : ℕ) : Prop :=
  ∃ f : Coloring t, w.Pairwise (Good r f) ∧ covered f w = m

theorem covered_append {t : ℕ} (f : Coloring t) (u v : List ℕ) :
    covered f (u ++ v) = covered f u + covered f v := by
  simp [covered]

theorem covered_congr {t : ℕ} {f g : Coloring t} {w : List ℕ}
    (h : ∀ a ∈ w, (f a).isSome = (g a).isSome) : covered f w = covered g w := by
  exact congrArg List.length (List.filter_congr h)

theorem Attains.reverse {r : ℕ → ℕ → Prop} {t m : ℕ} {w : List ℕ} :
    Attains (fun a b => r b a) t w.reverse m ↔ Attains r t w m := by
  have hgood (f : Coloring t) :
      w.reverse.Pairwise (Good (fun a b => r b a) f) ↔ w.Pairwise (Good r f) := by
    rw [List.pairwise_reverse]
    apply List.Pairwise.iff
    intro a b
    constructor <;> intro h c h₁ h₂ <;> exact h c h₂ h₁
  simp [Attains, hgood, covered]

structure TripleGood {t : ℕ} (r : ℕ → ℕ → Prop) (f : Coloring t)
    (p : List ℕ) (x y z : ℕ) (q : List ℕ) : Prop where
  prefixGood : p.Pairwise (Good r f)
  suffixGood : q.Pairwise (Good r f)
  across : ∀ a ∈ p, ∀ b ∈ q, Good r f a b
  leftX : ∀ a ∈ p, Good r f a x
  leftY : ∀ a ∈ p, Good r f a y
  leftZ : ∀ a ∈ p, Good r f a z
  rightX : ∀ b ∈ q, Good r f x b
  rightY : ∀ b ∈ q, Good r f y b
  rightZ : ∀ b ∈ q, Good r f z b
  xy : Good r f x y
  xz : Good r f x z
  yz : Good r f y z

theorem tripleGood_iff {t : ℕ} {r : ℕ → ℕ → Prop} {f : Coloring t}
    {p q : List ℕ} {x y z : ℕ} :
    (p ++ [x,y,z] ++ q).Pairwise (Good r f) ↔ TripleGood r f p x y z q := by
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.pairwise_append,
    List.pairwise_cons, List.mem_cons]
  constructor
  · rintro ⟨hp, ⟨hx, hy, hzq, hq⟩, ha⟩
    exact ⟨hp, hq, fun a h b hb => ha a h b (Or.inr (Or.inr (Or.inr hb))),
      fun a h => ha a h x (Or.inl rfl), fun a h => ha a h y (Or.inr (Or.inl rfl)),
      fun a h => ha a h z (Or.inr (Or.inr (Or.inl rfl))),
      (fun b hb => hx b (Or.inr (Or.inr hb))), (fun b hb => hy b (Or.inr hb)), hzq,
      hx y (Or.inl rfl), hx z (Or.inr (Or.inl rfl)), hy z (Or.inl rfl)⟩
  · intro h
    refine ⟨h.prefixGood, ⟨?_, ?_, h.rightZ, h.suffixGood⟩, ?_⟩
    · rintro a (rfl | rfl | ha)
      · exact h.xy
      · exact h.xz
      · exact h.rightX a ha
    · rintro a (rfl | ha)
      · exact h.yz
      · exact h.rightY a ha
    · rintro a ha b (rfl | rfl | rfl | hb)
      · exact h.leftX a ha
      · exact h.leftY a ha
      · exact h.leftZ a ha
      · exact h.across a ha b hb

/-- If two letters have no common color, either order satisfies the pair test. -/
theorem good_of_no_common {t : ℕ} {r : ℕ → ℕ → Prop} {f : Coloring t} {a b : ℕ}
    (h : ¬ ∃ c, f a = some c ∧ f b = some c) : Good r f a b :=
  fun c ha hb => (h ⟨c, ha, hb⟩).elim

theorem tripleGood_swap_of_no_common {t : ℕ} {r : ℕ → ℕ → Prop} {f : Coloring t}
    {p q : List ℕ} {x y z : ℕ} (h : TripleGood r f p x z y q)
    (hc : ¬ ∃ c, f z = some c ∧ f x = some c) : TripleGood r f p z x y q where
  prefixGood := h.prefixGood
  suffixGood := h.suffixGood
  across := h.across
  leftX := h.leftY
  leftY := h.leftX
  leftZ := h.leftZ
  rightX := h.rightY
  rightY := h.rightX
  rightZ := h.rightZ
  xy := good_of_no_common hc
  xz := h.yz
  yz := h.xz

theorem covered_swap_first {t : ℕ} (f : Coloring t) (p q : List ℕ) (x y z : ℕ) :
    covered f (p ++ [x,z,y] ++ q) = covered f (p ++ [z,x,y] ++ q) :=
  (((List.Perm.swap z x [y]).append_left p).append_right q).filter _ |>.length_eq

theorem attains_first_backward {r : ℕ → ℕ → Prop} {t m x y z : ℕ} {p q : List ℕ}
    (hzx : ¬ r z x) (h : Attains r t (p ++ [z,x,y] ++ q) m) :
    Attains r t (p ++ [x,z,y] ++ q) m := by
  obtain ⟨f, hs, hm⟩ := h
  have hg := tripleGood_iff.mp hs
  have hnone : ¬ ∃ c, f x = some c ∧ f z = some c := by
    rintro ⟨c, hx, hz⟩
    exact hzx (hg.xy c hz hx)
  exact ⟨f, tripleGood_iff.mpr (tripleGood_swap_of_no_common hg hnone),
    (covered_swap_first f p q x y z).trans hm⟩

theorem attains_first_no_conflict {r : ℕ → ℕ → Prop} {t x y z : ℕ} {p q : List ℕ}
    {f : Coloring t} (hs : (p ++ [x,z,y] ++ q).Pairwise (Good r f))
    (hc : ¬ ∃ c, f x = some c ∧ f z = some c) :
    Attains r t (p ++ [z,x,y] ++ q) (covered f (p ++ [x,z,y] ++ q)) := by
  have hn : ¬ ∃ c, f z = some c ∧ f x = some c := by
    rintro ⟨c, hz, hx⟩
    exact hc ⟨c, hx, hz⟩
  exact ⟨f, tripleGood_iff.mpr (tripleGood_swap_of_no_common (tripleGood_iff.mp hs) hn),
    (covered_swap_first f p q x y z).symm⟩

#print axioms attains_first_backward
#print axioms attains_first_no_conflict


private theorem context_separation {p q : List ℕ} {x y z : ℕ}
    (h : (p ++ [x,z,y] ++ q).Nodup) :
    (∀ a ∈ p, a ≠ y ∧ a ≠ z ∧ a ∉ q) ∧
    (∀ a ∈ q, a ≠ y ∧ a ≠ z) ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ x ∉ q := by
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.nodup_append,
    List.nodup_cons, List.mem_cons] at h
  grind

private theorem good_of_eq {t : ℕ} {r : ℕ → ℕ → Prop} {f g : Coloring t} {a b : ℕ}
    (ha : g a = f a) (hb : g b = f b) (h : Good r f a b) : Good r g a b :=
  fun c h₁ h₂ => h c (ha ▸ h₁) (hb ▸ h₂)

private theorem pairwise_good_of_eq {t : ℕ} {r : ℕ → ℕ → Prop} {f g : Coloring t}
    {l : List ℕ} (he : ∀ a ∈ l, g a = f a) (h : l.Pairwise (Good r f)) :
    l.Pairwise (Good r g) :=
  List.Pairwise.imp_of_mem (fun ha hb h => good_of_eq (he _ ha) (he _ hb) h) h

private theorem covered_triple_congr {t : ℕ} {f g : Coloring t} {p q : List ℕ} {x y z : ℕ}
    (hp : ∀ a ∈ p, (f a).isSome = (g a).isSome)
    (hq : ∀ a ∈ q, (f a).isSome = (g a).isSome)
    (h : covered f [x,z,y] = covered g [z,x,y]) :
    covered f (p ++ [x,z,y] ++ q) = covered g (p ++ [z,x,y] ++ q) := by
  simp only [covered_append]
  rw [covered_congr hp, covered_congr hq, h]

private theorem exchange_unused {r : ℕ → ℕ → Prop} {t x y z : ℕ} {p q : List ℕ}
    {f : Coloring t} (h : TripleGood r f p x z y q) (hnd : (p ++ [x,z,y] ++ q).Nodup)
    (hxy : r x y) (hyz : r y z) (htr : ∀ a b c, r a b → r b c → r a c)
    {c : Fin t} (hx : f x = some c) (hy : f y = none) (hz : f z = some c) :
    Attains r t (p ++ [z,x,y] ++ q) (covered f (p ++ [x,z,y] ++ q)) := by
  classical
  obtain ⟨hp, hq, hxy', hxz', hyz', _⟩ := context_separation hnd
  let g : Coloring t := fun a => if a = z then none else if a = y then some c else f a
  have gp (a : ℕ) (ha : a ∈ p) : g a = f a := by simp [g, (hp a ha).1, (hp a ha).2.1]
  have gq (a : ℕ) (ha : a ∈ q) : g a = f a := by simp [g, (hq a ha).1, (hq a ha).2]
  have gx : g x = some c := by simp [g, hxz', hxy', hx]
  have gy : g y = some c := by simp [g, hyz']
  have gz : g z = none := by simp [g]
  refine ⟨g, tripleGood_iff.mpr ?_, (covered_triple_congr ?_ ?_ ?_).symm⟩
  · refine ⟨pairwise_good_of_eq gp h.prefixGood, pairwise_good_of_eq gq h.suffixGood,
      fun a ha b hb => good_of_eq (gp a ha) (gq b hb) (h.across a ha b hb),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a ha d _ hd
      simp [gz] at hd
    · exact fun a ha => good_of_eq (gp a ha) (gx.trans hx.symm) (h.leftX a ha)
    · intro a ha d ha' hd
      have e : d = c := by simpa [gy, eq_comm] using hd
      subst d
      exact htr a x y (h.leftX a ha c ((gp a ha).symm ▸ ha') hx) hxy
    · intro b hb d hd
      simp [gz] at hd
    · exact fun b hb => good_of_eq (gx.trans hx.symm) (gq b hb) (h.rightX b hb)
    · intro b hb d hd hd'
      have e : d = c := by simpa [gy, eq_comm] using hd
      subst d
      exact htr y z b hyz (h.rightY b hb c hz ((gq b hb).symm ▸ hd'))
    · intro d hd
      simp [gz] at hd
    · intro d hd
      simp [gz] at hd
    · exact fun _ _ _ => hxy
  · exact fun a ha => congrArg Option.isSome (gp a ha).symm
  · exact fun a ha => congrArg Option.isSome (gq a ha).symm
  · simp [covered, gx, gy, gz, hx, hy, hz]

private def flipColors {t : ℕ} (c d : Fin t) (a : Option (Fin t)) : Option (Fin t) :=
  if a = some c then some d else if a = some d then some c else a

private theorem flipColors_eq_c {t : ℕ} {c d : Fin t} (h : c ≠ d) (a : Option (Fin t)) :
    flipColors c d a = some c ↔ a = some d := by
  by_cases hc : a = some c <;> by_cases hd : a = some d <;>
    simp_all [flipColors, Ne.symm h]

private theorem flipColors_eq_d {t : ℕ} {c d : Fin t} (h : c ≠ d) (a : Option (Fin t)) :
    flipColors c d a = some d ↔ a = some c := by
  by_cases hc : a = some c <;> by_cases hd : a = some d <;>
    simp_all [flipColors, Ne.symm h]

private theorem flipColors_eq_other {t : ℕ} {c d e : Fin t} (hc : e ≠ c) (hd : e ≠ d)
    (a : Option (Fin t)) : flipColors c d a = some e ↔ a = some e := by
  by_cases hac : a = some c <;> by_cases had : a = some d <;>
    simp_all [flipColors, Ne.symm hc, Ne.symm hd]

private theorem flipColors_involutive {t : ℕ} {c d : Fin t} (h : c ≠ d) :
    Function.Involutive (flipColors c d) := by
  intro a
  by_cases hc : a = some c <;> by_cases hd : a = some d <;>
    simp_all [flipColors, Ne.symm h]

private theorem flipColors_isSome {t : ℕ} (c d : Fin t) (a : Option (Fin t)) :
    (flipColors c d a).isSome = a.isSome := by
  unfold flipColors
  split <;> rename_i h
  · simp [h]
  · split <;> rename_i h'
    · simp [h']
    · rfl

private theorem exchange_used {r : ℕ → ℕ → Prop} {t x y z : ℕ} {p q : List ℕ}
    {f : Coloring t} (h : TripleGood r f p x z y q) (hnd : (p ++ [x,z,y] ++ q).Nodup)
    (hxy : r x y) (hyz : r y z) (htr : ∀ a b c, r a b → r b c → r a c)
    {c d : Fin t} (hcd : c ≠ d)
    (hx : f x = some c) (hy : f y = some d) (hz : f z = some c) :
    Attains r t (p ++ [z,x,y] ++ q) (covered f (p ++ [x,z,y] ++ q)) := by
  classical
  obtain ⟨hp, hq, hxy', hxz', hyz', hxq⟩ := context_separation hnd
  let g : Coloring t := fun a =>
    if a = z then some d else if a = y then some c else
      if a ∈ q then flipColors c d (f a) else f a
  have gp (a : ℕ) (ha : a ∈ p) : g a = f a := by
    simp [g, (hp a ha).1, (hp a ha).2.1, (hp a ha).2.2]
  have gq (a : ℕ) (ha : a ∈ q) : g a = flipColors c d (f a) := by
    simp [g, (hq a ha).1, (hq a ha).2, ha]
  have gx : g x = some c := by simp [g, hxz', hxy', hxq, hx]
  have gy : g y = some c := by simp [g, hyz']
  have gz : g z = some d := by simp [g]
  have gqc (a : ℕ) (ha : a ∈ q) : g a = some c ↔ f a = some d := by
    rw [gq a ha, flipColors_eq_c hcd]
  have gqd (a : ℕ) (ha : a ∈ q) : g a = some d ↔ f a = some c := by
    rw [gq a ha, flipColors_eq_d hcd]
  have gqe (a : ℕ) (ha : a ∈ q) (e : Fin t) (hc : e ≠ c) (hd : e ≠ d) :
      g a = some e ↔ f a = some e := by
    rw [gq a ha, flipColors_eq_other hc hd]
  have suffix : q.Pairwise (Good r g) := by
    refine h.suffixGood.imp_of_mem ?_
    intro a b ha hb hh e h₁ h₂
    have he : flipColors c d (f a) = flipColors c d (f b) :=
      (gq a ha).symm.trans (h₁.trans (h₂.symm.trans (gq b hb)))
    have hab := (flipColors_involutive hcd).injective he
    cases hfa : f a with
    | none => simp [gq a ha, hfa, flipColors] at h₁
    | some u => exact hh u hfa (hab.symm.trans hfa)
  have across (a : ℕ) (ha : a ∈ p) (b : ℕ) (hb : b ∈ q) : Good r g a b := by
    intro e h₁ h₂
    have h₁' := (gp a ha).symm.trans h₁
    by_cases hc : e = c
    · subst e
      exact htr a x b (h.leftX a ha c h₁' hx)
        (htr x y b hxy (h.rightZ b hb d hy ((gqc b hb).mp h₂)))
    by_cases hd : e = d
    · subst e
      exact htr a y b (h.leftZ a ha d h₁' hy)
        (htr y z b hyz (h.rightY b hb c hz ((gqd b hb).mp h₂)))
    exact h.across a ha b hb e h₁' ((gqe b hb e hc hd).mp h₂)
  refine ⟨g, tripleGood_iff.mpr ?_, (covered_triple_congr ?_ ?_ ?_).symm⟩
  · refine ⟨pairwise_good_of_eq gp h.prefixGood, suffix, across, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a ha e h₁ h₂
      have he : e = d := Option.some.inj (h₂.symm.trans gz)
      subst e
      exact htr a y z (h.leftZ a ha d ((gp a ha).symm.trans h₁) hy) hyz
    · exact fun a ha => good_of_eq (gp a ha) (gx.trans hx.symm) (h.leftX a ha)
    · intro a ha e h₁ h₂
      have he : e = c := Option.some.inj (h₂.symm.trans gy)
      subst e
      exact htr a x y (h.leftX a ha c ((gp a ha).symm.trans h₁) hx) hxy
    · intro b hb e h₁ h₂
      have he : e = d := Option.some.inj (h₁.symm.trans gz)
      subst e
      exact h.rightY b hb c hz ((gqd b hb).mp h₂)
    · intro b hb e h₁ h₂
      have he : e = c := Option.some.inj (h₁.symm.trans gx)
      subst e
      exact htr x y b hxy (h.rightZ b hb d hy ((gqc b hb).mp h₂))
    · intro b hb e h₁ h₂
      have he : e = c := Option.some.inj (h₁.symm.trans gy)
      subst e
      exact h.rightZ b hb d hy ((gqc b hb).mp h₂)
    · intro e h₁ h₂
      exact (hcd (Option.some.inj (gx.symm.trans (h₂.trans (h₁.symm.trans gz))))).elim
    · intro e h₁ h₂
      exact (hcd (Option.some.inj (gy.symm.trans (h₂.trans (h₁.symm.trans gz))))).elim
    · exact fun _ _ _ => hxy
  · exact fun a ha => congrArg Option.isSome (gp a ha).symm
  · intro a ha
    rw [gq a ha, flipColors_isSome]
  · simp [covered, gx, gy, gz, hx, hy, hz]

theorem attains_first_iff {r : ℕ → ℕ → Prop} {t m x y z : ℕ} {p q : List ℕ}
    (hnd : (p ++ [x,z,y] ++ q).Nodup)
    (hxy : r x y) (hyz : r y z) (htr : ∀ a b c, r a b → r b c → r a c)
    (has : ∀ a b, r a b → ¬ r b a) :
    Attains r t (p ++ [x,z,y] ++ q) m ↔ Attains r t (p ++ [z,x,y] ++ q) m := by
  refine ⟨?_, attains_first_backward (has x z (htr x y z hxy hyz))⟩
  rintro ⟨f, hs, rfl⟩
  by_cases hc : ∃ c, f x = some c ∧ f z = some c
  · obtain ⟨c, hx, hz⟩ := hc
    have h := tripleGood_iff.mp hs
    cases hy : f y with
    | none => exact exchange_unused h hnd hxy hyz htr hx hy hz
    | some d =>
      have hcd : c ≠ d := by
        rintro rfl
        exact has y z hyz (h.yz c hz hy)
      exact exchange_used h hnd hxy hyz htr hcd hx hy hz
  · exact attains_first_no_conflict hs hc

#print axioms attains_first_iff


theorem attains_second_iff {t m x y z : ℕ} {p q : List ℕ}
    (hnd : (p ++ [y,x,z] ++ q).Nodup) (hxy : x < y) (hyz : y < z) :
    Attains (· < ·) t (p ++ [y,x,z] ++ q) m ↔
      Attains (· < ·) t (p ++ [y,z,x] ++ q) m := by
  have hd : (q.reverse ++ [z,x,y] ++ p.reverse).Nodup := by
    have he := List.nodup_reverse.mpr hnd
    simpa [List.reverse_append, List.append_assoc] using he
  have h := attains_first_iff (t := t) (m := m) (r := fun a b => b < a) hd hyz hxy
    (fun _ _ _ h₁ h₂ => Nat.lt_trans h₂ h₁) (fun _ _ h => Nat.not_lt_of_ge h.le)
  rw [← Attains.reverse (w := p ++ [y,x,z] ++ q), ← Attains.reverse (w := p ++ [y,z,x] ++ q)]
  simpa [List.reverse_append, List.append_assoc] using h

theorem Knuth.attains_iff {u v : List ℕ} (h : Knuth u v) (hn : u.Nodup) (t m : ℕ) :
    Attains (· < ·) t u m ↔ Attains (· < ·) t v m := by
  induction h with
  | first _ _ hxy hyz =>
    exact attains_first_iff hn hxy hyz (fun _ _ _ => Nat.lt_trans)
      (fun _ _ h => Nat.not_lt_of_ge h.le)
  | second _ _ hxy hyz => exact attains_second_iff hn hxy hyz
  | refl => rfl
  | symm h ih => exact (ih (h.perm.nodup_iff.mpr hn)).symm
  | trans h _ ih₁ ih₂ => exact (ih₁ hn).trans (ih₂ (h.perm.nodup_iff.mp hn))

theorem insertionTableau_attains_iff {w : List ℕ} (hn : w.Nodup) (t m : ℕ) :
    Attains (· < ·) t w m ↔ Attains (· < ·) t (readingWord (insertionTableau w)) m :=
  (knuth_insertionTableau hn).attains_iff hn t m

#print axioms insertionTableau_attains_iff

end TableauStabilization
```

### `StabGreene.lean`

```lean
import StabCovers
import Mathlib.Data.List.FinRange

set_option autoImplicit false

namespace TableauStabilization

open scoped List

def topSize (T : Tableau) (t : ℕ) : ℕ := (T.take t).flatten.length

/-- This condition allows empty rows at the end when columns are removed. -/
def ColumnsOK : Tableau → Prop
  | [] => True
  | r :: rs => Above r (rowAt rs 0) ∧ ColumnsOK rs

theorem Valid.columnsOK {T : Tableau} (h : Valid T) : ColumnsOK T := by
  induction T with
  | nil => trivial
  | cons r rs ih => exact ⟨h.2.2.1, ih h.2.2.2⟩

def firstColumn : Tableau → List ℕ
  | [] => []
  | r :: rs => firstColumn rs ++ r.head?.toList

def dropColumn (T : Tableau) : Tableau := T.map List.tail

private theorem firstColumn_sublist (T : Tableau) : (firstColumn T).Sublist (readingWord T) := by
  induction T with
  | nil => exact List.Sublist.slnil
  | cons r rs ih =>
    have h : r.head?.toList <+ r := by cases r <;> simp
    simpa [firstColumn, readingWord] using ih.append h

private theorem Above.tail {r s : List ℕ} (h : Above r s) : Above r.tail s.tail := by
  cases h with
  | nil => exact Above.nil _
  | cons _ h => exact h

private theorem dropColumn_columnsOK {T : Tableau} (h : ColumnsOK T) :
    ColumnsOK (dropColumn T) := by
  induction T with
  | nil => trivial
  | cons r rs ih =>
    have he : rowAt (dropColumn rs) 0 = (rowAt rs 0).tail := by cases rs <;> rfl
    exact ⟨he.symm ▸ h.1.tail, ih h.2⟩

private theorem firstColumn_eq_nil {T : Tableau} (h : ColumnsOK T) (he : rowAt T 0 = []) :
    firstColumn T = [] := by
  induction T with
  | nil => rfl
  | cons r rs ih =>
    change r = [] at he
    subst r
    have hnil : rowAt rs 0 = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero h.1.length_le)
    simpa [firstColumn] using ih h.2 hnil

private theorem head_lt_of_mem_firstColumn {T : Tableau} {a b : ℕ}
    (h : ColumnsOK T) (ha : (rowAt T 0).head? = some a) (hb : b ∈ firstColumn T) : a ≤ b := by
  induction T generalizing a with
  | nil => simp [firstColumn] at hb
  | cons r rs ih =>
    change r.head? = some a at ha
    obtain ⟨hcol, htail⟩ := h
    change b ∈ firstColumn rs ++ r.head?.toList at hb
    rcases (List.mem_append (s := firstColumn rs) (t := r.head?.toList)).mp hb with hb' | hb'
    · cases e : rowAt rs 0 with
      | nil => simp [firstColumn_eq_nil htail e] at hb'
      | cons c cs =>
        cases r with
        | nil => simp at ha
        | cons a' as =>
          have hlt : a' < c := by
            rw [e] at hcol
            cases hcol with
            | cons h _ => exact h
          have hc := ih htail (a := c) (by simp [e]) hb'
          simp at ha
          omega
    · simp [ha] at hb'
      exact hb' ▸ Nat.le_refl a

private theorem firstColumn_decreasing {T : Tableau} (h : ColumnsOK T) :
    (firstColumn T).Pairwise (· > ·) := by
  induction T with
  | nil => simp [firstColumn]
  | cons r rs ih =>
    obtain ⟨hcol, htail⟩ := h
    rw [firstColumn, List.pairwise_append]
    refine ⟨ih htail, ?_, ?_⟩
    · cases r <;> simp
    · intro a ha b hb
      cases r with
      | nil => simp at hb
      | cons x xs =>
        have he : b = x := by simpa using hb
        subst b
        cases e : rowAt rs 0 with
        | nil => simp [firstColumn_eq_nil htail e] at ha
        | cons y ys =>
          have hlt : x < y := by
            rw [e] at hcol
            cases hcol with
            | cons h _ => exact h
          exact hlt.trans_le (head_lt_of_mem_firstColumn htail (by simp [e]) ha)

private theorem covered_split_column {t : ℕ} (f : Coloring t) (T : Tableau) :
    covered f (readingWord T) =
      covered f (firstColumn T) + covered f (readingWord (dropColumn T)) := by
  induction T with
  | nil => rfl
  | cons r rs ih =>
    cases r with
    | nil => simpa [readingWord, firstColumn, dropColumn] using ih
    | cons x xs =>
      simp only [readingWord, List.reverse_cons, List.flatten_append, List.flatten_cons,
        List.flatten_nil, List.append_nil, firstColumn, List.head?_cons, Option.toList_some,
        dropColumn, List.map_cons, List.tail_cons, covered_append] at ih ⊢
      have he : covered f (x :: xs) = covered f [x] + covered f xs := covered_append f [x] xs
      omega

private theorem firstColumn_take_len {T : Tableau} (h : ColumnsOK T) (t : ℕ) :
    (firstColumn (T.take t)).length = min t (firstColumn T).length := by
  induction T generalizing t with
  | nil => simp [firstColumn]
  | cons r rs ih =>
    cases t with
    | zero => simp [firstColumn]
    | succ t =>
      obtain ⟨hcol, htail⟩ := h
      cases r with
      | nil =>
        have hz : rowAt rs 0 = [] :=
          List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hcol.length_le)
        simp [firstColumn, firstColumn_eq_nil htail hz, ih htail]
      | cons x xs =>
        simp [firstColumn, ih htail]

private theorem topSize_split_column (T : Tableau) (t : ℕ) :
    topSize T t = (firstColumn (T.take t)).length + topSize (dropColumn T) t := by
  induction T generalizing t with
  | nil => simp [topSize, firstColumn, dropColumn]
  | cons r rs ih =>
    cases t with
    | zero => simp [topSize, firstColumn]
    | succ t =>
      have h := ih t
      cases r <;>
        simp [topSize, firstColumn, dropColumn] at h ⊢ <;> omega

private theorem covered_le_length {t : ℕ} (f : Coloring t) (w : List ℕ) :
    covered f w ≤ w.length :=
  List.length_filter_le _ _

private theorem covered_decreasing_le {t : ℕ} (f : Coloring t) {w : List ℕ}
    (hg : w.Pairwise (Good (· < ·) f)) (hd : w.Pairwise (· > ·)) :
    covered f w ≤ t := by
  have hp : w.Pairwise (fun a b => ∀ c, f a = some c → f b ≠ some c) := by
    refine (hg.and hd).imp ?_
    intro a b hh c ha hb
    exact Nat.lt_asymm (hh.1 c ha hb) hh.2
  have hn : (w.filterMap f).Nodup := by
    rw [List.Nodup, List.pairwise_filterMap]
    apply hp.imp
    intro a b h c hc d hd hcd
    subst d
    exact h c hc hd
  have hsub : w.filterMap f ⊆ List.finRange t := fun _ _ => List.mem_finRange _
  have hs := (hn.length_le_of_subset hsub).trans_eq (List.length_finRange (n := t))
  have hlen : (w.filterMap f).length = covered f w := by
    clear hg hd hp hn hsub hs
    induction w with
    | nil => rfl
    | cons a as ih =>
      unfold covered at ih ⊢
      cases hf : f a <;> simp [hf, ih]
  simpa only [hlen] using hs

private theorem dropColumn_length_le (T : Tableau) :
    (dropColumn T).flatten.length ≤ T.flatten.length := by
  induction T with
  | nil => rfl
  | cons r rs ih =>
    have hr : r.tail.length ≤ r.length := (List.tail_sublist r).length_le
    simpa only [dropColumn, List.map_cons, List.flatten_cons, List.length_append] using
      Nat.add_le_add hr ih

private theorem dropColumn_measure {T : Tableau} (h : T.flatten.length ≠ 0) :
    (dropColumn T).flatten.length < T.flatten.length := by
  induction T with
  | nil => simp at h
  | cons r rs ih =>
    cases r with
    | nil =>
      have h' : rs.flatten.length ≠ 0 := by simpa using h
      simpa [dropColumn] using ih h'
    | cons x xs =>
      have hweak := dropColumn_length_le rs
      simp [dropColumn] at hweak ⊢
      omega

theorem covered_readingWord_le {T : Tableau} {t : ℕ} {f : Coloring t}
    (hc : ColumnsOK T) (hg : (readingWord T).Pairwise (Good (· < ·) f)) :
    covered f (readingWord T) ≤ topSize T t := by
  by_cases hzero : T.flatten.length = 0
  · have he := (readingWord_perm T).length_eq
    have h := covered_le_length f (readingWord T)
    omega
  have hm := dropColumn_measure hzero
  have hsub : readingWord (dropColumn T) <+ readingWord T := by
    clear hg hc hm hzero
    induction T with
    | nil => exact List.Sublist.slnil
    | cons r rs ih =>
      have ht : r.tail <+ r := List.tail_sublist r
      simpa [readingWord, dropColumn] using ih.append ht
  have htail := covered_readingWord_le (dropColumn_columnsOK hc) (hg.sublist hsub)
  have hcol := covered_decreasing_le f (hg.sublist (firstColumn_sublist T)) (firstColumn_decreasing hc)
  have hsize := covered_le_length f (firstColumn T)
  rw [covered_split_column, topSize_split_column, firstColumn_take_len hc]
  omega
termination_by T.flatten.length
decreasing_by simpa using hm

#print axioms covered_readingWord_le


theorem topSize_succ (T : Tableau) (t : ℕ) :
    topSize T (t + 1) = topSize T t + rowLength T t := by
  induction T generalizing t with
  | nil => simp [topSize, rowLength, rowAt]
  | cons r rs ih =>
    cases t with
    | zero => simp [topSize, rowLength, rowAt]
    | succ t =>
      have h := ih t
      simp [topSize, rowLength, rowAt] at h ⊢
      omega

theorem topSize_le_total (T : Tableau) (t : ℕ) : topSize T t ≤ T.flatten.length := by
  have he := congrArg List.flatten (List.take_append_drop t T)
  rw [List.flatten_append] at he
  rw [topSize, ← he, List.length_append]
  exact Nat.le_add_right _ _

theorem topSize_eq_total {T : Tableau} {t : ℕ} (h : T.length ≤ t) :
    topSize T t = T.flatten.length := by simp [topSize, List.take_of_length_le h]

theorem attains_topSize {T : Tableau} (hs : ∀ r ∈ T, List.Pairwise (· < ·) r)
    (hn : T.flatten.Nodup) (t : ℕ) :
    Attains (· < ·) t (readingWord T) (topSize T t) := by
  induction T generalizing t with
  | nil =>
    exact ⟨fun _ => none, List.Pairwise.nil, by simp [covered, readingWord, topSize]⟩
  | cons r rs ih =>
    cases t with
    | zero =>
      refine ⟨fun _ => none, ?_, by simp [covered, topSize]⟩
      apply List.pairwise_of_forall
      intro a b c ha
      simp at ha
    | succ t =>
      obtain ⟨_, hnd, hsep⟩ := List.nodup_append.mp hn
      obtain ⟨f, hf, hcount⟩ := ih (fun s hs' => hs s (List.mem_cons_of_mem _ hs')) hnd t
      let g : Coloring (t + 1) := fun a => if a ∈ r then some 0 else (f a).map Fin.succ
      have g_in (a : ℕ) (ha : a ∈ r) : g a = some 0 := by simp [g, ha]
      have g_out (a : ℕ) (ha : a ∈ readingWord rs) : g a = (f a).map Fin.succ := by
        have ha' : a ∈ rs.flatten := (readingWord_perm rs).mem_iff.mp ha
        have hnot : a ∉ r := fun hr => hsep a hr a ha' rfl
        simp [g, hnot]
      have htail : (readingWord rs).Pairwise (Good (· < ·) g) := by
        refine hf.imp_of_mem ?_
        intro a b ha hb hab c h₁ h₂
        rw [g_out a ha] at h₁
        rw [g_out b hb] at h₂
        cases ha' : f a with
        | none => simp [ha'] at h₁
        | some x =>
          cases hb' : f b with
          | none => simp [hb'] at h₂
          | some y =>
            simp [ha'] at h₁
            simp [hb'] at h₂
            have he : x = y := Fin.succ_inj.mp (h₁.trans h₂.symm)
            exact hab x ha' (he.symm ▸ hb')
      have hhead : r.Pairwise (Good (· < ·) g) :=
        (hs r List.mem_cons_self).imp (fun h _ _ _ => h)
      have hcross (a : ℕ) (ha : a ∈ readingWord rs) (b : ℕ) (hb : b ∈ r) :
          Good (· < ·) g a b := by
        intro c h₁ h₂
        rw [g_in b hb] at h₂
        have hc : c = 0 := (Option.some.inj h₂).symm
        subst c
        rw [g_out a ha] at h₁
        cases ha' : f a with
        | none => simp [ha'] at h₁
        | some x => simp [ha'] at h₁
      have hc₁ : covered g (readingWord rs) = covered f (readingWord rs) := by
        apply congrArg List.length
        exact List.filter_congr (fun a ha => by simp [g_out a ha])
      have hc₂ : covered g r = r.length := by
        unfold covered
        rw [List.filter_eq_self.mpr]
        intro a ha
        simp [g_in a ha]
      have he : readingWord (r :: rs) = readingWord rs ++ r := by simp [readingWord]
      refine ⟨g, ?_, ?_⟩
      · rw [he, List.pairwise_append]
        exact ⟨htail, hhead, hcross⟩
      · rw [he, covered_append, hc₁, hc₂, hcount]
        simp [topSize, Nat.add_comm]

/-- Distinct-letter Greene identity in witness-and-upper-bound form. -/
theorem greene {w : List ℕ} (hw : w.Nodup) (t : ℕ) :
    Attains (· < ·) t w (topSize (insertionTableau w) t) ∧
      ∀ m, Attains (· < ·) t w m → m ≤ topSize (insertionTableau w) t := by
  have hv := valid_insertionTableau hw
  have hn := (insertionTableau_perm w).nodup_iff.mpr hw
  have hs : ∀ r ∈ insertionTableau w, List.Pairwise (· < ·) r := by
    generalize insertionTableau w = T at hv
    induction T with
    | nil => simp
    | cons r rs ih =>
      intro s h
      rcases List.mem_cons.mp h with rfl | ht
      · exact hv.2.1
      · exact ih hv.2.2.2 s ht
  refine ⟨(insertionTableau_attains_iff hw _ _).mpr (attains_topSize hs hn t), ?_⟩
  intro m h
  obtain ⟨f, hf, rfl⟩ := (insertionTableau_attains_iff hw _ _).mp h
  exact covered_readingWord_le hv.columnsOK hf

#print axioms greene

end TableauStabilization
```

### `StabGrid.lean`

```lean
import StabGreene
import StabRestriction
import Mathlib.Data.List.ProdSigma
import Mathlib.Algebra.Group.End

set_option autoImplicit false

namespace TableauStabilization

open scoped List

abbrev Cell (n k : ℕ) := Fin n × Fin k

def before {n k : ℕ} (a b : Cell n k) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)

def cells (n k : ℕ) : List (Cell n k) := (List.finRange n).product (List.finRange k)

def value {n k : ℕ} (w : Equiv.Perm (Fin n)) (p : Cell n k) : ℕ :=
  letter w p.1 p.2.val

theorem value_injective {n k : ℕ} (w : Equiv.Perm (Fin n)) :
    Function.Injective (value (k := k) w) := by
  intro a b h
  obtain ⟨h₁, h₂⟩ := letter_injective w h
  exact Prod.ext h₁ (Fin.ext h₂)

theorem mem_cells {n k : ℕ} (a : Cell n k) : a ∈ cells n k := by
  rcases a with ⟨i,c⟩
  simp [cells]

theorem kFoldWord_eq_grid {n : ℕ} (w : Equiv.Perm (Fin n)) (k : ℕ) :
    kFoldWord w k = (cells n k).map (value w) := by
  unfold kFoldWord cells List.product
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro i _
  have he : (List.finRange k).map Fin.val = List.range k := by
    apply List.ext_getElem
    · simp
    · intro j h₁ h₂
      simp
  rw [block, ← he, List.map_map, List.map_map]
  rfl

private theorem finRange_pairwise_lt (n : ℕ) : (List.finRange n).Pairwise (· < ·) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj h
  simpa using h

theorem cells_before (n k : ℕ) : (cells n k).Pairwise before := by
  unfold cells
  have h := finRange_pairwise_lt n
  generalize List.finRange n = rows at h
  induction rows with
  | nil => exact List.Pairwise.nil
  | cons i rows ih =>
    obtain ⟨hi, hr⟩ := List.pairwise_cons.mp h
    change (((List.finRange k).map (fun j => (i, j))) ++ rows.product (List.finRange k)).Pairwise before
    rw [List.pairwise_append, List.pairwise_map]
    refine ⟨(finRange_pairwise_lt k).imp (fun hc => Or.inr ⟨rfl, hc⟩), ih hr, ?_⟩
    intro a ha b hb
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
    rcases b with ⟨j,y⟩
    exact Or.inl (hi j (List.mem_product.mp hb).1)

theorem before_asymm {n k : ℕ} {a b : Cell n k} (h : before a b) : ¬ before b a := by
  rcases h with h | ⟨he, h⟩
  · exact fun h' => h'.elim (fun h' => Nat.lt_asymm h h')
      (fun he => h.ne he.1.symm)
  · exact fun h' => h'.elim (fun h' => (ne_of_lt h') he.symm)
      (fun hc => Nat.lt_asymm h hc.2)

theorem cells_pairwise_iff {n k : ℕ} {r : Cell n k → Cell n k → Prop} :
    (cells n k).Pairwise r ↔ ∀ a b, before a b → r a b := by
  constructor
  · intro hr a b hab
    obtain ⟨i, hi, hai⟩ := List.getElem_of_mem (mem_cells a)
    obtain ⟨j, hj, hbj⟩ := List.getElem_of_mem (mem_cells b)
    rcases lt_trichotomy i j with h | he | h
    · simpa [hai, hbj] using hr.rel_getElem_of_lt hi hj h
    · subst j
      have hab' : a = b := hai.symm.trans hbj
      rw [hab'] at hab
      exact (before_asymm hab hab).elim
    · have hba := (cells_before n k).rel_getElem_of_lt hj hi h
      rw [hai, hbj] at hba
      exact (before_asymm hab hba).elim
  · intro hr
    exact (cells_before n k).imp (hr _ _)

noncomputable def colorWord {n k t : ℕ} (w : Equiv.Perm (Fin n))
    (f : Cell n k → Option (Fin t)) : Coloring t :=
  fun v => open Classical in
    if h : ∃ a, value w a = v then f h.choose else none

@[simp] theorem colorWord_value {n k t : ℕ} (w : Equiv.Perm (Fin n))
    (f : Cell n k → Option (Fin t)) (a : Cell n k) : colorWord w f (value w a) = f a := by
  classical
  unfold colorWord
  split
  · rename_i h
    rw [value_injective w h.choose_spec]
  · rename_i h
    exact (h ⟨a, rfl⟩).elim

theorem attains_grid {n k t : ℕ} {w : Equiv.Perm (Fin n)} (f : Cell n k → Option (Fin t))
    (h : ∀ a b, before a b → ∀ c, f a = some c → f b = some c → value w a < value w b) :
    Attains (· < ·) t (kFoldWord w k) ((cells n k).filter (fun a => (f a).isSome)).length := by
  refine ⟨colorWord w f, ?_, ?_⟩
  · rw [kFoldWord_eq_grid, List.pairwise_map, cells_pairwise_iff]
    intro a b hab c ha hb
    exact h a b hab c (by simpa using ha) (by simpa using hb)
  · rw [covered, kFoldWord_eq_grid, List.filter_map, List.length_map]
    simp [Function.comp_def]

theorem attains_grid_all {n k t : ℕ} {w : Equiv.Perm (Fin n)} (f : Cell n k → Fin t)
    (h : ∀ a b, before a b → f a = f b → value w a < value w b) :
    Attains (· < ·) t (kFoldWord w k) (n * k) := by
  have hs := attains_grid (w := w) (fun a => some (f a)) (by
    intro a b hab c ha hb
    exact h a b hab ((Option.some.inj ha).trans (Option.some.inj hb).symm))
  have he : (cells n k).length = n * k := by
    unfold cells
    change ((List.finRange n) ×ˢ (List.finRange k)).length = _
    simp [List.length_product]
  simpa [he] using hs

theorem topSize_n {n : ℕ} (w : Equiv.Perm (Fin n)) (k : ℕ) :
    topSize (insertionTableau (kFoldWord w k)) n = n * k := by
  have h := (greene (kFoldWord_nodup w k) n).2 _ (attains_grid_all (t := n)
    (w := w) (k := k) Prod.fst (by
      intro a b hab he
      have hc : a.2 < b.2 := hab.resolve_left (by simp [he]) |>.2
      exact letter_lt_of_copy_lt hc))
  have h' := topSize_le_total (insertionTableau (kFoldWord w k)) n
  rw [(insertionTableau_perm _).length_eq, kFoldWord_length] at h'
  exact Nat.le_antisymm h' h

theorem rowLength_id_zero_before_n {n k : ℕ} (hk : k < n) :
    rowLength (insertionTableau (kFoldWord (1 : Equiv.Perm (Fin n)) k)) (n - 1) = 0 := by
  let w : Equiv.Perm (Fin n) := 1
  have hcover : Attains (· < ·) (n - 1) (kFoldWord w k) (n * k) := by
    apply attains_grid_all (fun a => Fin.castLE (by omega) a.2)
    intro a b hab he
    have he' : a.2 = b.2 := Fin.ext (congrArg (fun i : Fin (n - 1) => i.val) he)
    have ha : a.1 < b.1 := hab.resolve_right (by simp [he'])
    exact (letter_lt_iff w a.1 b.1 a.2 b.2).mpr (Or.inr ⟨congrArg Fin.val he', ha⟩)
  have hlo := (greene (kFoldWord_nodup w k) (n - 1)).2 _ hcover
  have ht := topSize_n w k
  have hs := topSize_succ (insertionTableau (kFoldWord w k)) (n - 1)
  rw [show n - 1 + 1 = n by omega, ht] at hs
  change rowLength (insertionTableau (kFoldWord w k)) (n - 1) = 0
  omega

theorem id_not_stabilizes_before_n {n k : ℕ} (hk : k < n) :
    ¬ stabilizesAt (1 : Equiv.Perm (Fin n)) k := by
  intro h
  let i : Fin n := ⟨0, by omega⟩
  have ht := h.2 i
  have hn := (insertionTableau_perm _).nodup_iff.mpr (kFoldWord_nodup (1 : Equiv.Perm (Fin n)) k)
  have ha := (rowOf_eq_some_iff hn).mp ht
  have hz := rowLength_id_zero_before_n hk
  have hempty : rowAt (insertionTableau (kFoldWord (1 : Equiv.Perm (Fin n)) k)) (n - 1) = [] :=
    List.length_eq_zero_iff.mp hz
  simp [i, hempty] at ha

#print axioms topSize_n
#print axioms id_not_stabilizes_before_n

end TableauStabilization
```

### `StabShapeTest.lean`

```lean
import StabGrid
import Mathlib.Data.Nat.Find

set_option autoImplicit false

namespace TableauStabilization

def growsOne {n : ℕ} (w : Equiv.Perm (Fin n)) (k : ℕ) : Prop :=
  ∀ j < n, rowLength (insertionTableau (kFoldWord w (k + 1))) j =
    rowLength (insertionTableau (kFoldWord w k)) j + 1

/-- Last-copy letters are exactly the entries above the preceding word's cutoff. -/
theorem high_mem_iff {n k j x : ℕ} (w : Equiv.Perm (Fin n)) :
    x ∈ (rowAt (insertionTableau (kFoldWord w (k + 1))) j).filter (fun a => !small (k * n) a) ↔
      ∃ i : Fin n, x = lastCopy w (k + 1) i ∧
        x ∈ rowAt (insertionTableau (kFoldWord w (k + 1))) j := by
  apply List.mem_filter.trans
  constructor
  · rintro ⟨hr, hb⟩
    have hf : x ∈ (insertionTableau (kFoldWord w (k + 1))).flatten := by
      unfold rowAt at hr
      generalize he : (insertionTableau (kFoldWord w (k + 1)))[j]? = r at hr
      cases r with
      | none => simp at hr
      | some r => exact List.mem_flatten.mpr ⟨r, List.mem_of_getElem? he, hr⟩
    have hm := (insertionTableau_perm _).mem_iff.mp hf
    rw [kFoldWord_eq_grid, List.mem_map] at hm
    obtain ⟨⟨i,c⟩, _, rfl⟩ := hm
    have hnk : k ≤ c.val := by
      apply Nat.le_of_not_gt
      intro hc
      simp [small, (letter_lt_cutoff w i c.val k).mpr hc, value] at hb
    have hc : c.val = k := by have := c.isLt; omega
    exact ⟨i, by simp [value, lastCopy, hc], hr⟩
  · rintro ⟨i, rfl, hr⟩
    refine ⟨hr, ?_⟩
    have h : ¬ letter w i k ≤ k * n := (letter_lt_cutoff w i k k).not.mpr (Nat.lt_irrefl k)
    simpa [lastCopy] using small_eq_false.mpr (Nat.lt_of_not_ge h)

theorem rowAt_nodup {T : Tableau} (h : T.flatten.Nodup) (j : ℕ) :
    (rowAt T j).Nodup := by
  cases he : T[j]? with
  | none => simp [rowAt, he]
  | some r =>
    have hr : r.Nodup := (List.nodup_flatten.mp h).1 _ (List.mem_of_getElem? he)
    simpa [rowAt, he] using hr

theorem growsOne_of_stabilizesAt {n k : ℕ} (w : Equiv.Perm (Fin n))
    (h : stabilizesAt w (k + 1)) : growsOne w k := by
  intro j hj
  let T := insertionTableau (kFoldWord w (k + 1))
  let i : Fin n := ⟨n - 1 - j, by omega⟩
  have he : n - 1 - i.val = j := by dsimp [i]; omega
  have hn := (insertionTableau_perm _).nodup_iff.mpr (kFoldWord_nodup w (k + 1))
  have hlast : lastCopy w (k + 1) i ∈ rowAt T j := by
    apply (rowOf_eq_some_iff hn).mp
    simpa [he] using h.2 i
  have hone : ((rowAt T j).filter (fun a => !small (k * n) a)).length = 1 := by
    have hd := (rowAt_nodup hn j).filter (fun a => !small (k * n) a)
    have hp : List.Perm ((rowAt T j).filter (fun a => !small (k * n) a)) [lastCopy w (k + 1) i] := by
      apply (List.perm_ext_iff_of_nodup hd (by simp)).mpr
      intro x
      rw [high_mem_iff w, List.mem_singleton]
      constructor
      · rintro ⟨a, rfl, ha⟩
        have ha' := (rowOf_eq_some_iff hn).mpr ha
        have hr : n - 1 - a.val = j := Option.some.inj ((h.2 a).symm.trans ha')
        have e : a = i := Fin.ext (by dsimp [i]; have := a.isLt; omega)
        rw [e]
      · rintro rfl
        exact ⟨i, rfl, hlast⟩
    exact hp.length_eq
  have hsplit := List.length_eq_length_filter_add (l := rowAt T j) (small (k * n))
  change (rowAt T j).length = _
  change _ = ((rowAt T j).filter (small (k * n))).length + _ at hsplit
  rw [hone] at hsplit
  exact hsplit.trans (congrArg (fun s : List ℕ => s.length + 1) (kFoldWord_row_restriction w k j))

theorem growsOne_of_prefixGrowth {n k : ℕ} (w : Equiv.Perm (Fin n))
    (h : ∀ t ≤ n, topSize (insertionTableau (kFoldWord w (k + 1))) t =
      topSize (insertionTableau (kFoldWord w k)) t + t) : growsOne w k := by
  intro j hj
  have h₁ := h j hj.le
  have h₂ := h (j + 1) hj
  rw [topSize_succ, topSize_succ] at h₂
  omega

noncomputable def leastStabilization {n : ℕ} (w : Equiv.Perm (Fin n))
    (h : ∃ k, stabilizesAt w k) : ℕ :=
  open Classical in Nat.find h

theorem leastStabilization_spec {n : ℕ} {w : Equiv.Perm (Fin n)}
    (h : ∃ k, stabilizesAt w k) : stabilizesAt w (leastStabilization w h) :=
  open Classical in Nat.find_spec h

theorem leastStabilization_le {n k : ℕ} {w : Equiv.Perm (Fin n)}
    (h : ∃ j, stabilizesAt w j) (hk : stabilizesAt w k) : leastStabilization w h ≤ k :=
  open Classical in Nat.find_min' h hk

theorem leastStabilization_id {n : ℕ} (h : stabilizesAt (1 : Equiv.Perm (Fin n)) n) :
    leastStabilization 1 ⟨n, h⟩ = n := by
  apply le_antisymm (leastStabilization_le _ h)
  exact Nat.le_of_not_gt (fun hlt => id_not_stabilizes_before_n hlt (leastStabilization_spec _))

#print axioms growsOne_of_stabilizesAt
#print axioms growsOne_of_prefixGrowth
#print axioms leastStabilization_id

end TableauStabilization
```

### `StabBlock.lean`

```lean
import StabShapeTest

set_option autoImplicit false

namespace TableauStabilization

open scoped List

def insertWord (T : Tableau) (w : List ℕ) : Tableau :=
  w.foldl (fun U x => insert x U) T

/-- Inserting several letters into one row records the stream sent to the next row. -/
def runRow : List ℕ → List ℕ → List ℕ × List ℕ
  | [], r => (r, [])
  | x :: xs, r =>
    let p := insertRow x r
    let q := runRow xs p.1
    (q.1, p.2.toList ++ q.2)

theorem runRow_skip {xs r : List ℕ} {a : ℕ} (ha : ∀ x ∈ xs, a ≤ x) :
    runRow xs (a :: r) = (a :: (runRow xs r).1, (runRow xs r).2) := by
  induction xs generalizing r with
  | nil => rfl
  | cons x xs ih =>
    have ht : ¬ x < a := Nat.not_lt_of_ge (ha x List.mem_cons_self)
    have hs : ∀ y ∈ xs, a ≤ y := fun y hy => ha y (List.mem_cons_of_mem _ hy)
    simp [runRow, insertRow, ht, ih hs]

theorem runRow_empty {xs : List ℕ} (h : xs.Pairwise (· < ·)) : runRow xs [] = (xs, []) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨hx, hs⟩ := List.pairwise_cons.mp h
    have hsk : ∀ y ∈ xs, x ≤ y := fun y hy => (hx y hy).le
    simp [runRow, insertRow, runRow_skip (r := []) hsk, ih hs]

theorem runRow_bumped_sublist {xs r : List ℕ} (hs : xs.Pairwise (· < ·)) :
    (runRow xs r).2 <+ r := by
  induction r generalizing xs with
  | nil => simp [runRow_empty hs]
  | cons y ys ih =>
    cases xs with
    | nil => simp [runRow]
    | cons x xs =>
      obtain ⟨hx, hxs⟩ := List.pairwise_cons.mp hs
      by_cases hxy : x < y
      · have hsk : ∀ u ∈ xs, x ≤ u := fun u hu => (hx u hu).le
        simpa [runRow, insertRow, hxy, runRow_skip (r := ys) hsk] using (ih hxs).cons_cons y
      · have hsk : ∀ u ∈ x :: xs, y ≤ u := by
          intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · omega
          · exact (Nat.le_of_not_gt hxy).trans (hx a ha).le
        simpa [runRow_skip (r := ys) hsk] using (ih hs).cons y

theorem runRow_input_mem {xs r : List ℕ} (hs : xs.Pairwise (· < ·)) {z : ℕ} (hz : z ∈ xs) :
    z ∈ (runRow xs r).1 := by
  induction r generalizing xs with
  | nil => simpa [runRow_empty hs] using hz
  | cons y ys ih =>
    cases xs with
    | nil => simp at hz
    | cons x xs =>
      obtain ⟨hx, hxs⟩ := List.pairwise_cons.mp hs
      by_cases hxy : x < y
      · have hsk : ∀ u ∈ xs, x ≤ u := fun u hu => (hx u hu).le
        rw [runRow, insertRow, ite_eq_left hxy, runRow_skip hsk]
        exact List.mem_cons.mpr ((List.mem_cons.mp hz).imp_right (ih hxs))
      · have hsk : ∀ u ∈ x :: xs, y ≤ u := by
          intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · omega
          · exact (Nat.le_of_not_gt hxy).trans (hx a ha).le
        rw [runRow_skip hsk]
        exact List.mem_cons_of_mem y (ih hs hz)

theorem runRow_old_mem {xs r : List ℕ} {z : ℕ} (hz : z ∈ r) :
    z ∈ (runRow xs r).1 ∨ z ∈ (runRow xs r).2 := by
  induction xs generalizing r with
  | nil => exact Or.inl hz
  | cons x xs ih =>
    have he := (insertRow_perm x r).mem_iff.mpr (List.mem_cons_of_mem x hz)
    rcases List.mem_append.mp he with he | he
    · exact Or.inr (List.mem_append_left _ he)
    · exact (ih he).imp_right (List.mem_append_right _)

theorem insertWord_cons (xs r : List ℕ) (rs : Tableau) :
    insertWord (r :: rs) xs = (runRow xs r).1 :: insertWord rs (runRow xs r).2 := by
  induction xs generalizing r rs with
  | nil => rfl
  | cons x xs ih =>
    change insertWord (insert x (r :: rs)) xs = _
    cases hb : (insertRow x r).2 with
    | none => simpa [insert, hb, runRow] using ih (insertRow x r).1 rs
    | some y =>
      have he := ih (insertRow x r).1 (insert y rs)
      simpa [insert, hb, runRow, insertWord] using he

theorem insertWord_empty {xs : List ℕ} (hs : xs.Pairwise (· < ·)) :
    insertWord [] xs = if xs.isEmpty then [] else [xs] := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    change insertWord [[x]] xs = [x :: xs]
    obtain ⟨hx, hxs⟩ := List.pairwise_cons.mp hs
    have hsk : ∀ u ∈ xs, x ≤ u := fun u hu => (hx u hu).le
    rw [insertWord_cons, runRow_skip hsk, runRow_empty hxs]
    rfl

theorem input_mem_firstRow {xs : List ℕ} {T : Tableau} (hs : xs.Pairwise (· < ·)) {x : ℕ}
    (hx : x ∈ xs) : x ∈ rowAt (insertWord T xs) 0 := by
  cases T with
  | nil =>
    cases xs with
    | nil => simp at hx
    | cons a xs => simpa [insertWord_empty hs] using hx
  | cons r rs =>
    rw [insertWord_cons, rowAt_cons_zero]
    exact runRow_input_mem hs hx

theorem old_mem_row_or_next_of_block {T : Tableau} {xs : List ℕ} {x j : ℕ}
    (hv : Valid T) (hs : xs.Pairwise (· < ·)) (hx : x ∈ rowAt T j) :
    x ∈ rowAt (insertWord T xs) j ∨ x ∈ rowAt (insertWord T xs) (j + 1) := by
  induction T generalizing xs j with
  | nil => simp at hx
  | cons r rs ih =>
    have hsort := hv.2.1.sublist (runRow_bumped_sublist (r := r) hs)
    rw [insertWord_cons]
    cases j with
    | zero =>
      rcases runRow_old_mem (xs := xs) (show x ∈ r from hx) with h | h
      · exact Or.inl h
      · exact Or.inr (input_mem_firstRow hsort h)
    | succ j => exact ih hv.2.2.2 hsort hx

#print axioms input_mem_firstRow
#print axioms old_mem_row_or_next_of_block


theorem mem_row_after_blocks {T : Tableau} {blocks : List (List ℕ)} {x j : ℕ}
    (hv : Valid T) (hn : (blocks.flatten.reverse ++ T.flatten).Nodup)
    (hs : ∀ r ∈ blocks, List.Pairwise (· < ·) r)
    (hx : x ∈ rowAt T j) :
    ∃ q ≤ j + blocks.length, x ∈ rowAt (insertWord T blocks.flatten) q := by
  induction blocks generalizing T j with
  | nil => exact ⟨j, Nat.le_refl _, hx⟩
  | cons b bs ih =>
    have hn' : (bs.flatten.reverse ++ (b.reverse ++ T.flatten)).Nodup := by
      simpa [List.reverse_append, List.append_assoc] using hn
    have hv' := valid_foldInsert hv (List.nodup_append.mp hn').2.1
    have hn'' := ((foldInsert_perm T b).append_left bs.flatten.reverse).nodup_iff.mpr hn'
    have hs' : ∀ r ∈ bs, r.Pairwise (· < ·) := fun r hr => hs r (List.mem_cons_of_mem _ hr)
    have he : insertWord T (b :: bs).flatten = insertWord (insertWord T b) bs.flatten := by
      simp [insertWord, List.foldl_append]
    rw [he]
    rcases old_mem_row_or_next_of_block hv (hs b List.mem_cons_self) hx with h | h
    · obtain ⟨q, hq, hmem⟩ := ih hv' hn'' hs' h
      exact ⟨q, by simp; omega, hmem⟩
    · obtain ⟨q, hq, hmem⟩ := ih hv' hn'' hs' h
      exact ⟨q, by simp; omega, hmem⟩

/-- An entry begins in the first row of its own increasing block and moves
down at most one row per subsequent block. -/
theorem lastCopy_row_bound {n k : ℕ} (w : Equiv.Perm (Fin n)) (hk : 0 < k) (i : Fin n) :
    ∃ j ≤ n - 1 - i.val, lastCopy w k i ∈ rowAt (insertionTableau (kFoldWord w k)) j := by
  let indices := List.finRange n
  let p := (indices.take i.val).flatMap (fun j => block w j k)
  let bs := (indices.drop (i.val + 1)).map (fun j => block w j k)
  have hi : i.val < indices.length := by simp [indices]
  have hsplit : indices = indices.take i.val ++ i :: indices.drop (i.val + 1) := by
    have he := List.drop_eq_getElem_cons hi
    have hval : indices[i.val] = i := by simp [indices]
    exact (List.take_append_drop i.val indices).symm.trans (by rw [he, hval])
  have hw : kFoldWord w k = p ++ block w i k ++ bs.flatten := by
    change indices.flatMap _ = _
    conv => lhs; rw [hsplit]
    simp [p, bs, List.append_assoc, List.flatMap]
  have hn := kFoldWord_nodup w k
  rw [hw] at hn
  have hpb := (List.nodup_append.mp hn).1
  let T := insertionTableau (p ++ block w i k)
  have hv := valid_insertionTableau hpb
  have hB : T = insertWord (insertionTableau p) (block w i k) := by
    simp [T, insertWord, insertionTableau, List.foldl_append]
  have hmem : lastCopy w k i ∈ block w i k :=
    List.mem_map.mpr ⟨k - 1, List.mem_range.mpr (by omega), rfl⟩
  have hfirst : lastCopy w k i ∈ rowAt T 0 := by
    rw [hB]
    exact input_mem_firstRow (block_sorted w i k) hmem
  have hnd : (bs.flatten.reverse ++ T.flatten).Nodup := by
    have hrev := (List.reverse_perm bs.flatten).append_right T.flatten
    apply hrev.nodup_iff.mpr
    apply ((insertionTableau_perm (p ++ block w i k)).append_left bs.flatten).nodup_iff.mpr
    exact List.perm_append_comm.nodup_iff.mpr hn
  have hs : ∀ r ∈ bs, r.Pairwise (· < ·) := by
    intro r hr
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hr
    exact block_sorted w a k
  obtain ⟨j, hj, h⟩ := mem_row_after_blocks hv hnd hs hfirst
  have hlen : bs.length = n - 1 - i.val := by
    simp [bs, indices]
    omega
  refine ⟨j, by simpa [hlen] using hj, ?_⟩
  rwa [show insertionTableau (kFoldWord w k) = insertWord T bs.flatten by
    simp [hw, T, insertionTableau, insertWord, List.foldl_append]]

private theorem fin_eq_of_injective_le {n : ℕ} {f : Fin n → Fin n}
    (hi : Function.Injective f) (hl : ∀ i, (f i).val ≤ i.val) (i : Fin n) :
    f i = i := by
  generalize e : i.val = m
  induction m using Nat.strong_induction_on generalizing i with
  | h m ih =>
    by_contra hne
    have hlt : (f i).val < m := by
      have hval := hl i
      exact Nat.lt_of_le_of_ne (e ▸ hval) (fun h => hne (Fin.ext (h.trans e.symm)))
    have hf := ih (f i).val hlt (f i) rfl
    exact hne (hi hf)

theorem stabilizesAt_of_growsOne {n k : ℕ} (w : Equiv.Perm (Fin n))
    (h : growsOne w k) : stabilizesAt w (k + 1) := by
  classical
  let T := insertionTableau (kFoldWord w (k + 1))
  let bound (i : Fin n) : ℕ := n - 1 - i.val
  let ex := fun i : Fin n => lastCopy_row_bound w (Nat.succ_pos k) i
  let f (i : Fin n) : Fin n :=
    ⟨(ex i).choose, by have h₁ := (ex i).choose_spec.1; dsimp [bound] at *; have := i.isLt; omega⟩
  have hf (i : Fin n) : (f i).val ≤ bound i ∧ lastCopy w (k + 1) i ∈ rowAt T (f i).val :=
    (ex i).choose_spec
  have hcount (j : Fin n) :
      ((rowAt T j.val).filter (fun a => !small (k * n) a)).length = 1 := by
    have ht := List.length_eq_length_filter_add (l := rowAt T j.val) (small (k * n))
    have hr := kFoldWord_row_restriction w k j.val
    have hg := h j.val j.isLt
    rw [hr] at ht
    unfold rowLength at hg
    exact Nat.add_left_cancel (ht.symm.trans hg)
  have hinj : Function.Injective f := by
    intro i j he
    let l := (rowAt T (f j).val).filter (fun a => !small (k * n) a)
    have hi : lastCopy w (k + 1) i ∈ l := (high_mem_iff w).mpr
      ⟨i, rfl, he ▸ (hf i).2⟩
    have hj : lastCopy w (k + 1) j ∈ l := (high_mem_iff w).mpr ⟨j, rfl, (hf j).2⟩
    have hlen : l.length = 1 := hcount (f j)
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen
    rw [hx, List.mem_singleton] at hi hj
    exact (letter_injective w (hi.trans hj.symm)).1
  let rev (i : Fin n) : Fin n := ⟨bound i, by have := i.isLt; dsimp [bound]; omega⟩
  have hrev (i : Fin n) : rev (rev i) = i := by
    apply Fin.ext
    have := i.isLt
    dsimp [rev, bound]
    omega
  have hri : Function.Injective rev := (show Function.Involutive rev from hrev).injective
  have hf_rev (i : Fin n) : f (rev i) = i := by
    apply fin_eq_of_injective_le (hinj.comp hri) _
    intro j
    have hle := (hf (rev j)).1
    change (f (rev j)).val ≤ (rev (rev j)).val at hle
    simpa [hrev j] using hle
  refine ⟨Nat.succ_pos k, ?_⟩
  intro i
  have he : f i = rev i := by simpa [hrev i] using hf_rev (rev i)
  have hm := (hf i).2
  rw [he] at hm
  have hn := (insertionTableau_perm _).nodup_iff.mpr (kFoldWord_nodup w (k + 1))
  exact (rowOf_eq_some_iff hn).mpr hm

theorem stabilizesAt_iff_growsOne {n k : ℕ} (w : Equiv.Perm (Fin n)) :
    stabilizesAt w (k + 1) ↔ growsOne w k :=
  ⟨growsOne_of_stabilizesAt w, stabilizesAt_of_growsOne w⟩

#print axioms lastCopy_row_bound
#print axioms stabilizesAt_iff_growsOne

end TableauStabilization
```

### `StabLevels.lean`

```lean
import StabBlock
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Preorder.Finite

set_option autoImplicit false

namespace TableauStabilization

def ascStep {n : ℕ} (w : Equiv.Perm (Fin n)) (i : ℕ) : ℕ :=
    if hi : i + 1 < n then
      if w ⟨i, by omega⟩ < w ⟨i + 1, hi⟩ then 1 else 0
    else 0

def ascPrefix {n : ℕ} (w : Equiv.Perm (Fin n)) : ℕ → ℕ
  | 0 => 0
  | i + 1 => ascPrefix w i + ascStep w i

def ascents {n : ℕ} (w : Equiv.Perm (Fin n)) : ℕ := ascPrefix w (n - 1)

theorem ascStep_le_one {n : ℕ} (w : Equiv.Perm (Fin n)) (i : ℕ) : ascStep w i ≤ 1 := by
  unfold ascStep
  split
  · split <;> omega
  · omega

theorem ascStep_eq_one_iff {n i : ℕ} (w : Equiv.Perm (Fin n)) (hi : i + 1 < n) :
    ascStep w i = 1 ↔ w ⟨i, by omega⟩ < w ⟨i + 1, hi⟩ := by simp [ascStep, hi]

theorem ascStep_eq_zero_iff {n i : ℕ} (w : Equiv.Perm (Fin n)) (hi : i + 1 < n) :
    ascStep w i = 0 ↔ w ⟨i + 1, hi⟩ < w ⟨i, by omega⟩ := by
  have hne : w ⟨i, by omega⟩ ≠ w ⟨i + 1, hi⟩ := by
    intro h
    have he := congrArg Fin.val (w.injective h)
    simp at he
  have hiff := ascStep_eq_one_iff w hi
  have hh := ascStep_le_one w i
  constructor
  · intro hz
    exact lt_of_le_of_ne (le_of_not_gt (fun hs => by omega)) hne.symm
  · intro hs
    have hnot := not_lt_of_ge hs.le
    omega

theorem ascPrefix_mono {n : ℕ} (w : Equiv.Perm (Fin n)) : Monotone (ascPrefix w) :=
  monotone_nat_of_le_succ fun i => Nat.le_add_right (ascPrefix w i) (ascStep w i)

theorem ascPrefix_le_index {n : ℕ} (w : Equiv.Perm (Fin n)) (i : ℕ) :
    ascPrefix w i ≤ i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [ascPrefix]
    have hl := ascStep_le_one w i
    omega

theorem ascPrefix_difference_le {n : ℕ} (w : Equiv.Perm (Fin n)) {i j : ℕ} (h : i ≤ j) :
    ascPrefix w j - ascPrefix w i ≤ j - i := by
  induction j with
  | zero => simp [ascPrefix]
  | succ j ih =>
    by_cases hi : i ≤ j
    · have hm := ascPrefix_mono w hi
      have h₁ := ih hi
      have h₂ := ascStep_le_one w j
      rw [ascPrefix]
      omega
    · have he : i = j + 1 := by omega
      simp [he]

theorem ascents_le {n : ℕ} (w : Equiv.Perm (Fin n)) : ascents w ≤ n - 1 :=
  ascPrefix_le_index w (n - 1)

theorem ascents_eq_max_iff {n : ℕ} (w : Equiv.Perm (Fin n)) :
    ascents w = n - 1 ↔ w = 1 := by
  constructor
  · intro h
    have hstep (i : Fin (n - 1)) : w ⟨i.val, by have := i.isLt; omega⟩ <
        w ⟨i.val + 1, by have := i.isLt; omega⟩ := by
      have hi := i.isLt
      have hb := ascPrefix_le_index w i.val
      have hdiff := ascPrefix_difference_le w (i := i.val + 1) (j := n - 1) (by omega)
      have hmax := ascStep_le_one w i.val
      change ascPrefix w (n - 1) = n - 1 at h
      rw [ascPrefix] at hdiff
      apply (ascStep_eq_one_iff w (by omega)).mp
      omega
    cases n with
    | zero => exact Subsingleton.elim _ _
    | succ n =>
      have hm : StrictMono w := Fin.strictMono_iff_lt_succ.mpr fun i => hstep i
      apply Equiv.ext
      intro i
      exact congrFun hm.eq_id i
  · rintro rfl
    unfold ascents
    have hpre (i : ℕ) (hi : i ≤ n - 1) : ascPrefix (1 : Equiv.Perm (Fin n)) i = i := by
      induction i with
      | zero => rfl
      | succ i ih =>
        have he : ascStep (1 : Equiv.Perm (Fin n)) i = 1 :=
          (ascStep_eq_one_iff _ (by omega)).mpr (by change i < i + 1; omega)
        rw [ascPrefix, ih (by omega), he]
    exact hpre (n - 1) (Nat.le_refl _)

theorem ascents_le_of_ne_one {n : ℕ} (w : Equiv.Perm (Fin n)) (h : w ≠ 1) :
    ascents w ≤ n - 2 := by
  have hb := ascents_le w
  have hne : ascents w ≠ n - 1 := fun he => h ((ascents_eq_max_iff w).mp he)
  omega

theorem desc_of_prefix_eq {n : ℕ} (w : Equiv.Perm (Fin n)) {i j : Fin n}
    (hij : i < j) (he : ascPrefix w i.val = ascPrefix w j.val) :
    w j < w i := by
  obtain ⟨j, hj⟩ := j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    have hi : i.val < j := hij
    let u : Fin n := ⟨j - 1, by omega⟩
    have hu : u.val + 1 = j := by dsimp [u]; omega
    have hp : ascPrefix w j = ascPrefix w u.val + ascStep w u.val := by
      conv => lhs; rw [← hu, ascPrefix]
    have hmono := ascPrefix_mono w (show i.val ≤ u.val by dsimp [u]; omega)
    have hz : ascStep w u.val = 0 := by change ascPrefix w i.val = ascPrefix w j at he; omega
    have hlast := (ascStep_eq_zero_iff w (by omega : u.val + 1 < n)).mp hz
    have hlast' : w ⟨j, hj⟩ < w u := by
      simpa only [Fin.mk.injEq, hu] using hlast
    by_cases h : i = u
    · simpa [h] using hlast'
    · have hlt : i.val < u.val := Nat.lt_of_le_of_ne (by dsimp [u]; omega)
        (fun e => h (Fin.ext e))
      have he' : ascPrefix w i.val = ascPrefix w u.val := by
        change ascPrefix w i.val = ascPrefix w j at he
        omega
      exact hlast'.trans (ih u.val (by omega) u.isLt hlt he')

def level {n k : ℕ} (w : Equiv.Perm (Fin n)) (a : Cell n k) : ℕ :=
    a.2.val + ascPrefix w a.1.val

theorem level_decreases {n k : ℕ} (w : Equiv.Perm (Fin n)) {a b : Cell n k}
    (hab : before a b) (he : level w a = level w b) : value w b < value w a := by
  unfold level at he
  have hr : a.1 < b.1 := by
    rcases hab with h | ⟨eq, hc⟩
    · exact h
    · rw [eq] at he
      change a.2.val < b.2.val at hc
      omega
  have hm := ascPrefix_mono w (show a.1.val ≤ b.1.val from hr.le)
  unfold value
  apply (letter_lt_iff w b.1 a.1 b.2.val a.2.val).mpr
  by_cases hs : ascPrefix w a.1.val = ascPrefix w b.1.val
  · exact Or.inr ⟨by omega, desc_of_prefix_eq w hr hs⟩
  · exact Or.inl (by omega)

#print axioms ascents_eq_max_iff
#print axioms ascents_le_of_ne_one
#print axioms level_decreases

end TableauStabilization
```

### `StabDeletion.lean`

```lean
import StabLevels

set_option autoImplicit false

namespace TableauStabilization

open scoped List

def descentLink {n k : ℕ} (w : Equiv.Perm (Fin n)) (a b : Cell n k) : Prop :=
  before a b ∧ value w b < value w a

theorem before_trans {n k : ℕ} {a b c : Cell n k}
    (hab : before a b) (hbc : before b c) : before a c := by
  rcases hab with h | ⟨he, hc⟩ <;> rcases hbc with h' | ⟨he', hc'⟩
  · exact Or.inl (h.trans h')
  · exact Or.inl (he' ▸ h)
  · exact Or.inl (he.symm ▸ h')
  · exact Or.inr ⟨he.trans he', hc.trans hc'⟩

theorem descentLink_trans {n k : ℕ} {w : Equiv.Perm (Fin n)} {a b c : Cell n k}
    (hab : descentLink w a b) (hbc : descentLink w b c) : descentLink w a c :=
  ⟨before_trans hab.1 hbc.1, hbc.2.trans hab.2⟩

theorem descentLink_row_lt {n k : ℕ} {w : Equiv.Perm (Fin n)} {a b : Cell n k}
    (h : descentLink w a b) : a.1 < b.1 := by
  rcases h.1 with hs | ⟨_, hcol⟩
  · exact hs
  · exact (Nat.lt_asymm (letter_lt_of_copy_lt (w := w) (i := a.1) (j := b.1) hcol) h.2).elim

def kept {n k : ℕ} (w : Equiv.Perm (Fin n)) (a : Cell n k) : Prop :=
  a.1.val ≠ 0 ∨ a.2.val < ascents w

private theorem kept_chain_len_le {n k : ℕ} {w : Equiv.Perm (Fin n)}
    (hn : 0 < n) {s : List (Cell n k)} (hs : s.Pairwise (descentLink w))
    (hkept : ∀ a ∈ s, kept w a) : s.length ≤ n - 1 := by
  have hsorted : (s.map Prod.fst).Pairwise (· < ·) :=
    List.pairwise_map.mpr (hs.imp descentLink_row_lt)
  have hlen : s.length ≤ n := by
    have hnd : (s.map Prod.fst).Nodup := hsorted.imp ne_of_lt
    have ht := hnd.length_le_of_subset (l₂ := List.finRange n) (fun _ _ => List.mem_finRange _)
    simpa using ht
  by_contra! hg
  have he : s.length = n := by omega
  let row (j : Fin n) : Fin n := (s[j.val]'(he.symm ▸ j.isLt)).1
  have hmono : StrictMono row := by
    intro i j hij
    exact descentLink_row_lt (hs.rel_getElem_of_lt (he.symm ▸ i.isLt) (he.symm ▸ j.isLt) hij)
  have hrow (j : Fin n) : (s[j.val]'(he.symm ▸ j.isLt)).1 = j := congrFun hmono.eq_id j
  let col (i : ℕ) : ℕ := (s[i]?.map (fun a => a.2.val)).getD 0
  have hcol (i : ℕ) (hi : i < n) : col i = (s[i]'(he.symm ▸ hi)).2.val := by
    unfold col
    rw [List.getElem?_eq_getElem]
    rfl
  have hstep (i : ℕ) (hi : i + 1 < n) : col (i + 1) + ascStep w i ≤ col i := by
    have hi' : i < n := by omega
    let a := s[i]'(he.symm ▸ hi')
    let b := s[i + 1]'(he.symm ▸ hi)
    have hs' : descentLink w a b := hs.rel_getElem_of_lt (he.symm ▸ hi') (he.symm ▸ hi) (by omega)
    have ha : a.1 = ⟨i, hi'⟩ := hrow ⟨i, hi'⟩
    have hb : b.1 = ⟨i + 1, hi⟩ := hrow ⟨i + 1, hi⟩
    have hval := (letter_lt_iff w b.1 a.1 b.2.val a.2.val).mp hs'.2
    rw [hcol _ hi', hcol _ hi]
    change b.2.val + ascStep w i ≤ a.2.val
    rcases hval with hl | ⟨hc, hv⟩
    · have hb := ascStep_le_one w i
      omega
    · have hzero := (ascStep_eq_zero_iff w hi).mpr (by simpa [ha, hb] using hv)
      omega
  have hbound (j : ℕ) (hj : j < n) : col j + ascPrefix w j ≤ col 0 := by
    induction j with
    | zero => simp [ascPrefix]
    | succ j ih =>
      have hs' := hstep j hj
      have hm := ih (by omega)
      rw [ascPrefix]
      omega
  have htop : col 0 < ascents w := by
    have hc := hkept (s[0]'(he.symm ▸ hn)) (List.getElem_mem _)
    change (s[0]'(he.symm ▸ hn)).1.val ≠ 0 ∨ (s[0]'(he.symm ▸ hn)).2.val < ascents w at hc
    rw [hrow ⟨0, hn⟩, ← hcol 0 hn] at hc
    exact hc.resolve_left (fun h => h rfl)
  have hbot := hbound (n - 1) (by omega)
  unfold ascents at htop
  omega

/-- A decreasing chain ending at a retained cell. -/
def EndsAt {n k : ℕ} (w : Equiv.Perm (Fin n)) (p : Cell n k) (m : ℕ) : Prop :=
  ∃ s : List (Cell n k), s.length = m + 1 ∧
    s.Pairwise (descentLink w) ∧ (∀ c ∈ s, kept w c) ∧ s.getLast? = some p

private theorem ends_single {n k : ℕ} {w : Equiv.Perm (Fin n)} {p : Cell n k}
    (hp : kept w p) : EndsAt w p 0 :=
  ⟨[p], rfl, by simp, by simpa using hp, rfl⟩

private theorem ends_succ {n k m : ℕ} {w : Equiv.Perm (Fin n)} {p q : Cell n k}
    (h : EndsAt w p m) (hpq : descentLink w p q) (hq : kept w q) : EndsAt w q (m + 1) := by
  obtain ⟨s, hl, hs, hS, he⟩ := h
  have hne : s ≠ [] := fun hn => by simp [hn] at he
  have hget : s.getLast hne = p := by
    apply Option.some.inj
    simpa [List.getLast?_eq_some_getLast hne] using he
  refine ⟨s ++ [q], by simp [hl], ?_, ?_, by simp⟩
  · rw [List.pairwise_append]
    refine ⟨hs, by simp, ?_⟩
    intro a ha b hb
    have hb' := List.mem_singleton.mp hb
    subst b
    rw [← List.dropLast_append_getLast hne, hget] at ha hs
    rcases List.mem_append.mp ha with ha | ha
    · exact descentLink_trans (hs.rel_of_mem_append ha (by simp)) hpq
    · have ha' := List.mem_singleton.mp ha
      simpa [ha'] using hpq
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hS _ ha
    · simpa [List.mem_singleton.mp ha] using hq

noncomputable def label {n k : ℕ} (w : Equiv.Perm (Fin n)) (p : Cell n k) : ℕ :=
    open Classical in Nat.findGreatest (EndsAt w p) (n - 1)

private theorem label_spec {n k : ℕ} {w : Equiv.Perm (Fin n)} {p : Cell n k}
    (hp : kept w p) : EndsAt w p (label w p) := by
  classical
  exact Nat.findGreatest_spec (Nat.zero_le _) (ends_single hp)

private theorem label_lt {n k : ℕ} {w : Equiv.Perm (Fin n)} {p : Cell n k}
    (hn : 0 < n) (hp : kept w p) : label w p < n - 1 := by
  obtain ⟨s, hl, hs, hS, _⟩ := label_spec hp
  have h := kept_chain_len_le hn hs hS
  omega

private theorem label_lt_of_desc {n k : ℕ} {w : Equiv.Perm (Fin n)} {p q : Cell n k}
    (hn : 0 < n) (hp : kept w p) (hq : kept w q) (h : descentLink w p q) :
    label w p < label w q := by
  classical
  exact Nat.le_findGreatest (show label w p + 1 ≤ n - 1 from label_lt hn hp)
    (ends_succ (label_spec hp) h hq)

theorem deletion_cover {n k : ℕ} (w : Equiv.Perm (Fin n)) (hn : 0 < n) :
    Attains (· < ·) (n - 1) (kFoldWord w k)
      ((cells n k).filter (fun a => open Classical in decide (kept w a))).length := by
  classical
  let f : Cell n k → Option (Fin (n - 1)) :=
    fun a => if h : kept w a then some ⟨label w a, label_lt hn h⟩ else none
  have hcolor (a : Cell n k) (c : Fin (n - 1)) (h : f a = some c) :
      kept w a ∧ label w a = c.val := by
    by_cases ha : kept w a
    · have he : (⟨label w a, label_lt hn ha⟩ : Fin (n - 1)) = c := by simpa [f, ha] using h
      exact ⟨ha, congrArg Fin.val he⟩
    · simp [f, ha] at h
  have h := attains_grid (w := w) f (by
    intro a b hab c ha hb
    obtain ⟨hka, hla⟩ := hcolor a c ha
    obtain ⟨hkb, hlb⟩ := hcolor b c hb
    rcases lt_trichotomy (value w a) (value w b) with he | he | he
    · exact he
    · have e := value_injective w he
      subst b
      exact (before_asymm hab hab).elim
    · have hlt := label_lt_of_desc hn hka hkb ⟨hab, he⟩
      omega)
  have he : (fun a => (f a).isSome) = (fun a => decide (kept w a)) := by
    funext a
    by_cases ha : kept w a <;> simp [f, ha]
  simpa only [he] using h

#print axioms deletion_cover

end TableauStabilization
```

### `StabUpper.lean`

```lean
import StabDeletion
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fintype.Prod
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false

namespace TableauStabilization

open Finset
open scoped BigOperators

theorem filtered_cells_card {n k : ℕ} (p : Cell n k → Prop) [DecidablePred p] :
    ((cells n k).filter (fun a => decide (p a))).length = (univ.filter p).card := by
  have hn : (cells n k).Nodup := List.Nodup.of_map (value (1 : Equiv.Perm (Fin n)))
    (kFoldWord_eq_grid (1 : Equiv.Perm (Fin n)) k ▸ kFoldWord_nodup _ k)
  have hset : (cells n k).toFinset = univ := by ext a; simp [mem_cells]
  rw [← List.toFinset_card_of_nodup (hn.filter (fun a => decide (p a))), List.toFinset_filter, hset]
  simp

def levelRows {n : ℕ} (w : Equiv.Perm (Fin n)) (k ell : ℕ) : Finset ℕ :=
    (range n).filter (fun i => ascPrefix w i ≤ ell ∧ ell < ascPrefix w i + k)

def discard {n k : ℕ} (w : Equiv.Perm (Fin n)) (t : ℕ) (a : Cell n k) : Prop :=
    a.1.val + t < n ∧ ascPrefix w (a.1.val + t) - ascPrefix w a.1.val ≤ a.2.val

instance {n k : ℕ} (w : Equiv.Perm (Fin n)) (t : ℕ) : DecidablePred (discard (k := k) w t) :=
    fun _a => inferInstanceAs (Decidable (_ ∧ _))

private theorem levelRows_interval {n : ℕ} (w : Equiv.Perm (Fin n)) (k ell : ℕ)
    (h : (levelRows w k ell).Nonempty) :
    ∃ lo hi, lo ≤ hi ∧ levelRows w k ell = Icc lo hi := by
  let s := levelRows w k ell
  let lo := s.min' h
  let hi := s.max' h
  have hlo : lo ∈ s := min'_mem s h
  have hhi : hi ∈ s := max'_mem s h
  refine ⟨lo, hi, min'_le s _ hhi, ?_⟩
  ext i
  constructor
  · intro hi'
    exact mem_Icc.mpr ⟨min'_le s _ hi', le_max' s _ hi'⟩
  · intro hi'
    obtain ⟨hli, hih⟩ := mem_Icc.mp hi'
    have hlo' : lo < n ∧ ascPrefix w lo ≤ ell ∧ ell < ascPrefix w lo + k := by
      simpa [s, levelRows] using hlo
    have hhi' : hi < n ∧ ascPrefix w hi ≤ ell ∧ ell < ascPrefix w hi + k := by
      simpa [s, levelRows] using hhi
    simp only [levelRows, mem_filter, mem_range]
    exact ⟨hih.trans_lt hhi'.1, (ascPrefix_mono w hih).trans hhi'.2.1,
      hlo'.2.2.trans_le (Nat.add_le_add_right (ascPrefix_mono w hli) k)⟩

private theorem row_mem_levelRows {n k : ℕ} {w : Equiv.Perm (Fin n)} {a : Cell n k}
    {ell : ℕ} (h : level w a = ell) : a.1.val ∈ levelRows w k ell := by
  simp only [levelRows, mem_filter, mem_range]
  have hi := a.1.isLt
  have hc := a.2.isLt
  unfold level at h
  exact ⟨hi, by omega, by omega⟩

private theorem discard_iff_levelRows {n k : ℕ} {w : Equiv.Perm (Fin n)} {a : Cell n k}
    {t ell : ℕ} (h : level w a = ell) : discard w t a ↔ a.1.val + t ∈ levelRows w k ell := by
  have hs := ascPrefix_mono w (Nat.le_add_right a.1.val t)
  have hk := a.2.isLt
  simp only [discard, levelRows, mem_filter, mem_range]
  unfold level at h
  omega

private theorem fiber_card {n k : ℕ} (w : Equiv.Perm (Fin n)) (ell : ℕ)
    (p : ℕ → Prop) [DecidablePred p] :
    ((univ : Finset (Cell n k)).filter (fun a => level w a = ell ∧ p a.1.val)).card =
      ((levelRows w k ell).filter p).card := by
  apply card_bij (fun a _ => a.1.val)
  · intro a ha
    have h := (mem_filter.mp ha).2
    exact mem_filter.mpr ⟨row_mem_levelRows h.1, h.2⟩
  · intro a ha b hb h
    have ea := (mem_filter.mp ha).2.1
    have eb := (mem_filter.mp hb).2.1
    unfold level at ea eb
    refine Prod.ext (Fin.ext h) (Fin.ext ?_)
    rw [h] at ea
    omega
  · intro i hi
    have hp := (mem_filter.mp hi).2
    have h := (mem_filter.mp (mem_filter.mp hi).1)
    have hn := mem_range.mp h.1
    let a : Cell n k := (⟨i, hn⟩, ⟨ell - ascPrefix w i, by obtain ⟨_, hlt⟩ := h.2; omega⟩)
    have he : level w a = ell := by
      change (ell - ascPrefix w i) + ascPrefix w i = ell
      have := h.2.1
      omega
    exact ⟨a, mem_filter.mpr ⟨mem_univ _, he, hp⟩, rfl⟩

private theorem level_keep_card {n k : ℕ} (w : Equiv.Perm (Fin n)) (t ell : ℕ) :
    ((univ : Finset (Cell n k)).filter (fun a => level w a = ell ∧ ¬ discard w t a)).card =
      min t ((univ : Finset (Cell n k)).filter (fun a => level w a = ell)).card := by
  classical
  have hAll : ((univ : Finset (Cell n k)).filter (fun a => level w a = ell)).card =
      (levelRows w k ell).card := by
    simpa using fiber_card (k := k) w ell (fun _ => True)
  have heq : (univ : Finset (Cell n k)).filter (fun a => level w a = ell ∧ ¬ discard w t a) =
      univ.filter (fun a => level w a = ell ∧ a.1.val + t ∉ levelRows w k ell) := by
    ext a
    simp only [mem_filter, mem_univ, true_and]
    constructor <;> rintro ⟨h, hn⟩ <;> exact ⟨h, by simpa only [discard_iff_levelRows h] using hn⟩
  rw [heq, fiber_card w ell (fun i => i + t ∉ levelRows w k ell), hAll]
  by_cases h : (levelRows w k ell).Nonempty
  · obtain ⟨lo, hi, hle, hs⟩ := levelRows_interval w k ell h
    have htail : (Icc lo hi).filter (fun i => i + t ∉ Icc lo hi) = Icc (max lo (hi + 1 - t)) hi := by
      ext i
      simp only [mem_filter, mem_Icc, max_le_iff]
      omega
    simp only [hs, htail, Nat.card_Icc]
    omega
  · simp [not_nonempty_iff_eq_empty.mp h]

private theorem same_level_color_ne {n k t : ℕ} (w : Equiv.Perm (Fin n)) (f : Coloring t)
    (hf : (kFoldWord w k).Pairwise (Good (· < ·) f)) {a b : Cell n k}
    (hab : a ≠ b) (hl : level w a = level w b) :
    ∀ c, f (value w a) = some c → f (value w b) ≠ some c := by
  rw [kFoldWord_eq_grid, List.pairwise_map, cells_pairwise_iff] at hf
  have hb : before a b ∨ before b a := by
    rcases lt_trichotomy a.1 b.1 with h | h | h
    · exact Or.inl (Or.inl h)
    · rcases lt_trichotomy a.2 b.2 with e | e | e
      · exact Or.inl (Or.inr ⟨h, e⟩)
      · exact (hab (Prod.ext h e)).elim
      · exact Or.inr (Or.inr ⟨h.symm, e⟩)
    · exact Or.inr (Or.inl h)
  intro c ha hb'
  rcases hb with hb | hb
  · exact Nat.lt_asymm (hf a b hb c ha hb') (level_decreases w hb hl)
  · exact Nat.lt_asymm (hf b a hb c hb' ha) (level_decreases w hb hl.symm)

private theorem cover_le_keep {n k t : ℕ} {w : Equiv.Perm (Fin n)} {f : Coloring t}
    (hf : (kFoldWord w k).Pairwise (Good (· < ·) f)) :
    covered f (kFoldWord w k) ≤ ((univ : Finset (Cell n k)).filter (fun a => ¬ discard w t a)).card := by
  classical
  let used : Finset (Cell n k) := univ.filter (fun a => (f (value w a)).isSome)
  let keep : Finset (Cell n k) := univ.filter (fun a => ¬ discard w t a)
  have hcard : covered f (kFoldWord w k) = used.card := by
    rw [covered, kFoldWord_eq_grid, List.filter_map, List.length_map]
    have hdec (b : Bool) : decide (b = true) = b := by cases b <;> rfl
    simpa only [Function.comp_def, hdec] using
      filtered_cells_card (k := k) (fun a => (f (value w a)).isSome = true)
  let L := (univ : Finset (Cell n k)).image (level w)
  have e₁ := card_eq_sum_card_fiberwise (s := used) (t := L) (f := level w)
    (fun a _ => mem_image_of_mem _ (mem_univ a))
  have e₂ := card_eq_sum_card_fiberwise (s := keep) (t := L) (f := level w)
    (fun a _ => mem_image_of_mem _ (mem_univ a))
  change covered f (kFoldWord w k) ≤ keep.card
  rw [hcard, e₁, e₂]
  apply sum_le_sum
  intro ell _
  let U := used.filter (fun a => level w a = ell)
  have h₁ : U.card ≤ ((univ : Finset (Cell n k)).filter (fun a => level w a = ell)).card :=
    card_le_card (fun a ha => mem_filter.mpr ⟨mem_univ _, (mem_filter.mp ha).2⟩)
  have h₂ : U.card ≤ t := by
    let F (a : Cell n k) (ha : a ∈ U) : Fin t :=
      (f (value w a)).get (mem_filter.mp (mem_filter.mp ha).1).2
    have hF (a : Cell n k) (ha : a ∈ U) : f (value w a) = some (F a ha) :=
      (Option.some_get _).symm
    have hb : U.card ≤ (univ : Finset (Fin t)).card := by
      have he : U.attach.card ≤ (univ : Finset (Fin t)).card := by
        apply card_le_card_of_injOn (fun a : {a // a ∈ U} => F a.val a.property)
          (fun _ _ => mem_univ _)
        intro a _ b _ e
        apply Subtype.ext
        by_contra! hne
        have hl : level w a.val = level w b.val :=
          (mem_filter.mp a.property).2.trans (mem_filter.mp b.property).2.symm
        exact same_level_color_ne w f hf hne hl _ (hF a.val a.property)
          ((hF b.val b.property).trans (congrArg some e.symm))
      simpa using he
    simpa using hb
  have hk : keep.filter (fun a => level w a = ell) =
      univ.filter (fun a => level w a = ell ∧ ¬ discard w t a) := by
    ext a
    simp [keep, and_comm]
  rw [hk, level_keep_card]
  exact le_min h₂ h₁

def shapeBound {n : ℕ} (w : Equiv.Perm (Fin n)) (k t : ℕ) : ℕ :=
    t * k + ∑ i ∈ range (n - t), (ascPrefix w (i + t) - ascPrefix w i)

private theorem discard_row_card {n k : ℕ} (w : Equiv.Perm (Fin n)) (t i : ℕ) :
    ((univ : Finset (Cell n k)).filter (fun a => discard w t a ∧ a.1.val = i)).card =
      if i + t < n then k - (ascPrefix w (i + t) - ascPrefix w i) else 0 := by
  classical
  by_cases hi : i + t < n
  · rw [ite_eq_left hi, ← Nat.card_Ico]
    apply card_bij (fun a _ => a.2.val)
    · intro a ha
      have h := (mem_filter.mp ha).2
      exact mem_Ico.mpr ⟨h.2 ▸ h.1.2, a.2.isLt⟩
    · intro a ha b hb he
      have ea := (mem_filter.mp ha).2.2
      have eb := (mem_filter.mp hb).2.2
      exact Prod.ext (Fin.ext (ea.trans eb.symm)) (Fin.ext he)
    · intro c hc
      obtain ⟨hlo, hhi⟩ := mem_Ico.mp hc
      let a : Cell n k := (⟨i, by omega⟩, ⟨c, hhi⟩)
      exact ⟨a, mem_filter.mpr ⟨mem_univ _, ⟨hi, hlo⟩, rfl⟩, rfl⟩
  · rw [ite_eq_right hi]
    apply card_eq_zero.mpr
    ext a
    simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false]
    rintro ⟨h, e⟩
    exact hi (e ▸ h.1)

theorem discard_card {n k t : ℕ} (w : Equiv.Perm (Fin n))
    (hk : ascents w ≤ k) :
    ((univ : Finset (Cell n k)).filter (discard w t)).card =
      (n - t) * k - ∑ i ∈ range (n - t), (ascPrefix w (i + t) - ascPrefix w i) := by
  classical
  let s : Finset (Cell n k) := univ.filter (discard w t)
  have hs := card_eq_sum_card_fiberwise (s := s) (t := range (n - t)) (f := fun a => a.1.val)
    (fun a ha => mem_range.mpr (by
      change a.1.val < n - t
      have h := (mem_filter.mp ha).2.1
      omega))
  change s.card = _
  rw [hs]
  have hsum : (∑ i ∈ range (n - t), (s.filter (fun a => a.1.val = i)).card) =
      ∑ i ∈ range (n - t), (k - (ascPrefix w (i + t) - ascPrefix w i)) := by
    apply sum_congr rfl
    intro i hi
    have hif : i + t < n := by have := mem_range.mp hi; omega
    rw [show s.filter (fun a => a.1.val = i) =
      univ.filter (fun a => discard w t a ∧ a.1.val = i) by ext a; simp [s]]
    simp [discard_row_card, hif]
  rw [hsum, sum_tsub_distrib]
  · simp only [sum_const, card_range, Nat.nsmul_eq_mul]
  · intro i hi
    have hlt := mem_range.mp hi
    have hle := ascPrefix_mono w (show i + t ≤ n - 1 by omega)
    unfold ascents at hk
    omega

theorem keep_card {n k t : ℕ} (w : Equiv.Perm (Fin n)) (ht : t ≤ n) (hk : ascents w ≤ k) :
    ((univ : Finset (Cell n k)).filter (fun a => ¬ discard w t a)).card = shapeBound w k t := by
  have hsum := card_filter_add_card_filter_not (s := (univ : Finset (Cell n k))) (discard w t)
  have hm : n * k = t * k + (n - t) * k := by
    conv_lhs => rw [show n = t + (n - t) by omega]
    rw [Nat.add_mul]
  have hd := discard_card (t := t) w hk
  have hdiff : ∑ i ∈ range (n - t), (ascPrefix w (i + t) - ascPrefix w i) ≤ (n - t) * k := by
    calc
      _ ≤ ∑ _ ∈ range (n - t), k := sum_le_sum fun i hi => by
        have hlt := mem_range.mp hi
        have he := ascPrefix_mono w (show i + t ≤ n - 1 by omega)
        unfold ascents at hk
        omega
      _ = _ := by simp only [sum_const, card_range, Nat.nsmul_eq_mul]
  have htotal : (univ : Finset (Cell n k)).card = n * k := by
    rw [card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  rw [htotal] at hsum
  unfold shapeBound
  omega

theorem topSize_upper {n k t : ℕ} (w : Equiv.Perm (Fin n))
    (ht : t ≤ n) (hk : ascents w ≤ k) :
    topSize (insertionTableau (kFoldWord w k)) t ≤ shapeBound w k t := by
  obtain ⟨f, hf, he⟩ := (greene (kFoldWord_nodup w k) t).1
  rw [← he]
  have hle := cover_le_keep hf
  rwa [keep_card w ht hk] at hle

theorem shapeBound_route {n k t : ℕ} (w : Equiv.Perm (Fin n)) (ht : t ≤ n) :
    shapeBound w k t = t * k + ∑ j ∈ range t, (ascPrefix w (j + (n - t)) - ascPrefix w j) := by
  unfold shapeBound
  congr 1
  rw [sum_tsub_distrib, sum_tsub_distrib]
  · have h₁ := sum_range_add (ascPrefix w) t (n - t)
    have h₂ := sum_range_add (ascPrefix w) (n - t) t
    rw [show t + (n - t) = n by omega] at h₁
    rw [show n - t + t = n by omega] at h₂
    have hle₁ : (∑ i ∈ range (n - t), ascPrefix w i) ≤
        ∑ i ∈ range (n - t), ascPrefix w (i + t) :=
      sum_le_sum (fun i _ => ascPrefix_mono w (Nat.le_add_right i t))
    have hle₂ : (∑ i ∈ range t, ascPrefix w i) ≤
        ∑ i ∈ range t, ascPrefix w (i + (n - t)) :=
      sum_le_sum (fun i _ => ascPrefix_mono w (Nat.le_add_right i (n - t)))
    have e₁ : (∑ i ∈ range (n - t), ascPrefix w (t + i)) =
        ∑ i ∈ range (n - t), ascPrefix w (i + t) := by simp only [Nat.add_comm t]
    have e₂ : (∑ i ∈ range t, ascPrefix w ((n - t) + i)) =
        ∑ i ∈ range t, ascPrefix w (i + (n - t)) := by simp only [Nat.add_comm (n - t)]
    rw [e₁] at h₁
    rw [e₂] at h₂
    omega
  · exact fun j _ => ascPrefix_mono w (Nat.le_add_right j _)
  · exact fun j _ => ascPrefix_mono w (Nat.le_add_right j _)

theorem topSize_penultimate_lower {n k : ℕ} (w : Equiv.Perm (Fin n))
    (hn : 0 < n) (hk : ascents w ≤ k) :
    shapeBound w k (n - 1) ≤ topSize (insertionTableau (kFoldWord w k)) (n - 1) := by
  classical
  have h := deletion_cover w (k := k) hn
  rw [filtered_cells_card] at h
  have he : (univ : Finset (Cell n k)).filter (kept w) =
      univ.filter (fun a => ¬ discard w (n - 1) a) := by
    ext a
    simp only [mem_filter, mem_univ, true_and, kept, discard]
    by_cases ha : a.1.val = 0
    · simp [ha, ascPrefix, ascents]
      omega
    · simp [ha]
      omega
  rw [he, keep_card w (Nat.sub_le n 1) hk] at h
  exact (greene (kFoldWord_nodup w k) (n - 1)).2 _ h

#print axioms discard_card
#print axioms topSize_upper

end TableauStabilization
```

### `StabRoutes.lean`

```lean
import StabUpper
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false

namespace TableauStabilization

open Finset
open scoped BigOperators

/-- The boundary skips h−1, so the last change in a route has width two. -/
def routeCut (h u : ℕ) : ℕ := if u + 1 < h then u else h

private theorem routeCut_le (h u : ℕ) : routeCut h u ≤ h := by
  unfold routeCut
  split <;> omega

private theorem routeCut_mono (h : ℕ) : Monotone (routeCut h) := by
  intro a b hab
  unfold routeCut
  split <;> split <;> omega

private theorem routeCut_succ_le (h u : ℕ) : routeCut h (u + 1) ≤ routeCut h u + 2 := by
  unfold routeCut
  split <;> split <;> omega

def routeLo (n t j c : ℕ) : ℕ := j + routeCut (n - t) (c - (t - 1 - j))

def routeHi (n t j c : ℕ) : ℕ := routeLo n t j (c + 1)

private theorem routeLo_mono (n t j : ℕ) : Monotone (routeLo n t j) := by
  intro a b hab
  exact Nat.add_le_add_left (routeCut_mono _ (Nat.sub_le_sub_right hab _)) _

private theorem routeHi_lt {n t j c : ℕ} (ht : t ≤ n) (hj : j < t) :
    routeHi n t j c < n := by
  unfold routeHi routeLo
  have h := routeCut_le (n - t) (c + 1 - (t - 1 - j))
  omega

private theorem routeHi_le_lo_add_two (n t j c : ℕ) :
    routeHi n t j c ≤ routeLo n t j c + 2 := by
  unfold routeHi routeLo
  have h := routeCut_succ_le (n - t) (c - (t - 1 - j))
  have hm := routeCut_mono (n - t) (show c + 1 - (t - 1 - j) ≤ (c - (t - 1 - j)) + 1 by omega)
  omega

private theorem routeHi_lt_next_route {n t i j c : ℕ} (hi : i < j) (hj : j < t) :
    routeHi n t i c < routeLo n t j c := by
  unfold routeHi routeLo
  have h := routeCut_mono (n - t)
    (show c + 1 - (t - 1 - i) ≤ c - (t - 1 - j) by omega)
  omega

private theorem routeLo_zero {n t j : ℕ} (h : t ≤ n - 2) (hn : 2 ≤ n) :
    routeLo n t j 0 = j := by
  simp [routeLo, routeCut, show 1 < n - t by omega]

private theorem routeLo_final {n k t j : ℕ} (hk : n - 2 ≤ k) (hj : j < t)
    (ht : t ≤ n - 2) : routeLo n t j k = j + (n - t) := by
  unfold routeLo routeCut
  rw [ite_eq_right (by omega)]

/-- In the short interval, select a longest contiguous increasing run. -/
def selectedRows {n : ℕ} (w : Equiv.Perm (Fin n)) (lo hi : ℕ) : ℕ × ℕ :=
    if hi = lo then (lo, lo)
    else if ascStep w lo = 1 then
      if hi = lo + 2 ∧ ascStep w (lo + 1) = 1 then (lo, hi) else (lo, lo + 1)
    else if hi = lo + 2 ∧ ascStep w (lo + 1) = 1 then (lo + 1, hi) else (lo, lo)

private theorem selectedRows_spec {n lo hi : ℕ} (w : Equiv.Perm (Fin n))
    (hle : lo ≤ hi) (hhi : hi ≤ lo + 2) :
    let p := selectedRows w lo hi
    lo ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ hi ∧
      p.2 + 1 - p.1 = 1 + (ascPrefix w hi - ascPrefix w lo) ∧
      ∀ i, p.1 ≤ i → i < p.2 → ascStep w i = 1 := by
  have h₁ := ascStep_le_one w lo
  have h₂ := ascStep_le_one w (lo + 1)
  have e₁ : ascPrefix w (lo + 1) = ascPrefix w lo + ascStep w lo := rfl
  have e₂ : ascPrefix w (lo + 2) = ascPrefix w lo + ascStep w lo + ascStep w (lo + 1) := rfl
  have htriv : ∀ i, lo ≤ i → i < lo → ascStep w i = 1 := by
    intro i hl hu
    omega
  rcases (show hi = lo ∨ hi = lo + 1 ∨ hi = lo + 2 by omega) with he | he | he
  · rw [he]
    simpa [selectedRows] using htriv
  · rw [he]
    by_cases ha : ascStep w lo = 1
    · have hh : ∀ i, lo ≤ i → i < lo + 1 → ascStep w i = 1 := by
        intro i hl hu
        rwa [show i = lo by omega]
      simp [selectedRows, ha, e₁]
      exact ⟨by omega, fun i h h' => hh i h (by omega)⟩
    · have hz : ascStep w lo = 0 := by omega
      simpa [selectedRows, hz, e₁] using htriv
  · rw [he]
    by_cases ha : ascStep w lo = 1 <;> by_cases hb : ascStep w (lo + 1) = 1
    · have hh : ∀ i, lo ≤ i → i < lo + 2 → ascStep w i = 1 := by
        intro i hl hu
        rcases (show i = lo ∨ i = lo + 1 by omega) with rfl | rfl <;> assumption
      simp [selectedRows, ha, hb, e₂]
      exact ⟨by omega, fun i h h' => hh i h (by omega)⟩
    · have hz : ascStep w (lo + 1) = 0 := by omega
      have hh : ∀ i, lo ≤ i → i < lo + 1 → ascStep w i = 1 := by
        intro i hl hu
        rwa [show i = lo by omega]
      simp [selectedRows, ha, hz, e₂]
      exact ⟨by omega, fun i h h' => hh i h (by omega)⟩
    · have hz : ascStep w lo = 0 := by omega
      have hh : ∀ i, lo + 1 ≤ i → i < lo + 2 → ascStep w i = 1 := by
        intro i hl hu
        rwa [show i = lo + 1 by omega]
      simp [selectedRows, hz, hb, e₂]
      exact fun i h h' => hh i (by omega) h'
    · have hz₁ : ascStep w lo = 0 := by omega
      have hz₂ : ascStep w (lo + 1) = 0 := by omega
      simpa [selectedRows, hz₁, hz₂, e₂] using htriv

private theorem ascends_on_interval {n lo hi : ℕ} (w : Equiv.Perm (Fin n)) {a b : Fin n}
    (hstep : ∀ i, lo ≤ i → i < hi → ascStep w i = 1)
    (ha : lo ≤ a.val) (hb : b.val ≤ hi) (hab : a < b) : w a < w b := by
  obtain ⟨b, hbn⟩ := b
  induction b using Nat.strong_induction_on with
  | h b ih =>
    have hlt : a.val < b := hab
    change b ≤ hi at hb
    let q : Fin n := ⟨b - 1, by omega⟩
    have hq : q.val + 1 = b := by dsimp [q]; omega
    have hqval : q.val = b - 1 := rfl
    have hh := hstep q.val (by omega) (by omega)
    have hs := (ascStep_eq_one_iff w (show q.val + 1 < n by omega)).mp hh
    have hs' : w q < w ⟨b, hbn⟩ := by simpa [hq] using hs
    by_cases he : a = q
    · simpa [he] using hs'
    · have hlt' : a.val < q.val := Nat.lt_of_le_of_ne (by omega) (fun e => he (Fin.ext e))
      exact (ih q.val (by omega) q.isLt (show q.val ≤ hi by omega) hlt').trans hs'

def routePicks {n : ℕ} (w : Equiv.Perm (Fin n)) (t j c : ℕ) : Finset ℕ :=
  let p := selectedRows w (routeLo n t j c) (routeHi n t j c)
  Icc p.1 p.2

private theorem routePicks_bounds {n t j c r : ℕ} (w : Equiv.Perm (Fin n))
    (hr : r ∈ routePicks w t j c) : routeLo n t j c ≤ r ∧ r ≤ routeHi n t j c := by
  have hs := selectedRows_spec w ((routeLo_mono n t j) (Nat.le_succ c))
    (routeHi_le_lo_add_two n t j c)
  have hm := mem_Icc.mp hr
  exact ⟨hs.1.trans hm.1, hm.2.trans hs.2.2.1⟩

private theorem routePicks_card {n t j c : ℕ} (w : Equiv.Perm (Fin n)) :
    (routePicks w t j c).card =
      1 + (ascPrefix w (routeHi n t j c) - ascPrefix w (routeLo n t j c)) := by
  rw [routePicks, Nat.card_Icc]
  exact (selectedRows_spec w ((routeLo_mono n t j) (Nat.le_succ c))
    (routeHi_le_lo_add_two n t j c)).2.2.2.1

private theorem routePicks_ascends {n t j c : ℕ} (w : Equiv.Perm (Fin n)) {a b : Fin n}
    (ha : a.val ∈ routePicks w t j c) (hb : b.val ∈ routePicks w t j c) (h : a < b) :
    w a < w b := by
  have hs := selectedRows_spec w ((routeLo_mono n t j) (Nat.le_succ c))
    (routeHi_le_lo_add_two n t j c)
  exact ascends_on_interval w hs.2.2.2.2 (mem_Icc.mp ha).1 (mem_Icc.mp hb).2 h

#print axioms routePicks_card
#print axioms routePicks_ascends


def routeCells {n k : ℕ} (w : Equiv.Perm (Fin n)) (t j : ℕ) : Finset (Cell n k) :=
  univ.filter (fun a => a.1.val ∈ routePicks w t j a.2.val)

private theorem routeCells_increasing {n k t j : ℕ} (w : Equiv.Perm (Fin n))
    {a b : Cell n k} (ha : a ∈ routeCells w t j) (hb : b ∈ routeCells w t j) (hab : before a b) :
    value w a < value w b := by
  have ha' := (mem_filter.mp ha).2
  have hb' := (mem_filter.mp hb).2
  have hA := routePicks_bounds w ha'
  have hB := routePicks_bounds w hb'
  rcases lt_trichotomy a.2 b.2 with h | e | h
  · exact letter_lt_of_copy_lt h
  · have hrow : a.1 < b.1 := hab.resolve_right (by simp [e])
    have hcol : a.2.val = b.2.val := congrArg Fin.val e
    have hb'' : b.1.val ∈ routePicks w t j a.2.val := by simpa only [hcol] using hb'
    exact (letter_lt_iff w a.1 b.1 a.2.val b.2.val).mpr
      (Or.inr ⟨hcol, routePicks_ascends w ha' hb'' hrow⟩)
  · have hcol : b.2.val + 1 ≤ a.2.val := h
    have hhi := (routeLo_mono n t j) hcol
    have hrow : b.1.val ≤ a.1.val := hB.2.trans (hhi.trans hA.1)
    rcases hab with h' | ⟨_, h'⟩
    · exact (Nat.not_lt_of_ge hrow h').elim
    · exact (Nat.lt_asymm h' h).elim

private theorem routeCell_unique {n k t : ℕ} {w : Equiv.Perm (Fin n)} {a : Cell n k}
    {i j : Fin t} (hi : a ∈ routeCells w t i.val) (hj : a ∈ routeCells w t j.val) : i = j := by
  have h₁ := routePicks_bounds w (mem_filter.mp hi).2
  have h₂ := routePicks_bounds w (mem_filter.mp hj).2
  rcases lt_trichotomy i j with h | h | h
  · have ht := routeHi_lt_next_route (n := n) (c := a.2.val) h j.isLt
    omega
  · exact h
  · have ht := routeHi_lt_next_route (n := n) (c := a.2.val) h i.isLt
    omega

private theorem route_column_card {n k t j : ℕ} (w : Equiv.Perm (Fin n)) (ht : t ≤ n)
    (hj : j < t) (c : Fin k) :
    ((routeCells w t j).filter (fun a => a.2 = c)).card = (routePicks w t j c.val).card := by
  classical
  apply card_bij (fun a _ => a.1.val)
  · intro a ha
    have h := (mem_filter.mp ha).2
    have hp := (mem_filter.mp (mem_filter.mp ha).1).2
    simpa only [h] using hp
  · intro a ha b hb h
    exact Prod.ext (Fin.ext h) ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm)
  · intro i hi
    have hb := routePicks_bounds w hi
    let a : Cell n k := (⟨i, hb.2.trans_lt (routeHi_lt ht hj)⟩, c)
    exact ⟨a, mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hi⟩, rfl⟩, rfl⟩

private theorem route_sum {n : ℕ} (w : Equiv.Perm (Fin n)) (t j k : ℕ) :
    (∑ c ∈ range k, (1 + (ascPrefix w (routeHi n t j c) - ascPrefix w (routeLo n t j c)))) =
      k + (ascPrefix w (routeLo n t j k) - ascPrefix w (routeLo n t j 0)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih]
    have hmono : Monotone (fun c => ascPrefix w (routeLo n t j c)) :=
      (ascPrefix_mono w).comp (routeLo_mono n t j)
    have h₁ := hmono (Nat.zero_le k)
    have h₂ := hmono (Nat.le_succ k)
    unfold routeHi
    change ascPrefix w (routeLo n t j 0) ≤ ascPrefix w (routeLo n t j k) at h₁
    change ascPrefix w (routeLo n t j k) ≤ ascPrefix w (routeLo n t j (k + 1)) at h₂
    omega

private theorem route_card {n k t : ℕ} (w : Equiv.Perm (Fin n)) (hn : 2 ≤ n) (ht : t ≤ n - 2)
    (hk : n - 2 ≤ k) (j : Fin t) :
    (routeCells (k := k) w t j.val).card = k + (ascPrefix w (j.val + (n - t)) - ascPrefix w j.val) := by
  have h := card_eq_sum_card_fiberwise (f := Prod.snd) (s := routeCells (k := k) w t j.val)
    (t := univ) (fun c _ => mem_univ c.2)
  rw [h]
  simp_rw [route_column_card w (show t ≤ n by omega) j.isLt, routePicks_card]
  rw [Fin.sum_univ_eq_sum_range (fun c => 1 +
    (ascPrefix w (routeHi n t j.val c) - ascPrefix w (routeLo n t j.val c))),
    route_sum, routeLo_zero ht hn, routeLo_final hk j.isLt ht]

private noncomputable def routeColor {n k t : ℕ} (w : Equiv.Perm (Fin n)) (a : Cell n k) :
    Option (Fin t) :=
  open Classical in
    if h : ∃ j : Fin t, a ∈ routeCells w t j.val then some h.choose else none

private theorem routeColor_eq_some {n k t : ℕ} {w : Equiv.Perm (Fin n)}
    {a : Cell n k} {j : Fin t} : routeColor w a = some j ↔ a ∈ routeCells w t j.val := by
  classical
  unfold routeColor
  split
  · rename_i h
    constructor
    · intro e
      rw [← Option.some.inj e]
      exact h.choose_spec
    · intro e
      exact congrArg some (routeCell_unique h.choose_spec e)
  · rename_i h
    constructor
    · intro e
      cases e
    · intro e
      exact (h ⟨j, e⟩).elim

private theorem routeCover_card {n k t : ℕ} (w : Equiv.Perm (Fin n))
    (hn : 2 ≤ n) (ht : t ≤ n - 2) (hk : n - 2 ≤ k) :
    ((cells n k).filter (fun a => (routeColor (t := t) w a).isSome)).length = shapeBound w k t := by
  classical
  let used : Finset (Cell n k) := univ.filter (fun a => (routeColor (t := t) w a).isSome)
  have he : ((cells n k).filter (fun a => (routeColor (t := t) w a).isSome)).length = used.card := by
    have hdec (b : Bool) : decide (b = true) = b := by cases b <;> rfl
    simpa only [hdec] using filtered_cells_card (k := k) (fun a => (routeColor (t := t) w a).isSome = true)
  let F (a : Cell n k) : Option (Fin t) := routeColor w a
  have h := card_eq_sum_card_fiberwise (f := F) (s := used) (t := (univ : Finset (Fin t)).image some)
    (fun a ha => by
      have hu := (mem_filter.mp ha).2
      exact mem_image.mpr ⟨(F a).get hu, mem_univ _, Option.some_get _⟩)
  have hh (i : Fin t) :
      (used.filter (fun a => F a = some i)).card = (routeCells (k := k) w t i.val).card := by
    congr 1
    ext a
    simp only [mem_filter, F, routeColor_eq_some]
    constructor
    · exact And.right
    · intro hi
      have hs : routeColor w a = some i := routeColor_eq_some.mpr hi
      exact ⟨mem_filter.mpr ⟨mem_univ _, by simp [hs]⟩, hi⟩
  rw [he, h, sum_image (fun _ _ _ _ e => Option.some.inj e)]
  simp_rw [hh, route_card w hn ht hk]
  rw [sum_add_distrib, shapeBound_route w (show t ≤ n by omega),
    Fin.sum_univ_eq_sum_range (fun j => ascPrefix w (j + (n - t)) - ascPrefix w j)]
  simp only [sum_const, card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]

/-- Sharp lower bound from disjoint increasing routes with one merged triple. -/
theorem topSize_route_lower {n k t : ℕ} (w : Equiv.Perm (Fin n))
    (hn : 2 ≤ n) (ht : t ≤ n - 2) (hk : n - 2 ≤ k) :
    shapeBound w k t ≤ topSize (insertionTableau (kFoldWord w k)) t := by
  have h := attains_grid (k := k) (w := w) (routeColor (t := t) w) (by
    intro a b hab c ha hb
    exact routeCells_increasing w (routeColor_eq_some.mp ha) (routeColor_eq_some.mp hb) hab)
  rw [routeCover_card w hn ht hk] at h
  exact (greene (kFoldWord_nodup w k) t).2 _ h

#print axioms topSize_route_lower

end TableauStabilization
```

### `StabConjecture.lean`

```lean
import StabRoutes

set_option autoImplicit false

namespace TableauStabilization

/-- The sharp copy-grid shape formula applies already at n−2 when there
are at most n−2 ascents. -/
theorem shape_formula {n k t : ℕ} (w : Equiv.Perm (Fin n))
    (hn : 2 ≤ n) (hk : n - 2 ≤ k) (ha : ascents w ≤ k) (ht : t ≤ n) :
    topSize (insertionTableau (kFoldWord w k)) t = shapeBound w k t := by
  apply le_antisymm (topSize_upper w ht ha)
  by_cases hfull : t = n
  · subst t
    rw [topSize_n]
    simp [shapeBound]
  by_cases hpen : t = n - 1
  · subst t
    exact topSize_penultimate_lower w (by omega) ha
  · exact topSize_route_lower w hn (by omega) hk

theorem stabilizesAt_succ_of_threshold {n k : ℕ} (w : Equiv.Perm (Fin n))
    (hn : 2 ≤ n) (hk : n - 2 ≤ k) (ha : ascents w ≤ k) :
    stabilizesAt w (k + 1) := by
  apply stabilizesAt_of_growsOne w
  apply growsOne_of_prefixGrowth w
  intro t ht
  rw [shape_formula w hn (hk.trans (Nat.le_succ k)) (ha.trans (Nat.le_succ k)) ht,
    shape_formula w hn hk ha ht, shapeBound, shapeBound, Nat.mul_succ]
  omega

theorem id_stabilizesAt_n {n : ℕ} (hn : 0 < n) : stabilizesAt (1 : Equiv.Perm (Fin n)) n := by
  by_cases h : n = 1
  · subst n
    refine ⟨by decide, ?_⟩
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    decide
  · have ht := stabilizesAt_succ_of_threshold (k := n - 1) (1 : Equiv.Perm (Fin n))
      (by omega) (by omega) (ascents_le _)
    rwa [show n - 1 + 1 = n by omega] at ht

theorem stabilizesAt_pred_of_ne_one {n : ℕ} {w : Equiv.Perm (Fin n)} (h : w ≠ 1) :
    stabilizesAt w (n - 1) := by
  have hn : 2 ≤ n := by
    by_contra! hn
    have hsmall : n = 0 ∨ n = 1 := by omega
    rcases hsmall with rfl | rfl
    · exact h (Subsingleton.elim _ _)
    · exact h (Subsingleton.elim _ _)
  have ht := stabilizesAt_succ_of_threshold (k := n - 2) w hn (Nat.le_refl _)
    (ascents_le_of_ne_one w h)
  rwa [show n - 2 + 1 = n - 1 by omega] at ht

theorem exists_stabilizes {n : ℕ} (w : Equiv.Perm (Fin n)) : ∃ k, stabilizesAt w k := by
  by_cases hn : 0 < n
  · by_cases hw : w = 1
    · subst w
      exact ⟨n, id_stabilizesAt_n hn⟩
    · exact ⟨n - 1, stabilizesAt_pred_of_ne_one hw⟩
  · have he : n = 0 := by omega
    subst n
    exact ⟨1, by decide, fun i => Fin.elim0 i⟩

/-- The least positive copy count satisfying the source's last-copy row test. -/
noncomputable def stab {n : ℕ} (w : Equiv.Perm (Fin n)) : ℕ :=
  leastStabilization w (exists_stabilizes w)

theorem stab_spec {n : ℕ} (w : Equiv.Perm (Fin n)) : stabilizesAt w (stab w) :=
  leastStabilization_spec (exists_stabilizes w)

theorem stab_min {n k : ℕ} {w : Equiv.Perm (Fin n)} (hk : stabilizesAt w k) : stab w ≤ k :=
  leastStabilization_le (exists_stabilizes w) hk

theorem stab_id {n : ℕ} (hn : 0 < n) : stab (1 : Equiv.Perm (Fin n)) = n :=
  leastStabilization_id (id_stabilizesAt_n hn)

theorem stab_le_pred_of_ne_one {n : ℕ} {w : Equiv.Perm (Fin n)} (h : w ≠ 1) :
    stab w ≤ n - 1 := stab_min (stabilizesAt_pred_of_ne_one h)

/-- Ahlbach's Conjecture 9.2, MathDB 343104. -/
theorem mathdb_343104 (n : ℕ) (hn : 0 < n) (w : Equiv.Perm (Fin n)) :
    stab w = n ↔ w = 1 := by
  constructor
  · intro h
    by_contra hne
    have hl := stab_le_pred_of_ne_one hne
    omega
  · rintro rfl
    exact stab_id hn

#eval Lean.versionString
#check mathdb_343104
#check stab_id
#check stab_le_pred_of_ne_one
#check stabilizesAt_iff_growsOne
#check shape_formula
#check greene
#print stabilizesAt
#print stab
#print axioms mathdb_343104
#print axioms stab_id
#print axioms stab_le_pred_of_ne_one
#print axioms exists_stabilizes
#print axioms stab_spec
#print axioms stabilizesAt_iff_growsOne
#print axioms shape_formula
#print axioms greene

end TableauStabilization
```
