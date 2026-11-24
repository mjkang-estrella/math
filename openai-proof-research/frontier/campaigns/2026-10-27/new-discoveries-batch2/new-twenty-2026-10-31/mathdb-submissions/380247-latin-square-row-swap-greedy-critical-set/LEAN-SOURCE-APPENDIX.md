# Lean source appendix for MathDB 380247

### `LatinGreedy.lean`

```lean
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Order.Lex

namespace Rowswap

abbrev Cell (n : ℕ) := Fin n × Fin n
abbrev Square (n : ℕ) := Fin n → Fin n → Fin n

def IsLatin (L : Square n) : Prop :=
  (∀ r, Function.Bijective (L r)) ∧ ∀ c, Function.Bijective (fun r => L r c)

/-- A support denotes the partial Latin square carrying exactly the entries of L there. -/
def PartialLatin (P : Finset (Cell n)) (L : Square n) : Prop :=
  (∀ a ∈ P, ∀ b ∈ P, a.1 = b.1 → L a.1 a.2 = L b.1 b.2 → a = b) ∧
  (∀ a ∈ P, ∀ b ∈ P, a.2 = b.2 → L a.1 a.2 = L b.1 b.2 → a = b)

def Completes (P : Finset (Cell n)) (L M : Square n) : Prop :=
  IsLatin M ∧ ∀ p ∈ P, M p.1 p.2 = L p.1 p.2

def UniqueCompletion (P : Finset (Cell n)) (L : Square n) : Prop :=
  Completes P L L ∧ ∀ M, Completes P L M → M = L

def IsCritical (P : Finset (Cell n)) (L : Square n) : Prop :=
  UniqueCompletion P L ∧ ∀ p ∈ P, ¬ UniqueCompletion (P.erase p) L

def rectangle (r t c d : Fin n) : Finset (Cell n) :=
  {(r,c), (r,d), (t,c), (t,d)}

def Intercalate (L : Square n) (I : Finset (Cell n)) : Prop :=
  ∃ r t c d, r ≠ t ∧ c ≠ d ∧ L r c = L t d ∧ L r d = L t c ∧
    L r c ≠ L r d ∧ I = rectangle r t c d

def TwoCritical (P : Finset (Cell n)) (L : Square n) : Prop :=
  IsCritical P L ∧ ∀ p ∈ P, ∃ I, Intercalate L I ∧ P ∩ I = {p}

def Available (L : Square n) (P : Finset (Cell n)) (p : Cell n) (a : Fin n) : Prop :=
  p ∉ P ∧ ∀ q ∈ P, (p.1 = q.1 ∨ p.2 = q.2) → L q.1 q.2 ≠ a

def Forced (L : Square n) (P : Finset (Cell n)) (p : Cell n) : Prop :=
  Available L P p (L p.1 p.2) ∧ ∀ a, Available L P p a → a = L p.1 p.2

inductive Fills (L : Square n) : Finset (Cell n) → List (Cell n) → Prop
  | done : Fills L Finset.univ []
  | step {P p xs} : p ∉ P → Forced L P p → Fills L (insert p P) xs → Fills L P (p :: xs)

def Strong (P : Finset (Cell n)) (L : Square n) : Prop :=
  IsCritical P L ∧ ∃ xs, Fills L P xs

def CompletesTopDown (P : Finset (Cell n)) (L : Square n) : Prop :=
  ∃ xs, Fills L P xs ∧ xs.Pairwise (fun a b => a.1 ≤ b.1)

/-- The position in row-major order, using the indicated numbering of the rows. -/
def key (row : Equiv.Perm (Fin n)) (p : Cell n) : ℕ :=
  n * (row p.1).val + p.2.val

theorem key_injective (row : Equiv.Perm (Fin n)) : Function.Injective (key row) := by
  rintro ⟨r,c⟩ ⟨t,d⟩ he
  have hn : 0 < n := Nat.zero_lt_of_lt c.isLt
  have hcol : c = d := by
    apply Fin.ext
    simpa [key, Nat.mod_eq_of_lt c.isLt, Nat.mod_eq_of_lt d.isLt] using
      congrArg (· % n) he
  have hrow : r = t := by
    apply row.injective
    apply Fin.ext
    simpa [key, Nat.mul_comm n, Nat.add_comm, Nat.add_mul_div_right _ _ hn,
      Nat.div_eq_of_lt c.isLt, Nat.div_eq_of_lt d.isLt] using congrArg (· / n) he
  simp [hrow,hcol]

instance (row : Equiv.Perm (Fin n)) : Std.Antisymm (fun p q => key row q ≤ key row p) where
  antisymm _ _ h h' := key_injective row (le_antisymm h' h)

def descending (row : Equiv.Perm (Fin n)) : List (Cell n) :=
  Finset.univ.sort (fun p q => key row q ≤ key row p)

/-- The prose order. The displayed formula numbers rows in the opposite direction. -/
def f0order (n : ℕ) : List (Cell n) := descending (Equiv.refl (Fin n))

/-- The printed formula's increasing row coordinate and right-to-left column order. -/
def printedOrder (n : ℕ) : List (Cell n) := descending Fin.revPerm

noncomputable def attempt (L : Square n) (P : Finset (Cell n)) (p : Cell n) :
    Finset (Cell n) := by
  classical
  exact if UniqueCompletion (P.erase p) L then P.erase p else P

noncomputable def greedy (L : Square n) (order : List (Cell n)) : Finset (Cell n) :=
  order.foldl (attempt L) Finset.univ

noncomputable def gcs (L : Square n) : Finset (Cell n) := greedy L (f0order n)

noncomputable def printedGcs (L : Square n) : Finset (Cell n) := greedy L (printedOrder n)

theorem available_self (hL : IsLatin L) (hp : p ∉ P) :
    Available L P p (L p.1 p.2) := by
  refine ⟨hp,?_⟩
  intro q hq hsame hval
  apply hp
  obtain ⟨r,c⟩ := p
  obtain ⟨t,d⟩ := q
  rcases hsame with he | he
  · change r = t at he
    subst t
    have he : d = c := (hL.1 r).1 hval
    simpa [he] using hq
  · change c = d at he
    subst d
    have he : t = r := (hL.2 c).1 hval
    simpa [he] using hq

theorem forced_agree (hM : Completes P L M) (hp : p ∉ P) (hf : Forced L P p) :
    M p.1 p.2 = L p.1 p.2 := by
  apply hf.2
  refine ⟨hp,?_⟩
  intro q hq hsame
  rw [← hM.2 q hq]
  exact (available_self hM.1 hp).2 q hq hsame

theorem Fills.unique (hL : IsLatin L) (h : Fills L P xs) : UniqueCompletion P L := by
  refine ⟨⟨hL, fun _ _ => rfl⟩, ?_⟩
  induction h with
  | done =>
    intro M hM
    exact funext fun r => funext fun c => hM.2 (r,c) (Finset.mem_univ _)
  | @step P p xs hp hf _ ih =>
    intro M hM
    apply ih M
    refine ⟨hM.1, ?_⟩
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact forced_agree hM hp hf
    · exact hM.2 q hq

theorem Fills.mem_of_missing (h : Fills L P xs) (hp : p ∉ P) : p ∈ xs := by
  induction h with
  | done => exact (hp (Finset.mem_univ _)).elim
  | @step P q xs _ _ _ ih =>
    by_cases he : p = q
    · simp [he]
    · exact List.mem_cons_of_mem _ (ih (by simpa [he] using hp))

theorem UniqueCompletion.mono (h : UniqueCompletion P L) (hle : P ⊆ Q) :
    UniqueCompletion Q L :=
  ⟨⟨h.1.1, fun _ _ => rfl⟩, fun M hM => h.2 M ⟨hM.1, fun p hp => hM.2 p (hle hp)⟩⟩

theorem isCritical_iff_proper_subsets {P : Finset (Cell n)} {L : Square n} :
    IsCritical P L ↔ UniqueCompletion P L ∧
      ∀ Q : Finset (Cell n), Q ⊂ P → ¬ UniqueCompletion Q L := by
  constructor
  · rintro ⟨hu,hm⟩
    refine ⟨hu,?_⟩
    intro Q hQ hU
    have hPQ : ¬ P ⊆ Q := fun h => (ne_of_lt hQ) (Finset.Subset.antisymm hQ.le h)
    obtain ⟨p,hp,hpQ⟩ := Finset.not_subset.mp hPQ
    apply hm p hp
    exact hU.mono (fun t ht => Finset.mem_erase.mpr ⟨fun e => hpQ (e ▸ ht),hQ.le ht⟩)
  · rintro ⟨hu,hm⟩
    exact ⟨hu,fun p hp => hm (P.erase p) (Finset.erase_ssubset hp)⟩

private def flip (L : Square n) (r t c d : Fin n) : Square n :=
  fun i j => if i = r ∨ i = t then L i (Equiv.swap c d j) else L i j

private theorem flip_column (L : Square n) {r t c d : Fin n}
    (hrt : r ≠ t) (hcd : c ≠ d) (h₁ : L r c = L t d) (h₂ : L r d = L t c)
    (i j : Fin n) :
    flip L r t c d i j = if j = c ∨ j = d then L (Equiv.swap r t i) j else L i j := by
  by_cases hir : i = r
  · subst i
    by_cases hjc : j = c
    · subst j; simp [flip, h₂]
    by_cases hjd : j = d
    · subst j; simp [flip, h₁, hcd.symm]
    · simp [flip, hjc, hjd, Equiv.swap_apply_of_ne_of_ne]
  by_cases hit : i = t
  · subst i
    by_cases hjc : j = c
    · subst j; simp [flip, h₁, hrt.symm]
    by_cases hjd : j = d
    · subst j; simp [flip, h₂, hrt.symm, hcd.symm]
    · simp [flip, hjc, hjd, Equiv.swap_apply_of_ne_of_ne]
  · simp [flip, hir, hit, Equiv.swap_apply_of_ne_of_ne]

theorem Intercalate.not_unique (hL : IsLatin L) (hI : Intercalate L I)
    (hd : Disjoint P I) : ¬ UniqueCompletion P L := by
  obtain ⟨r,t,c,d,hrt,hcd,h₁,h₂,hs,rfl⟩ := hI
  let M := flip L r t c d
  have hm : IsLatin M := by
    constructor
    · intro i
      change Function.Bijective (fun j => if i = r ∨ i = t then
        L i (Equiv.swap c d j) else L i j)
      by_cases hi : i = r ∨ i = t
      · simpa only [ite_eq_left hi, Function.comp_def] using (hL.1 i).comp (Equiv.swap c d).bijective
      · simpa only [ite_eq_right hi] using hL.1 i
    · intro j
      by_cases hj : j = c ∨ j = d
      · simpa [M, flip_column L hrt hcd h₁ h₂, hj, Function.comp_def] using
          (hL.2 j).comp (Equiv.swap r t).bijective
      · simpa [M, flip_column L hrt hcd h₁ h₂, hj] using hL.2 j
  intro hu
  have he := hu.2 M ⟨hm, ?_⟩
  · have := congrFun (congrFun he r) c
    exact hs (by simpa [M, flip] using this.symm)
  · rintro ⟨i,j⟩ hp
    have hn := fun hi => Finset.disjoint_left.mp hd hp hi
    by_cases hi : i = r ∨ i = t
    · have hj : j ≠ c ∧ j ≠ d := by
        constructor <;> intro hj <;> apply hn <;>
          rcases hi with he | he <;> simp [rectangle, he, hj]
      simp [M, flip, hi, Equiv.swap_apply_of_ne_of_ne hj.1 hj.2]
    · simp [M, flip, hi]

/-- Every clue has a private intercalate with its three other cells at larger keys. -/
def Witnesses (L : Square n) (P : Finset (Cell n)) (priority : Cell n → ℕ) : Prop :=
  ∀ p ∈ P, ∃ I, Intercalate L I ∧ p ∈ I ∧
    ∀ q ∈ I, q ≠ p → q ∉ P ∧ priority p < priority q

theorem twoCritical_of_witnesses (hL : IsLatin L) (hu : UniqueCompletion P L)
    (hw : Witnesses L P priority) : TwoCritical P L := by
  have hprivate : ∀ p ∈ P, ∃ I, Intercalate L I ∧ P ∩ I = {p} := by
    intro p hp
    obtain ⟨I,hI,hpI,h⟩ := hw p hp
    refine ⟨I,hI,Finset.ext fun q => ?_⟩
    by_cases he : q = p
    · subst q; simp [hp, hpI]
    · simp only [Finset.mem_inter, Finset.mem_singleton, he, iff_false, not_and]
      exact fun hq hqI => (h q hqI he).1 hq
  refine ⟨⟨hu, ?_⟩, hprivate⟩
  intro p hp
  obtain ⟨I,hI,he⟩ := hprivate p hp
  apply hI.not_unique hL
  rw [Finset.disjoint_left]
  intro q hq hqI
  have := Finset.mem_inter.mpr ⟨(Finset.mem_erase.mp hq).2,hqI⟩
  rw [he, Finset.mem_singleton] at this
  exact (Finset.mem_erase.mp hq).1 this

private theorem scan {L : Square n} (hL : IsLatin L) (hu : UniqueCompletion P L)
    (hw : Witnesses L P priority) (xs : List (Cell n))
    (hs : xs.Pairwise (fun p q => priority q ≤ priority p)) (hn : xs.Nodup) :
    xs.foldl (attempt L) (P ∪ xs.toFinset) = P := by
  classical
  induction xs with
  | nil => simp
  | cons p xs ih =>
    have hp : p ∉ xs.toFinset := by simpa using (List.nodup_cons.mp hn).1
    have he := ih (List.pairwise_cons.mp hs).2 (List.nodup_cons.mp hn).2
    simp only [List.foldl_cons, List.toFinset_cons]
    suffices attempt L (P ∪ insert p xs.toFinset) p = P ∪ xs.toFinset by rw [this, he]
    unfold attempt
    by_cases hpP : p ∈ P
    · obtain ⟨I,hI,_,h⟩ := hw p hpP
      have hd : Disjoint ((P ∪ insert p xs.toFinset).erase p) I := by
        rw [Finset.disjoint_left]
        intro q hq hqI
        obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hq
        obtain ⟨hqP, hlt⟩ := h q hqI hne
        rcases Finset.mem_union.mp hmem with hb | hb
        · exact hqP hb
        rcases Finset.mem_insert.mp hb with hb | hb
        · exact hne hb
        · exact (not_le_of_gt hlt) ((List.pairwise_cons.mp hs).1 q (List.mem_toFinset.mp hb))
      rw [ite_eq_right (hI.not_unique hL hd)]
      ext q
      simp only [Finset.mem_union, Finset.mem_insert]
      grind
    · have hErase : (P ∪ insert p xs.toFinset).erase p = P ∪ xs.toFinset := by
        ext q
        by_cases hq : q = p
        · subst q; simp [hpP, hp]
        · simp [hq]
      rw [hErase, ite_eq_left (hu.mono Finset.subset_union_left)]

theorem greedy_eq {L : Square n} (row : Equiv.Perm (Fin n))
    (hL : IsLatin L) (hu : UniqueCompletion P L)
    (hw : Witnesses L P (key row)) : greedy L (descending row) = P := by
  classical
  let xs := descending row
  have ht : xs.toFinset = Finset.univ := by ext; simp [xs, descending]
  have hj : P ∪ (Finset.univ : Finset (Cell n)) = Finset.univ := by ext; simp
  simpa only [greedy, ht, hj] using
    scan hL hu hw xs (Finset.pairwise_sort _ _) (Finset.sort_nodup _ _)

end Rowswap
```

### `LatinCertificate.lean`

```lean
import LatinGreedy
import Mathlib.Data.Prod.Lex

namespace Rowswap

theorem key_lt_same (row : Equiv.Perm (Fin n)) {r c d : Fin n} (h : c < d) :
    key row (r,c) < key row (r,d) := Nat.add_lt_add_left h _

theorem key_lt_later (row : Equiv.Perm (Fin n)) {r t c d : Fin n} (h : row r < row t) :
    key row (r,c) < key row (t,d) := by
  have hm := Nat.mul_le_mul_left n (Nat.succ_le_of_lt h)
  simp only [Nat.mul_succ] at hm
  change n * (row r).val + c.val < n * (row t).val + d.val
  have hc := c.isLt
  omega

/-- The rectangular form of the witness used in the proof. -/
def RectWitnesses (L : Square n) (P : Finset (Cell n)) (row : Equiv.Perm (Fin n)) : Prop :=
  ∀ r c, (r,c) ∈ P →
    ∃ t d, row r < row t ∧ c < d ∧ L r c = L t d ∧ L r d = L t c ∧
      (r,d) ∉ P ∧ (t,c) ∉ P ∧ (t,d) ∉ P

theorem RectWitnesses.witnesses (hL : IsLatin L) (h : RectWitnesses L P row) :
    Witnesses L P (key row) := by
  rintro ⟨r,c⟩ hp
  obtain ⟨t,d,hrt,hcd,h₁,h₂,h₃,h₄,h₅⟩ := h r c hp
  have hr : r ≠ t := fun he => (ne_of_lt hrt) (congrArg row he)
  have hc := ne_of_lt hcd
  refine ⟨rectangle r t c d, ⟨r,t,c,d,hr,hc,h₁,h₂,fun he => hc ((hL.1 r).1 he),rfl⟩,
    by simp [rectangle], ?_⟩
  intro q hq hne
  simp only [rectangle, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact (hne rfl).elim
  · exact ⟨h₃,key_lt_same row hcd⟩
  · exact ⟨h₄,key_lt_later row hrt⟩
  · exact ⟨h₅,key_lt_later row hrt⟩

/-- An arc from blank (r,c) to blank (r,d) uses the blank (t,c) in a later row t. -/
def Descends (L : Square n) (P : Finset (Cell n)) (row : Equiv.Perm (Fin n))
    (rank : Cell n → ℕ) : Prop :=
  ∀ r t c d, row r < row t → c ≠ d → L r d = L t c →
    (r,c) ∉ P → (r,d) ∉ P → (t,c) ∉ P → rank (r,d) < rank (r,c)

theorem fills_of_descends {L : Square n} (hL : IsLatin L) {P : Finset (Cell n)}
    (hd : Descends L P row rank) :
    ∃ xs, Fills L P xs ∧ xs.Pairwise (fun a b => row a.1 ≤ row b.1) := by
  classical
  let score (p : Cell n) := toLex (row p.1, rank p)
  suffices main : ∀ U : Finset (Cell n), ∀ Q : Finset (Cell n),
      U = Finset.univ \ Q → P ⊆ Q →
      ∃ xs, Fills L Q xs ∧ xs.Pairwise (fun a b => row a.1 ≤ row b.1) ∧
        ∀ p ∈ xs, p ∈ U by
    obtain ⟨xs,hx,hs,_⟩ := main _ P rfl (Finset.Subset.refl _)
    exact ⟨xs,hx,hs⟩
  intro U
  induction U using Finset.strongInductionOn with
  | _ U ih =>
    intro Q hU hPQ
    by_cases hUn : U.Nonempty
    · let m := (U.image score).min' (hUn.image score)
      have hm : m ∈ U.image score := Finset.min'_mem _ _
      obtain ⟨p,hp,he⟩ := Finset.mem_image.mp hm
      have hmin (q : Cell n) (hq : q ∈ U) : score p ≤ score q := by
        rw [he]
        exact Finset.min'_le _ _ (Finset.mem_image_of_mem score hq)
      have missing (q : Cell n) : q ∈ U ↔ q ∉ Q := by simp [hU]
      have hpQ := (missing p).mp hp
      obtain ⟨r,c⟩ := p
      have hf : Forced L Q (r,c) := by
        refine ⟨available_self hL hpQ, ?_⟩
        intro a ha
        obtain ⟨d,rfl⟩ := (hL.1 r).2 a
        by_contra hne
        have hcd : c ≠ d := fun h => hne (by rw [h])
        obtain ⟨t,ht⟩ := (hL.2 c).2 (L r d)
        have hrt : r ≠ t := by
          intro heq
          subst t
          exact hne ht.symm
        have hdQ : (r,d) ∉ Q := fun h => ha.2 (r,d) h (Or.inl rfl) rfl
        have htQ : (t,c) ∉ Q := fun h => ha.2 (t,c) h (Or.inr rfl) ht
        have hminT := Prod.Lex.toLex_le_toLex.mp (hmin (t,c) ((missing _).mpr htQ))
        have hminD := Prod.Lex.toLex_le_toLex.mp (hmin (r,d) ((missing _).mpr hdQ))
        have hlt : row r < row t := hminT.resolve_right
          (fun h => hrt (row.injective h.1))
        have hle := (hminD.resolve_left (lt_irrefl _)).2
        exact (not_lt_of_ge hle) (hd r t c d hlt hcd ht.symm
          (fun h => hpQ (hPQ h)) (fun h => hdQ (hPQ h)) (fun h => htQ (hPQ h)))
      have hstep : U.erase (r,c) = Finset.univ \ insert (r,c) Q := by
        ext q
        simp [missing, and_comm]
      obtain ⟨xs,hxs,hord,hmem⟩ := ih _ (Finset.erase_ssubset hp) _ hstep
        (fun q hq => Finset.mem_insert_of_mem (hPQ hq))
      refine ⟨(r,c)::xs,Fills.step hpQ hf hxs, List.pairwise_cons.mpr ⟨?_,hord⟩, ?_⟩
      · intro q hq
        have hh := Prod.Lex.toLex_le_toLex.mp
          (hmin q (Finset.mem_of_mem_erase (hmem q hq)))
        exact hh.elim le_of_lt (fun e => le_of_eq e.1)
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hp
        · exact Finset.mem_of_mem_erase (hmem q hq)
    · have hQ : Q = Finset.univ := by
        ext p
        have hn : p ∉ U := fun h => hUn ⟨p,h⟩
        simpa [hU] using hn
      subst Q
      exact ⟨[],Fills.done,List.Pairwise.nil,by simp⟩

theorem certificate {L : Square n} (hL : IsLatin L) {P : Finset (Cell n)}
    (hw : RectWitnesses L P (Equiv.refl (Fin n)))
    (hd : Descends L P (Equiv.refl (Fin n)) rank) :
    gcs L = P ∧ TwoCritical (gcs L) L ∧ Strong (gcs L) L ∧ CompletesTopDown (gcs L) L := by
  obtain ⟨xs,hxs,hord⟩ := fills_of_descends hL hd
  have hu := hxs.unique hL
  have hW := hw.witnesses hL
  have hG : gcs L = P := greedy_eq _ hL hu hW
  have hTC := twoCritical_of_witnesses hL hu hW
  rw [hG]
  exact ⟨rfl,hTC,⟨hTC.1, xs,hxs⟩,xs,hxs,hord⟩

end Rowswap
```

### `LatinXor.lean`

```lean
import LatinCertificate
import Mathlib.Tactic.IntervalCases

namespace Rowswap

abbrev Mask (s : ℕ) := Fin (2^s)

def xor (x y : Mask s) : Mask s :=
  ⟨x.val ^^^ y.val, Nat.xor_lt_two_pow x.isLt y.isLt⟩

@[simp] theorem xor_val (x y : Mask s) : (xor x y).val = x.val ^^^ y.val := rfl

theorem xor_involutive (x : Mask s) : Function.Involutive (xor x) := by
  intro y
  apply Fin.ext
  simp [← Nat.xor_assoc]

theorem xor_comm (x y : Mask s) : xor x y = xor y x :=
  Fin.ext (Nat.xor_comm _ _)

def Ls (s : ℕ) : Square (2^s) := xor

def rowSwap (L : Square n) (k k' : Fin n) : Square n :=
  fun r c => L (Equiv.swap k k' r) c

theorem IsLatin.rowSwap {L : Square n} (hL : IsLatin L) (k k' : Fin n) : IsLatin (rowSwap L k k') :=
  ⟨fun r => hL.1 (Equiv.swap k k' r), fun c => (hL.2 c).comp (Equiv.swap k k').bijective⟩

theorem latin_Ls (s : ℕ) : IsLatin (Ls s) := by
  refine ⟨fun r => (xor_involutive r).bijective, fun c => ?_⟩
  simpa only [Ls, xor_comm _ c] using (xor_involutive c).bijective

/-- The two-by-two factor in the source's direct product. -/
def baseEntry (r c : ℕ) : ℕ := if r = c then 0 else 1

/-- Direct product with the two-by-two square, using the source's block numbering. -/
def recursiveEntry : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | s+1, r, c => 2^s * baseEntry (r / 2^s) (c / 2^s) +
      recursiveEntry s (r % 2^s) (c % 2^s)

private theorem baseEntry_eq_xor {r c : ℕ} (hr : r < 2) (hc : c < 2) :
    baseEntry r c = r ^^^ c := by
  interval_cases r <;> interval_cases c <;> decide

theorem recursiveEntry_eq_xor (s : ℕ) {r c : ℕ} (hr : r < 2^s) (hc : c < 2^s) :
    recursiveEntry s r c = r ^^^ c := by
  induction s generalizing r c with
  | zero =>
    have hr' : r = 0 := by simp at hr; omega
    have hc' : c = 0 := by simp at hc; omega
    simp [recursiveEntry,hr',hc']
  | succ s ih =>
    have hpos : 0 < 2^s := Nat.two_pow_pos _
    have hr' : r / 2^s < 2 := (Nat.div_lt_iff_lt_mul hpos).mpr (by simpa [pow_succ, Nat.mul_comm 2] using hr)
    have hc' : c / 2^s < 2 := (Nat.div_lt_iff_lt_mul hpos).mpr (by simpa [pow_succ, Nat.mul_comm 2] using hc)
    rw [recursiveEntry, baseEntry_eq_xor hr' hc', ih (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos),
      ← Nat.xor_div_two_pow, ← Nat.xor_mod_two_pow]
    exact Nat.div_add_mod _ _

def recursiveSquare (s : ℕ) (r c : Mask s) : Mask s :=
  ⟨recursiveEntry s r.val c.val, by
    rw [recursiveEntry_eq_xor s r.isLt c.isLt]
    exact Nat.xor_lt_two_pow r.isLt c.isLt⟩

theorem Ls_eq_recursiveSquare (s : ℕ) : Ls s = recursiveSquare s := by
  funext r c
  exact Fin.ext (recursiveEntry_eq_xor s r.isLt c.isLt).symm

#check Ls_eq_recursiveSquare
#print axioms Ls_eq_recursiveSquare

end Rowswap
```

### `LatinPrinted.lean`

```lean
import LatinXor

namespace Rowswap

/-- Zero-based transcription of the printed formula, with argument i+1 in the paper. -/
def printedCell (n : ℕ) (hn : 0 < n) (i : Fin (n*n)) : Cell n :=
  (⟨i.val/n,(Nat.div_lt_iff_lt_mul hn).mpr i.isLt⟩,
    Fin.rev ⟨i.val%n,Nat.mod_lt _ hn⟩)

private theorem printedCell_key {n : ℕ} (hn : 0 < n) (i : Fin (n*n)) :
    key Fin.revPerm (printedCell n hn i) = n*n-1-i.val := by
  have hi := i.isLt
  have hdiv := (printedCell n hn i).1.isLt
  change i.val / n < n at hdiv
  have hmod := Nat.mod_lt i.val hn
  have hsum := Nat.mod_add_div i.val n
  have hm := Nat.mul_le_mul_left n (Nat.succ_le_of_lt hdiv)
  rw [Nat.mul_succ] at hm
  change n * (n - (i.val/n + 1)) + (n - (i.val%n + 1)) = _
  rw [Nat.mul_sub, Nat.mul_add, Nat.mul_one]
  omega

theorem printedOrder_eq_formula (n : ℕ) (hn : 0 < n) :
    printedOrder n = (List.finRange (n*n)).map (printedCell n hn) := by
  let xs := (List.finRange (n*n)).map (printedCell n hn)
  have hinj : Function.Injective (printedCell n hn) := by
    intro i j he
    have hh := congrArg (key Fin.revPerm) he
    rw [printedCell_key,printedCell_key] at hh
    exact Fin.ext (by have := i.isLt; have := j.isLt; omega)
  have hnd : xs.Nodup := (List.nodup_finRange _).map hinj
  have hfs : xs.toFinset = Finset.univ := by
    ext p
    simp only [Finset.mem_univ, iff_true, List.mem_toFinset, xs, List.mem_map]
    obtain ⟨r,c⟩ := p
    have hmul := Nat.mul_le_mul_left n (Nat.succ_le_of_lt r.isLt)
    have hd := c.rev.isLt
    rw [Nat.mul_succ] at hmul
    let i : Fin (n*n) := ⟨n*r.val+c.rev.val, by omega⟩
    refine ⟨i,List.mem_finRange _,Prod.ext (Fin.ext ?_) ?_⟩
    · change (n*r.val+c.rev.val)/n = r.val
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt c.rev.isLt, Nat.zero_add]
    · change Fin.rev ⟨i.val%n,_⟩ = c
      have hcol : (⟨i.val%n,Nat.mod_lt _ hn⟩ : Fin n) = c.rev := Fin.ext (by
        change (n*r.val+c.rev.val)%n = c.rev.val
        rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt c.rev.isLt])
      rw [hcol, Fin.rev_rev]
  have hp : xs.Pairwise (fun p q => key Fin.revPerm q ≤ key Fin.revPerm p) := by
    rw [List.pairwise_map]
    apply (List.pairwise_lt_finRange _).imp
    intro i j hij
    rw [printedCell_key,printedCell_key]
    exact Nat.sub_le_sub_left (le_of_lt hij) _
  have he := (List.toFinset_sort (r := fun p q => key Fin.revPerm q ≤ key Fin.revPerm p) hnd).mpr hp
  rw [hfs] at he
  exact he

private def sample : Square 4 := rowSwap (Ls 2) 0 1

private def printedClues : Finset (Cell 4) :=
  {(1,0), (1,2), (2,0), (2,1), (3,1), (3,2)}

private def sampleRank (p : Cell 4) : ℕ := p.2.val

private theorem printed_eq_clues : printedGcs sample = printedClues := by
  have hL := (latin_Ls 2).rowSwap 0 1
  have hw : RectWitnesses sample printedClues Fin.revPerm := by
    unfold RectWitnesses
    decide
  have hd : Descends sample printedClues Fin.revPerm sampleRank := by
    unfold Descends
    decide
  obtain ⟨xs,hxs,_⟩ := fills_of_descends hL hd
  exact greedy_eq Fin.revPerm hL (hxs.unique hL) (hw.witnesses hL)

theorem printed_order_counterexample :
    ¬ CompletesTopDown (printedGcs (rowSwap (Ls 2) 0 1)) (rowSwap (Ls 2) 0 1) := by
  change ¬ CompletesTopDown (printedGcs sample) sample
  rw [printed_eq_clues]
  have hzero : (0,0) ∉ printedClues := by decide
  have hnf : ∀ c, ¬ Forced sample printedClues (0,c) := by
    unfold Forced Available
    decide
  generalize printedClues = Q at hzero hnf ⊢
  rintro ⟨xs,hfills,hord⟩
  have hm := hfills.mem_of_missing hzero
  cases hfills with
  | done => simp at hm
  | @step _ p xs _ hf _ =>
    have hr : p.1 = 0 := by
      rcases List.mem_cons.mp hm with h | h
      · exact (congrArg Prod.fst h).symm
      · exact le_antisymm ((List.pairwise_cons.mp hord).1 _ h) (Fin.zero_le _)
    exact hnf p.2 (by simpa only [← hr] using hf)

#check printedOrder_eq_formula
#print axioms printedOrder_eq_formula
#check printed_order_counterexample
#print axioms printed_order_counterexample

end Rowswap
```

### `LatinMasks.lean`

```lean
import LatinXor

namespace Rowswap

def bit (x : Mask s) (i : ℕ) : Bool := x.val.testBit i

def Submask (x y : Mask s) : Prop := ∀ i, bit x i = true → bit y i = true

theorem Submask.le (h : Submask x y) : x ≤ y :=
  Nat.le_of_testBit h

def join (x u : Mask s) : Mask s := ⟨x.val ||| u.val, Nat.or_lt_two_pow x.isLt u.isLt⟩

def full (s : ℕ) : Mask s := ⟨2^s - 1, Nat.sub_lt (Nat.two_pow_pos _) (by decide)⟩

@[simp] theorem bit_join (x u : Mask s) (i : ℕ) :
    bit (join x u) i = (bit x i || bit u i) := Nat.testBit_or _ _ _

@[simp] theorem bit_xor (x u : Mask s) (i : ℕ) :
    bit (xor x u) i = (bit x i ^^ bit u i) := Nat.testBit_xor _ _ _

@[simp] theorem bit_full (s i : ℕ) : bit (full s) i = decide (i < s) :=
  Nat.testBit_two_pow_sub_one _ _

theorem bit_outside (x : Mask s) (hi : s ≤ i) : bit x i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) hi))

theorem bit_ext {x y : Mask s} (h : ∀ i, i < s → bit x i = bit y i) : x = y := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < s
  · exact h i hi
  · exact (bit_outside x (Nat.le_of_not_lt hi)).trans (bit_outside y (Nat.le_of_not_lt hi)).symm

def W (x u : Mask s) : Prop := join x u = full s

instance (x u : Mask s) : Decidable (W x u) := inferInstanceAs (Decidable (join x u = full s))

theorem W_iff (x u : Mask s) :
    W x u ↔ ∀ i, i < s → bit x i = false → bit u i = true := by
  constructor
  · intro h i hi hx
    have hb := congrArg (fun v => bit v i) h
    simpa [hx,hi] using hb
  · intro h
    apply bit_ext
    intro i hi
    cases hx : bit x i with
    | true => simp [hi,hx]
    | false => simp [hi,hx,h i hi hx]

theorem lt_of_submask_of_bit {x y : Mask s} (h : Submask x y) {i : ℕ}
    (hx : bit x i = false) (hy : bit y i = true) : x < y :=
  lt_of_le_of_ne h.le (fun e => by rw [e,hy] at hx; contradiction)

theorem canonical_bits {x u : Mask s} (h : ¬ W x u) :
    ∃ y v, Submask x y ∧ x < y ∧ u < v ∧ W x v ∧ W y u ∧ W y v ∧
      xor x u = xor y v ∧ xor x v = xor y u ∧ Submask u v := by
  have hm : ∃ i, i < s ∧ bit x i = false ∧ bit u i = false := by
    by_contra hn
    apply h
    rw [W_iff]
    intro i hi hx
    cases hu : bit u i
    · exact (hn ⟨i,hi,hx,hu⟩).elim
    · rfl
  let d := xor (full s) (join x u)
  let y := join x d
  let v := join u d
  have hb (i : ℕ) (hi : i < s) : bit d i = !(bit x i || bit u i) := by simp [d,hi]
  obtain ⟨i,hi,hx,hu⟩ := hm
  have hY : Submask x y := fun j hj => by simp [y,hj]
  have hV : Submask u v := fun j hj => by simp [v,hj]
  refine ⟨y,v,hY,lt_of_submask_of_bit hY hx ?_,lt_of_submask_of_bit hV hu ?_,
    (W_iff _ _).mpr ?_, (W_iff _ _).mpr ?_, (W_iff _ _).mpr ?_,
    bit_ext ?_, bit_ext ?_, hV⟩
  · simp [y,hb i hi,hx,hu]
  · simp [v,hb i hi,hx,hu]
  · intro j hj hx'
    cases hu' : bit u j <;> simp [v,hb j hj,hx',hu']
  · intro j hj hy
    cases hx' : bit x j <;> cases hu' : bit u j <;> simp_all [y]
  · intro j hj hy
    cases hx' : bit x j <;> cases hu' : bit u j <;> simp_all [y,v]
  · intro j hj
    cases hx' : bit x j <;> cases hu' : bit u j <;> simp [y,v,hb j hj,hx',hu']
  · intro j hj
    cases hx' : bit x j <;> cases hu' : bit u j <;> simp [y,v,hb j hj,hx',hu']

theorem submask_of_ordinary_arc {x y u v : Mask s}
    (hu : W x u) (hv : W x v) (he : xor x v = xor y u) : Submask y x := by
  intro i hy
  by_cases hn : i < s
  · cases hx : bit x i
    · have hbu := (W_iff _ _).mp hu i hn hx
      have hbv := (W_iff _ _).mp hv i hn hx
      have hb := congrArg (fun a => bit a i) he
      simp [hx,hy,hbu,hbv] at hb
    · rfl
  · rw [bit_outside y (Nat.le_of_not_lt hn)] at hy
    contradiction

/-- The square with named row x placed at physical position pos x. -/
def positioned (pos : Equiv.Perm (Mask s)) : Square (2^s) :=
  fun r c => xor (pos.symm r) c

theorem latin_positioned (pos : Equiv.Perm (Mask s)) : IsLatin (positioned pos) :=
  ⟨fun r => (latin_Ls s).1 (pos.symm r),
    fun c => ((latin_Ls s).2 c).comp pos.symm.bijective⟩

@[simp] theorem positioned_apply (pos : Equiv.Perm (Mask s)) (x u : Mask s) :
    positioned pos (pos x) u = xor x u := by simp [positioned]

def clues (pos : Equiv.Perm (Mask s)) (B : Mask s → Mask s → Prop)
    [∀ x u, Decidable (B x u)] : Finset (Cell (2^s)) :=
  Finset.univ.filter (fun p => ¬ B (pos.symm p.1) p.2)

@[simp] theorem mem_clues (pos : Equiv.Perm (Mask s)) (B : Mask s → Mask s → Prop)
    [∀ x u, Decidable (B x u)] (x u : Mask s) :
    (pos x,u) ∈ clues pos B ↔ ¬ B x u := by simp [clues]

theorem mask_certificate (pos : Equiv.Perm (Mask s)) (B : Mask s → Mask s → Prop)
    [∀ x u, Decidable (B x u)] (rank : Mask s → Mask s → ℕ)
    (hw : ∀ x u, ¬ B x u → ∃ y v, pos x < pos y ∧ u < v ∧
      xor x u = xor y v ∧ xor x v = xor y u ∧ B x v ∧ B y u ∧ B y v)
    (hd : ∀ x y u v, pos x < pos y → u ≠ v → xor x v = xor y u →
      B x u → B x v → B y u → rank x v < rank x u) :
    let L := positioned pos
    TwoCritical (gcs L) L ∧ Strong (gcs L) L ∧ CompletesTopDown (gcs L) L := by
  have hRect : RectWitnesses (positioned pos) (clues pos B) (Equiv.refl _) := by
    intro r u hu
    obtain ⟨x,rfl⟩ := pos.surjective r
    obtain ⟨y,v,hxy,huv,h₁,h₂,h₃,h₄,h₅⟩ := hw x u ((mem_clues pos B x u).mp hu)
    exact ⟨pos y,v,hxy,huv,by simpa using h₁,by simpa using h₂,
      by simpa using h₃,by simpa using h₄,by simpa using h₅⟩
  have hRank : Descends (positioned pos) (clues pos B) (Equiv.refl _)
      (fun p => rank (pos.symm p.1) p.2) := by
    intro r t u v hrt huv hval hu hv ht
    obtain ⟨x,rfl⟩ := pos.surjective r
    obtain ⟨y,rfl⟩ := pos.surjective t
    simpa using hd x y u v hrt huv (by simpa using hval)
      (by simpa using hu) (by simpa using hv) (by simpa using ht)
  exact (certificate (latin_positioned pos) hRect hRank).2

theorem ordinary_masks (pos : Equiv.Perm (Mask s))
    (hpos : ∀ x y, Submask x y → x < y → pos x < pos y) :
    let L := positioned pos
    TwoCritical (gcs L) L ∧ Strong (gcs L) L ∧ CompletesTopDown (gcs L) L := by
  apply mask_certificate pos W (fun _ _ => 0)
  · intro x u hu
    obtain ⟨y,v,hsub,hxy,huv,h₃,h₄,h₅,h₁,h₂,_⟩ := canonical_bits hu
    exact ⟨y,v,hpos x y hsub hxy,huv,h₁,h₂,h₃,h₄,h₅⟩
  · intro x y u v hxy _ he hu hv _
    have hsub := submask_of_ordinary_arc hu hv he
    have hne : y ≠ x := fun e => by subst y; exact (lt_irrefl _) hxy
    exact (not_lt_of_gt (hpos y x hsub (lt_of_le_of_ne hsub.le hne)) hxy).elim

@[simp] theorem positioned_swap (k k' : Mask s) :
    positioned (Equiv.swap k k') = rowSwap (Ls s) k k' := by
  funext r c
  change xor ((Equiv.swap k k').symm r) c = xor (Equiv.swap k k' r) c
  rw [Equiv.symm_swap]

end Rowswap
```

### `LatinOddAdjacent.lean`

```lean
import LatinMasks

namespace Rowswap

/-- Swapping adjacent indices reverses exactly the pair of swapped indices. -/
theorem adjacent_swap_order {a b x y : Fin n} (hab : a.val + 1 = b.val) :
    Equiv.swap a b x < Equiv.swap a b y ↔
      (x < y ∧ ¬ (x = a ∧ y = b)) ∨ (x = b ∧ y = a) := by
  have hab' : a ≠ b := fun h => by rw [h] at hab; omega
  by_cases hxa : x = a <;> by_cases hxb : x = b <;>
    by_cases hya : y = a <;> by_cases hyb : y = b <;>
    simp_all [Equiv.swap_apply_def] <;>
    simp only [Fin.lt_def, Fin.ext_iff] at * <;> omega

theorem ordinary_adjacent {a b : Mask s} (hab : a.val + 1 = b.val)
    (hodd : a.val % 2 = 1) :
    ∀ x y, Submask x y → x < y → Equiv.swap a b x < Equiv.swap a b y := by
  intro x y hs hlt
  apply (adjacent_swap_order hab).mpr
  left
  refine ⟨hlt, ?_⟩
  rintro ⟨rfl,rfl⟩
  have hb := hs 0 (Nat.mod_two_eq_one_iff_testBit_zero.mp hodd)
  have hb' := Nat.mod_two_eq_one_iff_testBit_zero.mpr hb
  omega

theorem conj_6_1_odd_adjacent (s : ℕ) (a b : Fin (2^s))
    (hab : a.val + 1 = b.val) (hodd : a.val % 2 = 1) :
    let L := rowSwap (Ls s) a b
    TwoCritical (gcs L) L ∧ Strong (gcs L) L ∧ CompletesTopDown (gcs L) L := by
  simpa only [positioned_swap] using ordinary_masks (Equiv.swap a b) (ordinary_adjacent hab hodd)

theorem conj_6_1_identity (s : ℕ) (a : Fin (2^s)) :
    let L := rowSwap (Ls s) a a
    TwoCritical (gcs L) L ∧ Strong (gcs L) L ∧ CompletesTopDown (gcs L) L := by
  simpa only [positioned_swap] using ordinary_masks (Equiv.swap a a)
    (fun x y _ h => by simpa only [Equiv.swap_self, Equiv.refl_apply] using h)

#check conj_6_1_odd_adjacent
#check conj_6_1_identity
#print axioms conj_6_1_odd_adjacent
#print axioms conj_6_1_identity

end Rowswap
```

### `LatinPolarBits.lean`

```lean
import LatinOddAdjacent
import Mathlib.Data.Nat.Find

namespace Rowswap

theorem W_mono {x y u : Mask s} (h : Submask x y) (hu : W x u) : W y u := by
  rw [W_iff] at *
  intro i hi hy
  cases hx : bit x i
  · exact hu i hi hx
  · have := h i hx
    simp [hy] at this

theorem bit_equation {x y u v : Mask s} (h : xor x v = xor y u) (i : ℕ) :
    (bit x i ^^ bit v i) = (bit y i ^^ bit u i) := by
  simpa only [bit_xor] using congrArg (fun w => bit w i) h

theorem opposite_diagonal {x y u v : Mask s} (h : xor x v = xor y u) :
    xor x u = xor y v := by
  apply bit_ext
  intro i _
  have hb := bit_equation h i
  simp only [bit_xor]
  revert hb
  cases bit x i <;> cases bit y i <;> cases bit u i <;> cases bit v i <;> decide

def Extra (x z u : Mask s) : Prop :=
  ∀ i, i < s → bit x i = false → bit u i = !bit z i

theorem isExtra {x z u v : Mask s} (huv : xor x v = xor z u) (hv : W x v) : Extra x z u := by
  intro i hi hx
  have hv' := (W_iff _ _).mp hv i hi hx
  have := bit_equation huv i
  cases hz : bit z i <;> cases hu : bit u i <;> simp_all

theorem least_hole (z : Mask s) : ∃ q, q ≤ s ∧
    (∀ i < q, bit z i = true) ∧ (q < s → bit z q = false) := by
  by_cases h : ∃ i, i < s ∧ bit z i = false
  · refine ⟨Nat.find h, (Nat.find_spec h).1.le, ?_, fun _ => (Nat.find_spec h).2⟩
    intro i hi
    cases he : bit z i
    · exact (Nat.find_min h hi ⟨lt_trans hi (Nat.find_spec h).1,he⟩).elim
    · rfl
  · refine ⟨s,le_rfl,?_,fun hn => (lt_irrefl _ hn).elim⟩
    intro i hi
    cases he : bit z i
    · exact (h ⟨i,hi,he⟩).elim
    · rfl

def atom (i : ℕ) (hi : i < s) : Mask s :=
  ⟨2^i,Nat.pow_lt_pow_right (by decide) hi⟩

@[simp] theorem bit_atom {i j : ℕ} {hi : i < s} :
    bit (atom i hi) j = decide (i = j) := Nat.testBit_two_pow

theorem toggles_zero {a z : Mask s} (heven : a.val % 2 = 0) (haz : a.val + 1 = z.val) :
    bit a 0 = false ∧ bit z 0 = true ∧ ∀ i, i ≠ 0 → bit a i = bit z i := by
  have ha := Nat.mod_two_eq_zero_iff_testBit_zero.mp heven
  have hz := Nat.mod_two_eq_one_iff_testBit_zero.mp (show z.val % 2 = 1 by omega)
  refine ⟨ha,hz,?_⟩
  intro i hi
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
  have hdiv : a.val / 2 = z.val / 2 := by omega
  simp [bit,Nat.testBit_succ,hdiv]

theorem zero_submask {a z : Mask s}
    (ha : bit a 0 = false) (hsame : ∀ i, i ≠ 0 → bit a i = bit z i) :
    Submask a z := by
  intro i h
  by_cases hi : i = 0
  · simp [hi,ha] at h
  · rwa [← hsame i hi]

theorem bit_toggle_zero {s : ℕ} (hs : 0 < s) (u : Mask s) :
    bit (xor u (atom 0 hs)) 0 = !bit u 0 ∧
    ∀ i, i ≠ 0 → bit (xor u (atom 0 hs)) i = bit u i := by
  constructor
  · cases hu : bit u 0 <;> simp [hu]
  · intro i hi
    simp [Ne.symm hi]

theorem lt_toggle_zero {u : Mask s} (hs : 0 < s) (hu : bit u 0 = false) :
    u < xor u (atom 0 hs) := by
  obtain ⟨hzero,hsame⟩ := bit_toggle_zero hs u
  have hsub : Submask u (xor u (atom 0 hs)) := by
    intro i hi
    by_cases hn : i = 0
    · simp [hn,hu] at hi
    · rwa [hsame i hn]
  apply lt_of_submask_of_bit hsub hu
  simp [hzero,hu]

/-- A strict increase in the bits above q outweighs any change at q or below. -/
theorem lt_of_increase_above {u v : Mask s} {q : ℕ}
    (hmon : ∀ i, q < i → bit u i = true → bit v i = true)
    (hgain : ∃ i, q < i ∧ bit u i = false ∧ bit v i = true) : u < v := by
  have hle : u.val / 2^(q+1) ≤ v.val / 2^(q+1) := by
    apply Nat.le_of_testBit
    intro i hi
    rw [Nat.testBit_div_two_pow] at hi ⊢
    exact hmon _ (by omega) hi
  obtain ⟨i,hi,hu,hv⟩ := hgain
  have hd : u.val / 2^(q+1) ≠ v.val / 2^(q+1) := by
    intro he
    have hh := congrArg (fun x : ℕ => x.testBit (i-(q+1))) he
    simp only [Nat.testBit_div_two_pow] at hh
    have hh' : i-(q+1) + (q+1) = i := by omega
    rw [hh'] at hh
    change bit u i = bit v i at hh
    simp [hu,hv] at hh
  exact lt_of_not_ge (fun hn => (not_le_of_gt (lt_of_le_of_ne hle hd)) (Nat.div_le_div_right hn))

/-- The column that fills precisely the missing bits of row z, other than q. -/
def modified (z u : Mask s) (q : ℕ) (hq : q < s) : Mask s :=
  xor (join u (xor (full s) z)) (atom q hq)

theorem bit_modified {z u : Mask s} {q i : ℕ} (hq : q < s) (hi : i < s) :
    bit (modified z u q hq) i = ((bit u i || !bit z i) ^^ decide (q=i)) := by
  simp [modified,hi]

theorem and_lt_of_cleared {x u v : Mask s}
    (hmon : ∀ i, bit x i = true → bit v i = true → bit u i = true)
    (hloss : ∃ i, bit x i = true ∧ bit v i = false ∧ bit u i = true) :
    v.val &&& x.val < u.val &&& x.val := by
  apply lt_of_le_of_ne
  · apply Nat.le_of_testBit
    intro i h
    rw [Nat.testBit_and, Bool.and_eq_true] at h ⊢
    exact ⟨hmon i h.2 h.1,h.2⟩
  · obtain ⟨i,hx,hv,hu⟩ := hloss
    intro h
    have hh := congrArg (fun j : ℕ => j.testBit i) h
    change (v.val &&& x.val).testBit i = (u.val &&& x.val).testBit i at hh
    simp only [Nat.testBit_and] at hh
    change (bit v i && bit x i) = (bit u i && bit x i) at hh
    simp [hx,hv,hu] at hh

end Rowswap
```

### `LatinPolar.lean`

```lean
import LatinPolarBits

namespace Rowswap

def Polar (z : Mask s) (q : ℕ) (u : Mask s) : Prop :=
  (bit u 0 = true ∧ W z u) ∨ (bit u 0 = false ∧ q < s ∧ bit u q = false)

def polarity (u : Mask s) : ℕ := (bit u 0).toNat

def expandedRank (x u : Mask s) : ℕ := 2 * (u.val &&& x.val) + polarity u

theorem W_toggle {x u : Mask s} (hx : bit x 0 = true) (hs : 0 < s) :
    W x (xor u (atom 0 hs)) ↔ W x u := by
  simp only [W_iff]
  obtain ⟨_, h⟩ := bit_toggle_zero hs u
  have same (i : ℕ) (hix : bit x i = false) : bit (xor u (atom 0 hs)) i = bit u i :=
    h i (fun hi => by simp [hi,hx] at hix)
  exact ⟨fun h' i hi hix => (same i hix).symm.trans (h' i hi hix),
    fun h' i hi hix => (same i hix).trans (h' i hi hix)⟩

theorem partner_toggle {x z a u v : Mask s} (hs : 0 < s)
    (ha : bit a 0 = false) (hz : bit z 0 = true)
    (hsame : ∀ i, i ≠ 0 → bit a i = bit z i)
    (he : xor x v = xor z u) :
    xor x (xor v (atom 0 hs)) = xor a u := by
  obtain ⟨hv,hvs⟩ := bit_toggle_zero hs v
  apply bit_ext
  intro i _
  have hb := bit_equation he i
  by_cases hi : i = 0
  · subst i
    simp only [bit_xor, hv, ha, hz] at hb ⊢
    revert hb
    cases bit x 0 <;> cases bit v 0 <;> cases bit u 0 <;> decide
  · simpa only [bit_xor,hvs i hi,hsame i hi] using hb

theorem polar_witness {a z u : Mask s} {q : ℕ}
    (ha : bit a 0 = false) (hz : bit z 0 = true)
    (hsame : ∀ i, i ≠ 0 → bit a i = bit z i)
    (hmin : ∀ i < q, bit z i = true) (hmiss : q < s → bit z q = false)
    (hu : ¬ Polar z q u) :
    ∃ y v, u < v ∧ xor z v = xor y u ∧ Polar z q v ∧
      ((y = a ∧ W z u ∧ W z v) ∨ (z < y ∧ Submask z y ∧ W y u ∧ W y v)) := by
  have hs : 0 < s := Nat.pos_of_ne_zero
    (fun e => by have hh := bit_outside z (show s ≤ 0 by omega); simp [hz] at hh)
  by_cases hu0 : bit u 0 = true
  · have hWu : ¬ W z u := fun h => hu (Or.inl ⟨hu0,h⟩)
    obtain ⟨y,v,hsub,hy,huv,hWv,hYu,hYv,_,he,hUV⟩ := canonical_bits hWu
    exact ⟨y,v,huv,he,Or.inl ⟨hUV 0 hu0,hWv⟩,Or.inr ⟨hy,hsub,hYu,hYv⟩⟩
  have hu0' : bit u 0 = false := Bool.eq_false_of_not_eq_true hu0
  by_cases hWu : W z u
  · let v := xor u (atom 0 hs)
    have hv0 : bit v 0 = true := by simp [v,hu0']
    have hWv := (W_toggle hz hs).mpr hWu
    have he := partner_toggle hs ha hz hsame (show xor z u = xor z u from rfl)
    exact ⟨a,v,lt_toggle_zero hs hu0',he,Or.inl ⟨hv0,hWv⟩,Or.inl ⟨rfl,hWu,hWv⟩⟩
  have hm : ∃ i, i < s ∧ bit z i = false ∧ bit u i = false := by
    by_contra hn
    apply hWu
    rw [W_iff]
    intro i hi hx
    cases hh : bit u i
    · exact (hn ⟨i,hi,hx,hh⟩).elim
    · rfl
  obtain ⟨i,hi,hzi,hui⟩ := hm
  have hqi : q ≤ i := by
    by_contra! h
    have := hmin i h
    simp_all
  have hqs : q < s := lt_of_le_of_lt hqi hi
  have hqz := hmiss hqs
  have hq0 : q ≠ 0 := fun e => by rw [e,hz] at hqz; contradiction
  have huq : bit u q = true := by
    cases h : bit u q
    · exact (hu (Or.inr ⟨hu0', hqs,h⟩)).elim
    · rfl
  have hqit : q < i := lt_of_le_of_ne hqi (fun e => by rw [← e,huq] at hui; contradiction)
  let v := modified z u q hqs
  let y := xor z (xor u v)
  have hV (j : ℕ) (hj : j < s) :
      bit v j = ((bit u j || !bit z j) ^^ decide (q=j)) := bit_modified hqs hj
  have hv0 : bit v 0 = false := by simp [hV 0 hs, hq0, hz, hu0']
  have hvq : bit v q = false := by simp [hV q hqs, hqz]
  have hvi : bit v i = true := by simp [hV i hi, ne_of_lt hqit,hzi]
  have huv : u < v := lt_of_increase_above (q := q) (fun j hj hju => by
    by_cases hjs : j < s
    · simp [hV j hjs,ne_of_lt hj,hju]
    · have := bit_outside u (Nat.le_of_not_lt hjs)
      simp [hju] at this) ⟨i,hqit,hui,hvi⟩
  have hY (j : ℕ) : bit y j = (bit z j ^^ (bit u j ^^ bit v j)) := by simp [y]
  have hsub : Submask z y := by
    intro j hz'
    have hj : j < s := by
      by_contra! hn
      rw [bit_outside z hn] at hz'
      contradiction
    have hne : q ≠ j := fun e => by subst j; simp [hqz] at hz'
    cases hu' : bit u j <;> simp [hY,hV j hj,hu',hz',hne]
  have hyi : bit y i = true := by simp [hY,hzi,hui,hvi]
  have hWu' : W y u := (W_iff _ _).mpr (fun j hj hy => by
    by_contra! hn
    have huf := Bool.eq_false_of_not_eq_true hn
    by_cases hne : q = j
    · subst j; simp [huq] at huf
    · cases hz' : bit z j <;> simp [hY,hV j hj, hne, huf,hz'] at hy)
  have hWv' : W y v := (W_iff _ _).mpr (fun j hj hy => by
    by_contra! hn
    have hvf := Bool.eq_false_of_not_eq_true hn
    by_cases hne : q = j
    · subst j; simp [hY,hqz,huq,hvf] at hy
    · cases hz' : bit z j
      · simp [hV j hj, hne,hz'] at hvf
      · simp [hY,hV j hj,hne,hz'] at hy)
  have he : xor z v = xor y u := by
    apply bit_ext
    intro j _
    simp only [hY, bit_xor]
    cases bit z j <;> cases bit u j <;> cases bit v j <;> decide
  exact ⟨y,v,huv,he,Or.inr ⟨hv0,hqs,hvq⟩,
    Or.inr ⟨lt_of_submask_of_bit hsub hzi hyi,hsub,hWu',hWv'⟩⟩

end Rowswap
```

### `LatinPolarArcs.lean`

```lean
import LatinPolar

namespace Rowswap

theorem polar_ordinary_arc {z y u v : Mask s} {q : ℕ} (hz : bit z 0 = true)
    (hmiss : q < s → bit z q = false) (hlt : z < y) (he : xor z v = xor y u)
    (hu : Polar z q u) (hv : Polar z q v) (hy : W y u) :
    polarity v < polarity u := by
  rcases hu with ⟨hu0,hWu⟩ | ⟨hu0,hq,huq⟩ <;>
    rcases hv with ⟨hv0,hWv⟩ | ⟨hv0,_,hvq⟩
  · exact (not_le_of_gt hlt (submask_of_ordinary_arc hWu hWv he).le).elim
  · simp [polarity,hu0,hv0]
  · have hY0 : bit y 0 = false := by
      have hh := bit_equation he 0
      cases h' : bit y 0 <;> simp_all
    have hs : 0 < s := by
      by_contra! hn
      have := bit_outside z hn
      simp_all
    have := (W_iff _ _).mp hy 0 hs hY0
    simp [hu0] at this
  · have hYq : bit y q = false := by
      have hh := bit_equation he q
      cases h' : bit y q <;> simp_all
    have := (W_iff _ _).mp hy q hq hYq
    simp [huq] at this

theorem polar_no_partner {z a u v : Mask s} {q : ℕ}
    (ha : bit a 0 = false) (hz : bit z 0 = true)
    (hsame : ∀ i, i ≠ 0 → bit a i = bit z i)
    (hmiss : q < s → bit z q = false)
    (hu : Polar z q u) (hv : Polar z q v) : xor z v ≠ xor a u := by
  intro he
  have h₀ := bit_equation he 0
  rcases hu with ⟨hu0,hWu⟩ | ⟨hu0,hq,huq⟩ <;>
    rcases hv with ⟨hv0,hWv⟩ | ⟨hv0,hq',hvq⟩
  · simp [ha,hz,hu0,hv0] at h₀
  · have huq := (W_iff _ _).mp hWu q hq' (hmiss hq')
    have hne : q ≠ 0 := fun h => by have hh := hmiss hq'; simp [h,hz] at hh
    have hh := bit_equation he q
    simp [hsame q hne,hmiss hq',huq,hvq] at hh
  · have hvq := (W_iff _ _).mp hWv q hq (hmiss hq)
    have hne : q ≠ 0 := fun h => by have hh := hmiss hq; simp [h,hz] at hh
    have hh := bit_equation he q
    simp [hsame q hne,hmiss hq,huq,hvq] at hh
  · simp [ha,hz,hu0,hv0] at h₀

theorem expanded_same_class {x y u v : Mask s} (he : xor x v = xor y u)
    (hsame : ∀ i, i < s → bit x i = false → bit u i = bit v i) : Submask y x := by
  intro i hy
  have hi : i < s := by
    by_contra! h
    rw [bit_outside y h] at hy
    contradiction
  cases hx : bit x i
  · have hh := bit_equation he i
    rw [hx,hy,hsame i hi hx] at hh
    cases hv : bit v i <;> simp [hv] at hh
  · rfl

theorem expanded_mixed {x y z u v : Mask s} (he : xor x v = xor y u)
    (hxz : Submask x z) (hu : W x u) (hv : Extra x z v) :
    Submask y z ∧ ∀ i, i < s → bit x i = false → bit y i = bit z i := by
  have aux (i : ℕ) (hi : i < s) (hx : bit x i = false) : bit y i = bit z i := by
    have hh := bit_equation he i
    rw [hx,(W_iff _ _).mp hu i hi hx,hv i hi hx] at hh
    revert hh
    cases bit y i <;> cases bit z i <;> decide
  refine ⟨?_,aux⟩
  intro i hy
  cases hx : bit x i
  · have hi : i < s := by
      by_contra! h
      rw [bit_outside y h] at hy
      contradiction
    rwa [aux i hi hx] at hy
  · exact hxz i hx

theorem expanded_smaller {x y z u v : Mask s} (he : xor x v = xor y u)
    (hy : W y u) (hne : y ≠ z)
    (hsub' : Submask y z) (hmatch : ∀ i, i < s → bit x i = false → bit y i = bit z i) :
    expandedRank x v < expandedRank x u := by
  have hm : ∃ i, i < s ∧ bit y i ≠ bit z i := by
    by_contra! h
    exact hne (bit_ext h)
  obtain ⟨i,hi,hbit⟩ := hm
  have hx : bit x i = true := by
    cases hx : bit x i
    · exact (hbit (hmatch i hi hx)).elim
    · rfl
  have hY : bit y i = false := by
    cases h : bit y i
    · rfl
    · exact (hbit (h.trans (hsub' i h).symm)).elim
  have hu := (W_iff _ _).mp hy i hi hY
  have hv : bit v i = false := by
    have hh := bit_equation he i
    cases h : bit v i <;> simp_all
  have hc : v.val &&& x.val < u.val &&& x.val := by
    apply and_lt_of_cleared (fun j hx' hv' => ?_) ⟨i,hx,hv,hu⟩
    by_cases hs : j < s
    · cases hY' : bit y j
      · exact (W_iff _ _).mp hy j hs hY'
      · have hh := bit_equation he j
        cases hU' : bit u j <;> simp_all
    · have := bit_outside x (Nat.le_of_not_lt hs)
      simp_all
  have hr (v : Mask s) : polarity v ≤ 1 := by unfold polarity; cases bit v 0 <;> decide
  unfold expandedRank
  have := hr v
  omega

theorem expanded_polar_smaller {x z u v : Mask s} {q : ℕ}
    (hx : bit x 0 = false) (hZ : bit z 0 = true) (hs : 0 < s)
    (hmiss : q < s → bit z q = false) (hsub : Submask x z)
    (he : xor x v = xor z u) (hu : Polar z q u)
    (hpair : (W x u ∧ Extra x z v) ∨ (Extra x z u ∧ W x v)) :
    expandedRank x v < expandedRank x u := by
  have hEq : v.val &&& x.val = u.val &&& x.val := by
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and]
    change (bit v i && bit x i) = (bit u i && bit x i)
    cases h : bit x i
    · simp
    · have he' := bit_equation he i
      have hz' := hsub i h
      cases hU : bit u i <;> cases hV : bit v i <;> simp_all
  rcases hpair with ⟨hWu,hEx⟩ | ⟨hEx,_⟩
  · have hu0 := (W_iff _ _).mp hWu 0 hs hx
    have hv0 := hEx 0 hs hx
    simp [expandedRank,polarity,hEq,hu0,hv0,hZ]
  · have hu0 := hEx 0 hs hx
    rcases hu with ⟨hU,_⟩ | ⟨_,hq,hU⟩
    · simp [hZ,hu0] at hU
    · have hxq : bit x q = false := by
        cases h : bit x q
        · rfl
        · have := hsub q h; simp [hmiss hq] at this
      have hh := hEx q hq hxq
      simp [hmiss hq,hU] at hh

end Rowswap
```

### `LatinCrossingMasks.lean`

```lean
import LatinPolarArcs

namespace Rowswap

private def crossB (lo p z : Mask s) (q : ℕ) (x u : Mask s) : Prop :=
  if x = z then Polar z q u else if x = p then W z u else
    W x u ∨ (x < lo ∧ bit x 0 = false ∧ Submask x z ∧ Extra x z u)

private def crossRank (z : Mask s) (x u : Mask s) : ℕ :=
  if x = z then polarity u else expandedRank x u

/-- The common polar-mask calculation, including the two crossing distance-two families. -/
theorem polar_masks (pos : Equiv.Perm (Mask s)) (lo hi p z t : Mask s)
    (hpz : p.val + 1 = z.val) (heven : p.val % 2 = 0)
    (hp : lo ≤ p ∧ p ≤ hi) (hz : lo ≤ z ∧ z ≤ hi) (ht : lo ≤ t ∧ t ≤ hi)
    (hparts : ∀ x, lo ≤ x → x ≤ hi → x = p ∨ x = z ∨ x = t)
    (hout : ∀ x y, x < lo ∨ hi < x → (pos x < pos y ↔ x < y))
    (hafter : ∀ x y, x ≤ hi → hi < y → pos x < pos y)
    (hzp : pos z < pos p)
    (hp_local : ∀ y u, p < y → Submask p y → y ≠ z → y ≤ hi →
      ¬ W z u → W y u → ∃ y' v, pos p < pos y' ∧ u < v ∧ xor p v = xor y' u ∧
        W z v ∧ y' ≠ z ∧ W y' u ∧ W y' v)
    (ht_good : ∀ y, t < y → Submask t y → hi < y)
    (hz_good : ∀ y, z < y → Submask z y → hi < y)
    (hp_bad : ∀ y, pos p < pos y → ¬ Submask y z)
    (ht_arc : t ≠ z → ∀ y u v, pos t < pos y → Submask y t → xor t v = xor y u →
      (y = p → W z u) → expandedRank t v < expandedRank t u)
    (hz_bad : ∀ y, pos z < pos y → y ≠ p → y ≠ t → hi < y)
    (ht_polar : pos z < pos t → ∀ q, (∀ i < q, bit z i = true) →
      (q < s → bit z q = false) → ∀ u v, Polar z q u → Polar z q v →
      xor z v ≠ xor t u) :
    let L := positioned pos
    TwoCritical (gcs L) L ∧ Strong (gcs L) L ∧ CompletesTopDown (gcs L) L := by
  classical
  obtain ⟨ha,hz0,hsame⟩ := toggles_zero heven hpz
  obtain ⟨q,_,hmin,hmiss⟩ := least_hole z
  have hpz' : p ≠ z := fun h => by rw [h] at hpz; omega
  have hsub : Submask p z := zero_submask ha hsame
  have hs : 0 < s := by
    by_contra! hn
    have := bit_outside z hn
    simp_all
  have hB (x u : Mask s) (hx : x ≠ z) (hu : W x u) : crossB lo p z q x u := by
    by_cases hxp : x = p
    · subst x
      simpa [crossB,hpz'] using W_mono hsub hu
    · simp [crossB,hx,hxp,hu]
  apply mask_certificate pos (crossB lo p z q) (crossRank z)
  · intro x u hu
    by_cases hxz : x = z
    · subst x
      obtain ⟨y,v,hv,he,hV,hy⟩ :=
        polar_witness ha hz0 hsame hmin hmiss (by simpa [crossB] using hu)
      refine ⟨y,v,?_,hv,opposite_diagonal he,he,by simpa [crossB] using hV,?_⟩
      · rcases hy with ⟨rfl,_,_⟩ | ⟨hy,hsub,_,_⟩
        · exact hzp
        · exact hafter _ _ hz.2 (hz_good y hy hsub)
      · rcases hy with ⟨rfl,hWu,hWv⟩ | ⟨hy,_,hWu,hWv⟩
        · exact ⟨by simpa [crossB,hpz'] using hWu,by simpa [crossB,hpz'] using hWv⟩
        · exact ⟨hB y u (ne_of_gt hy) hWu,hB y v (ne_of_gt hy) hWv⟩
    have hWu : ¬ W x u := fun h => hu (hB x u hxz h)
    obtain ⟨y,v,hXY,hxy,huv,hWv,hYu,hYv,h₁,h₂,hUV⟩ := canonical_bits hWu
    by_cases hyz : y = z
    · subst y
      have hxa : x < lo := by
        by_contra! h
        rcases hparts x h (hxy.le.trans hz.2) with rfl | rfl | rfl
        · exact hu (by simp [crossB,hpz',hYu])
        · exact hxz rfl
        · exact (not_lt_of_ge hz.2 (ht_good _ hxy hXY))
      have hex := isExtra h₂ hWv
      cases hx : bit x 0
      · exact (hu (by simp [crossB,hxz,ne_of_lt (hxa.trans_le hp.1),hxa,hx,hXY,hex])).elim
      · cases hu0 : bit u 0
        · have hv0 : bit v 0 = false := by
            have hb := bit_equation h₂ 0
            cases h : bit v 0 <;> simp_all
          have hvlt := lt_toggle_zero hs hv0
          have he := partner_toggle hs ha hz0 hsame h₂
          have hWv' := (W_toggle hx hs).mpr hWv
          have hZ := (W_toggle hz0 hs).mpr hYv
          refine ⟨p,_,(hout _ _ (Or.inl hxa)).mpr (hxa.trans_le hp.1),
            lt_trans huv hvlt,opposite_diagonal he,he,hB _ _ hxz hWv',?_,?_⟩
          · simpa [crossB,hpz'] using hYu
          · simpa [crossB,hpz'] using hZ
        · refine ⟨z,v,(hout _ _ (Or.inl hxa)).mpr hxy,huv,h₁,h₂,hB _ _ hxz hWv,?_,?_⟩
          · simpa [crossB,Polar,hu0] using hYu
          · simpa [crossB,Polar,hUV 0 hu0] using hYv
    · by_cases hxp : x = p
      · subst x
        have hP := fun h : W z u => hu (by simp [crossB,hpz',h])
        by_cases hyhi : hi < y
        · exact ⟨y,v,hafter _ _ hp.2 hyhi,huv,h₁,h₂,hB _ _ hxz hWv,
            hB _ _ hyz hYu,hB _ _ hyz hYv⟩
        · obtain ⟨y',v',hpos,huv',he',hv',hy'z,hu',hyv'⟩ :=
            hp_local y u hxy hXY hyz (le_of_not_gt hyhi) hP hYu
          exact ⟨y',v',hpos,huv',opposite_diagonal he',he',by simpa [crossB,hpz'] using hv',
            hB _ _ hy'z hu',hB _ _ hy'z hyv'⟩
      have hpos : pos x < pos y := by
        by_cases hx : x < lo ∨ hi < x
        · exact (hout _ _ hx).mpr hxy
        push Not at hx
        rcases hparts x hx.1 hx.2 with rfl | rfl | rfl
        · exact (hxp rfl).elim
        · exact (hxz rfl).elim
        · exact hafter _ _ ht.2 (ht_good y hxy hXY)
      exact ⟨y,v,hpos,huv,h₁,h₂,hB _ _ hxz hWv,hB _ _ hyz hYu,hB _ _ hyz hYv⟩
  · intro x y u v hpos _ he hu hv hy
    by_cases hxz : x = z
    · subst x
      have hU : Polar z q u := by simpa [crossB] using hu
      have hV : Polar z q v := by simpa [crossB] using hv
      have hr : polarity v < polarity u := by
        by_cases hyp : y = p
        · subst y
          exact (polar_no_partner ha hz0 hsame hmiss hU hV he).elim
        by_cases hyt : y = t
        · subst y
          exact (ht_polar hpos q hmin hmiss u v hU hV he).elim
        have hyhi := hz_bad y hpos hyp hyt
        have hzy := hz.2.trans_lt hyhi
        have hly := (hz.1.trans hz.2).trans_lt hyhi
        have hY : W y u := by
          simpa [crossB,ne_of_gt hzy,hyp,not_lt_of_gt hly] using hy
        exact polar_ordinary_arc hz0 hmiss hzy he hU hV hY
      simpa [crossRank] using hr
    by_cases hxp : x = p
    · subst x
      have hU : W z u := by simpa [crossB,hpz'] using hu
      have hV : W z v := by simpa [crossB,hpz'] using hv
      have h : Submask y z := by
        intro i hi
        cases hZ : bit z i
        · have hi' : i < s := by
            by_contra! hn
            rw [bit_outside y hn] at hi
            contradiction
          have hA : bit p i = false := by
            cases hA : bit p i
            · rfl
            · have := hsub i hA
              simp [hZ] at this
          have hh := bit_equation he i
          simp [hA,hi,(W_iff _ _).mp hU i hi' hZ,(W_iff _ _).mp hV i hi' hZ] at hh
        · rfl
      exact (hp_bad y hpos h).elim
    simp only [crossB,hxz,hxp,ite_false] at hu hv
    suffices hRank : expandedRank x v < expandedRank x u by simpa [crossRank,hxz] using hRank
    have ordinaryArc (hsub : Submask y x) : expandedRank x v < expandedRank x u := by
      by_cases hx : x < lo ∨ hi < x
      · exact ((not_le_of_gt ((hout _ _ hx).mp hpos)) hsub.le).elim
      push Not at hx
      rcases hparts x hx.1 hx.2 with rfl | rfl | rfl
      · exact (hxp rfl).elim
      · exact (hxz rfl).elim
      · exact ht_arc hxz y u v hpos hsub he (fun e => by subst y; simpa [crossB,hpz'] using hy)
    have handle (hx : bit x 0 = false) (hXZ : Submask x z)
        (hmix : Submask y z ∧ ∀ i, i < s → bit x i = false → bit y i = bit z i)
        (hpair : (W x u ∧ Extra x z v) ∨ (Extra x z u ∧ W x v)) :
        expandedRank x v < expandedRank x u := by
      by_cases hyz : y = z
      · subst y
        exact expanded_polar_smaller hx hz0 hs hmiss hXZ he (by simpa [crossB] using hy) hpair
      have hY0 : bit y 0 = true := (hmix.2 0 hs hx).trans hz0
      have hyp : y ≠ p := fun e => by simp [e,ha] at hY0
      have hWu : W y u := by simpa [crossB,hyz,hyp,hY0] using hy
      exact expanded_smaller he hWu hyz hmix.1 hmix.2
    rcases hu with hu | ⟨_,hx,hXZ,hu⟩ <;> rcases hv with hv | ⟨_,hx',hXZ',hv⟩
    · exact ordinaryArc (submask_of_ordinary_arc hu hv he)
    · exact handle hx' hXZ' (expanded_mixed he hXZ' hu hv) (Or.inl ⟨hu,hv⟩)
    · exact handle hx hXZ (expanded_mixed (opposite_diagonal he) hXZ hv hu)
        (Or.inr ⟨hu,hv⟩)
    · exact ordinaryArc (expanded_same_class he
        (fun i hi hbit => (hu i hi hbit).trans (hv i hi hbit).symm))

end Rowswap
```

### `LatinEvenAdjacent.lean`

```lean
import LatinCrossingMasks

namespace Rowswap

theorem conj_6_1_even_adjacent (s : ℕ) (a z : Fin (2^s))
    (haz : a.val + 1 = z.val) (heven : a.val % 2 = 0) :
    let L := rowSwap (Ls s) a z
    TwoCritical (gcs L) L ∧ Strong (gcs L) L ∧ CompletesTopDown (gcs L) L := by
  have haz' : a ≤ z := by change a.val ≤ z.val; omega
  rw [← positioned_swap]
  refine polar_masks (Equiv.swap a z) a z a z z haz heven
    ⟨le_rfl,haz'⟩ ⟨haz',le_rfl⟩ ⟨haz',le_rfl⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hlo hhi
    simp only [Fin.ext_iff]
    change a.val ≤ x.val at hlo
    change x.val ≤ z.val at hhi
    omega
  · intro x y hx
    simp only [adjacent_swap_order haz, Fin.lt_def, Fin.ext_iff] at *
    change x.val < a.val ∨ z.val < x.val at hx
    omega
  · intro x y hx hy
    simp only [adjacent_swap_order haz, Fin.lt_def, Fin.ext_iff]
    change x.val ≤ z.val at hx
    change z.val < y.val at hy
    omega
  · exact (adjacent_swap_order haz).mpr (Or.inr ⟨rfl,rfl⟩)
  · intro y _ hy _ hne hh _ _
    exfalso
    change a.val < y.val at hy
    change y.val ≤ z.val at hh
    exact hne (Fin.ext (by omega))
  · intro y hy _
    exact hy
  · intro y hy _
    exact hy
  · intro y hy hsub
    rcases (adjacent_swap_order haz).mp hy with ⟨hlt,hn⟩ | ⟨he,_⟩
    · have hY : y.val ≤ z.val := hsub.le
      change a.val < y.val at hlt
      exact hn ⟨rfl,Fin.ext (by omega)⟩
    · have hne : a.val ≠ z.val := by omega
      exact hne (congrArg Fin.val he)
  · intro h
    exact (h rfl).elim
  · intro y hy hya _
    rcases (adjacent_swap_order haz).mp hy with ⟨h,_⟩ | ⟨_,h⟩
    · exact h
    · exact (hya h).elim
  · intro h
    exact (lt_irrefl _ h).elim

#check conj_6_1_even_adjacent
#print axioms conj_6_1_even_adjacent

end Rowswap
```

### `LatinCrossing.lean`

```lean
import LatinCrossingMasks

namespace Rowswap

theorem distance_two_order {a c x y : Fin n} (hac : a.val + 2 = c.val) :
    Equiv.swap a c x < Equiv.swap a c y ↔
      (x < y ∧ ¬ (a ≤ x ∧ y ≤ c)) ∨ (y < x ∧ a ≤ y ∧ x ≤ c) := by
  have hac' : a ≠ c := fun h => by rw [h] at hac; omega
  by_cases hxa : x = a <;> by_cases hxc : x = c <;>
    by_cases hya : y = a <;> by_cases hyc : y = c <;>
    simp_all [Equiv.swap_apply_def] <;>
    simp only [Fin.lt_def, Fin.le_def, Fin.ext_iff] at * <;> omega

theorem bit_one (x : Mask s) : bit x 1 = decide (x.val / 2 % 2 = 1) := by
  simp [bit,Nat.testBit_succ]

private theorem not_submask {x y : Mask s} (i : ℕ)
    (hx : bit x i = true) (hy : bit y i = false) : ¬ Submask x y :=
  fun h => Bool.noConfusion (hy.symm.trans (h i hx))

theorem conj_6_1_even_crossing (s : ℕ) (a c : Fin (2^s))
    (hac : a.val + 2 = c.val) (hmod : a.val % 4 = 2) :
    let L := rowSwap (Ls s) a c
    TwoCritical (gcs L) L ∧ Strong (gcs L) L ∧ CompletesTopDown (gcs L) L := by
  let z : Mask s := ⟨a.val + 1, by have := c.isLt; omega⟩
  have hz : z.val = a.val + 1 := rfl
  have hac' : a ≤ c := by change a.val ≤ c.val; omega
  have hzc : z ≤ c := by change z.val ≤ c.val; omega
  have haz : a ≤ z := by change a.val ≤ z.val; omega
  have ha1 : bit a 1 = true := by rw [bit_one, decide_eq_true_eq]; omega
  have hz0 : bit z 0 = true := Nat.mod_two_eq_one_iff_testBit_zero.mp (by omega)
  have hc0 : bit c 0 = false := Nat.mod_two_eq_zero_iff_testBit_zero.mp (by omega)
  have hc1 : bit c 1 = false := by rw [bit_one, decide_eq_false_iff_not]; omega
  rw [← positioned_swap]
  refine polar_masks (Equiv.swap a c) a c a z c hz.symm (by omega)
    ⟨le_rfl,hac'⟩ ⟨haz,hzc⟩ ⟨hac',le_rfl⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hlo hhi
    simp only [Fin.ext_iff]
    change a.val ≤ x.val at hlo
    change x.val ≤ c.val at hhi
    omega
  · intro x y hx
    simp only [distance_two_order hac, Fin.lt_def, Fin.le_def] at *
    omega
  · intro x y hx hy
    simp only [distance_two_order hac, Fin.lt_def, Fin.le_def] at *
    omega
  · simp only [distance_two_order hac, Fin.lt_def, Fin.le_def]
    omega
  · intro y _ hy hsub hne hh _ _
    exfalso
    change a.val < y.val at hy
    change y.val ≤ c.val at hh
    have hne' : y.val ≠ z.val := fun e => hne (Fin.ext e)
    have hyc : y = c := Fin.ext (by omega)
    subst y
    exact not_submask 1 ha1 hc1 hsub
  · intro y hy _
    exact hy
  · intro y hy hsub
    change z.val < y.val at hy
    change c.val < y.val
    by_contra! hh
    have hyc : y = c := Fin.ext (by omega)
    subst y
    exact not_submask 0 hz0 hc0 hsub
  · intro y hy hsub
    have hcy : c < y := by
      simp only [distance_two_order hac, Fin.lt_def, Fin.le_def] at hy
      change c.val < y.val
      omega
    exact (not_le_of_gt (hzc.trans_lt hcy)) hsub.le
  · intro _ y _ _ hy hsub _ _
    exfalso
    simp only [distance_two_order hac] at hy
    rcases hy with ⟨hlt,_⟩ | ⟨hlt,hge,_⟩
    · exact (not_le_of_gt hlt) hsub.le
    · have hcase : y = a ∨ y = z := by
        simp only [Fin.lt_def, Fin.le_def, Fin.ext_iff] at *
        omega
      rcases hcase with rfl | rfl
      · exact not_submask 1 ha1 hc1 hsub
      · exact not_submask 0 hz0 hc0 hsub
  · intro y hy hya hyc
    simp only [distance_two_order hac, Fin.lt_def, Fin.le_def] at hy
    have hne' : y.val ≠ a.val := fun e => hya (Fin.ext e)
    have hne'' : y.val ≠ c.val := fun e => hyc (Fin.ext e)
    change c.val < y.val
    omega
  · intro hpos
    exfalso
    simp only [distance_two_order hac, Fin.lt_def, Fin.le_def] at hpos
    omega

theorem conj_6_1_odd_crossing (s : ℕ) (a c : Fin (2^s))
    (hac : a.val + 2 = c.val) (hmod : a.val % 4 = 3) :
    let L := rowSwap (Ls s) a c
    TwoCritical (gcs L) L ∧ Strong (gcs L) L ∧ CompletesTopDown (gcs L) L := by
  let p : Mask s := ⟨a.val + 1, by have := c.isLt; omega⟩
  have hp : p.val = a.val + 1 := rfl
  have hpc : p.val + 1 = c.val := by omega
  have hac' : a ≤ c := by change a.val ≤ c.val; omega
  have hpc' : p ≤ c := by change p.val ≤ c.val; omega
  have hap : a ≤ p := by change a.val ≤ p.val; omega
  have ha0 : bit a 0 = true := Nat.mod_two_eq_one_iff_testBit_zero.mp (by omega)
  have hc0 : bit c 0 = true := Nat.mod_two_eq_one_iff_testBit_zero.mp (by omega)
  have ha1 : bit a 1 = true := by rw [bit_one, decide_eq_true_eq]; omega
  have hp1 : bit p 1 = false := by rw [bit_one, decide_eq_false_iff_not]; omega
  have hc1 : bit c 1 = false := by rw [bit_one, decide_eq_false_iff_not]; omega
  rw [← positioned_swap]
  refine polar_masks (Equiv.swap a c) a c p c a hpc (by omega)
    ⟨hap,hpc'⟩ ⟨hac',le_rfl⟩ ⟨le_rfl,hac'⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hlo hhi
    simp only [Fin.ext_iff]
    change a.val ≤ x.val at hlo
    change x.val ≤ c.val at hhi
    omega
  · intro x y hx
    simp only [distance_two_order hac, Fin.lt_def, Fin.le_def] at *
    omega
  · intro x y hx hy
    simp only [distance_two_order hac, Fin.lt_def, Fin.le_def] at *
    omega
  · simp only [distance_two_order hac, Fin.lt_def, Fin.le_def]
    omega
  · intro y _ hy _ hne hh _ _
    exfalso
    change p.val < y.val at hy
    change y.val ≤ c.val at hh
    have hne' : y.val ≠ c.val := fun e => hne (Fin.ext e)
    omega
  · intro y hy hsub
    change a.val < y.val at hy
    change c.val < y.val
    by_contra! hh
    have he : y = p ∨ y = c := by
      simp only [Fin.ext_iff]
      omega
    rcases he with rfl | rfl
    · exact not_submask 1 ha1 hp1 hsub
    · exact not_submask 1 ha1 hc1 hsub
  · intro y hy _
    exact hy
  · intro y hy hsub
    simp only [distance_two_order hac] at hy
    rcases hy with ⟨hlt,hh⟩ | ⟨hlt,hge,_⟩
    · have hcy : c < y := by simp only [Fin.lt_def, Fin.le_def] at *; omega
      exact (not_le_of_gt hcy) hsub.le
    · have hyA : y = a := by simp only [Fin.lt_def, Fin.le_def, Fin.ext_iff] at *; omega
      subst y
      exact not_submask 1 ha1 hc1 hsub
  · intro _ y _ _ hy hsub _ _
    exfalso
    have hcy : c < y := by
      simp only [distance_two_order hac, Fin.lt_def, Fin.le_def] at hy
      change c.val < y.val
      omega
    exact (not_le_of_gt (hac'.trans_lt hcy)) hsub.le
  · intro y hy hyp hya
    simp only [distance_two_order hac, Fin.lt_def, Fin.le_def] at hy
    have hne' : y.val ≠ a.val := fun e => hya (Fin.ext e)
    have hne'' : y.val ≠ p.val := fun e => hyp (Fin.ext e)
    change c.val < y.val
    omega
  · intro _ q hmin hmiss u v hu hv he
    have hs : 1 < s := by
      by_contra! hn
      have hh := bit_outside a hn
      simp [ha1] at hh
    have hq : q = 1 := by
      by_contra! hn
      by_cases hq' : q = 0
      · subst q
        have hh := hmiss (by omega)
        simp [hc0] at hh
      · have hh := hmin 1 (by omega)
        simp [hc1] at hh
    subst q
    have h₀ := bit_equation he 0
    have h₁ := bit_equation he 1
    rcases hu with ⟨hu0,hU⟩ | ⟨hu0,_,hu1⟩ <;>
      rcases hv with ⟨hv0,hV⟩ | ⟨hv0,_,hv1⟩
    · have hu1 := (W_iff _ _).mp hU 1 hs hc1
      have hv1 := (W_iff _ _).mp hV 1 hs hc1
      simp [hc1,ha1,hu1,hv1] at h₁
    · simp [ha0,hc0,hu0,hv0] at h₀
    · simp [ha0,hc0,hu0,hv0] at h₀
    · simp [hc1,ha1,hu1,hv1] at h₁

#check conj_6_1_even_crossing
#check conj_6_1_odd_crossing
#print axioms conj_6_1_even_crossing
#print axioms conj_6_1_odd_crossing

end Rowswap
```

### `LatinEvenAligned.lean`

```lean
import LatinCrossing

namespace Rowswap

theorem same_high_bits {x y : Mask s} (h : x.val / 4 = y.val / 4) (i : ℕ)
    (hi : 2 ≤ i) : bit x i = bit y i := by
  have h' := congrArg (fun x : ℕ => x.testBit (i-2)) h
  change (x.val / 2^2).testBit (i-2) = (y.val / 2^2).testBit (i-2) at h'
  rw [Nat.testBit_div_two_pow,Nat.testBit_div_two_pow, Nat.sub_add_cancel hi] at h'
  exact h'

theorem conj_6_1_even_aligned (s : ℕ) (a c : Fin (2^s))
    (hac : a.val + 2 = c.val) (hmod : a.val % 4 = 0) :
    let L := rowSwap (Ls s) a c
    TwoCritical (gcs L) L ∧ Strong (gcs L) L ∧ CompletesTopDown (gcs L) L := by
  let z : Mask s := ⟨a.val + 1, by have := c.isLt; omega⟩
  have hz : z.val = a.val + 1 := rfl
  have hac' : a ≤ c := by change a.val ≤ c.val; omega
  have hzc : z ≤ c := by change z.val ≤ c.val; omega
  have haz : a ≤ z := by change a.val ≤ z.val; omega
  have ha0 : bit a 0 = false := Nat.mod_two_eq_zero_iff_testBit_zero.mp (by omega)
  have hz0 : bit z 0 = true := Nat.mod_two_eq_one_iff_testBit_zero.mp (by omega)
  have hc0 : bit c 0 = false := Nat.mod_two_eq_zero_iff_testBit_zero.mp (by omega)
  have ha1 : bit a 1 = false := by rw [bit_one, decide_eq_false_iff_not]; omega
  have hz1 : bit z 1 = false := by rw [bit_one, decide_eq_false_iff_not]; omega
  have hc1 : bit c 1 = true := by rw [bit_one, decide_eq_true_eq]; omega
  have hs : 1 < s := by
    by_contra! hn
    have hh := bit_outside c hn
    simp [hc1] at hh
  have hsameAC : ∀ i, 2 ≤ i → bit a i = bit c i :=
    same_high_bits (by omega)
  have hsameZC : ∀ i, 2 ≤ i → bit z i = bit c i :=
    same_high_bits (by omega)
  rw [← positioned_swap]
  refine polar_masks (Equiv.swap a c) a c a z c hz.symm (by omega)
    ⟨le_rfl,hac'⟩ ⟨haz,hzc⟩ ⟨hac',le_rfl⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hlo hhi
    simp only [Fin.ext_iff]
    change a.val ≤ x.val at hlo
    change x.val ≤ c.val at hhi
    omega
  · intro x y hx
    simp only [distance_two_order hac, Fin.lt_def, Fin.le_def] at *
    omega
  · intro x y hx hy
    simp only [distance_two_order hac, Fin.lt_def, Fin.le_def] at *
    omega
  · simp only [distance_two_order hac, Fin.lt_def, Fin.le_def]
    omega
  · intro y u hy _ hne hh hUZ hu
    change a.val < y.val at hy
    change y.val ≤ c.val at hh
    have hne' : y.val ≠ z.val := fun e => hne (Fin.ext e)
    have hyc : y = c := Fin.ext (by omega)
    subst y
    have hu1 : bit u 1 = false := by
      cases h1 : bit u 1
      · rfl
      · exfalso
        apply hUZ
        apply (W_iff _ _).mpr
        intro i hi hZi
        rcases (show i = 0 ∨ i = 1 ∨ 2 ≤ i by omega) with rfl | rfl | hhigh
        · simp [hz0] at hZi
        · exact h1
        · exact (W_iff _ _).mp hu i hi (by rwa [← hsameZC i hhigh])
    have hS : 0 < s := by omega
    let d := xor c (atom 0 hS)
    let v := xor (xor u (atom 0 hS)) (atom 1 hs)
    have hd0 : bit d 0 = true := by simp [d,hc0]
    have hdhi (i : ℕ) (hi : i ≠ 0) : bit d i = bit c i :=
      (bit_toggle_zero hS c).2 i hi
    have hv0 : bit v 0 = !bit u 0 := by
      cases h : bit u 0 <;> simp [v,h]
    have hv1 : bit v 1 = true := by simp [v,hu1]
    have hvhi (i : ℕ) (hi : 2 ≤ i) : bit v i = bit u i := by
      have h0 : 0 ≠ i := by omega
      have h1 : 1 ≠ i := by omega
      simp [v,h0,h1]
    have hcd : c < d := lt_toggle_zero hS hc0
    have hpos : Equiv.swap a c a < Equiv.swap a c d :=
      (distance_two_order hac).mpr (Or.inl ⟨hac'.trans_lt hcd,fun h => (not_le_of_gt hcd) h.2⟩)
    have hlt : u < v := lt_of_increase_above (q := 0) (fun i hi hi' => by
      rcases (show i = 1 ∨ 2 ≤ i by omega) with rfl | h
      · exact hv1
      · rwa [hvhi i h]) ⟨1,by decide,hu1,hv1⟩
    have hd1 : bit d 1 = true := (hdhi 1 (by decide)).trans hc1
    have huD : W d u := by
      rw [W_iff]
      intro i hi hbit
      by_cases hi0 : i = 0
      · simp [hi0,hd0] at hbit
      · exact (W_iff _ _).mp hu i hi (by rwa [← hdhi i hi0])
    refine ⟨d,v,hpos,hlt,bit_ext ?_,(W_iff _ _).mpr ?_,
      ne_of_gt (hzc.trans_lt hcd),huD,(W_iff _ _).mpr ?_⟩
    · intro i _
      simp only [bit_xor]
      rcases (show i = 0 ∨ i = 1 ∨ 2 ≤ i by omega) with rfl | rfl | h
      · cases hu' : bit u 0 <;> simp [ha0,hd0,hv0,hu']
      · simp [ha1,hd1,hv1,hu1]
      · rw [hsameAC i h, hdhi i (by omega), hvhi i h]
    · intro i hi hbit
      rcases (show i = 0 ∨ i = 1 ∨ 2 ≤ i by omega) with rfl | rfl | h
      · simp [hz0] at hbit
      · exact hv1
      · rw [hvhi i h]
        exact (W_iff _ _).mp hu i hi (by rwa [← hsameZC i h])
    · intro i hi hbit
      rcases (show i = 0 ∨ i = 1 ∨ 2 ≤ i by omega) with rfl | rfl | h
      · simp [hd0] at hbit
      · simp [hd1] at hbit
      · rw [hvhi i h]
        exact (W_iff _ _).mp huD i hi hbit
  · intro y hy _
    exact hy
  · intro y hy hsub
    change z.val < y.val at hy
    change c.val < y.val
    by_contra! hh
    have hyc : y = c := Fin.ext (by omega)
    subst y
    have := hsub 0 hz0
    simp [hc0] at this
  · intro y hy hsub
    have hcy : c < y := by
      simp only [distance_two_order hac, Fin.lt_def, Fin.le_def] at hy
      change c.val < y.val
      omega
    exact (not_le_of_gt (hzc.trans_lt hcy)) hsub.le
  · intro _ y u v hy hsub he hu
    simp only [distance_two_order hac] at hy
    rcases hy with ⟨hlt,_⟩ | ⟨hlt,hge,_⟩
    · exact ((not_le_of_gt hlt) hsub.le).elim
    · have hcase : y = a ∨ y = z := by
        simp only [Fin.lt_def, Fin.le_def, Fin.ext_iff] at *
        omega
      rcases hcase with rfl | rfl
      · have hu1 := (W_iff _ _).mp (hu rfl) 1 hs hz1
        have hv1 : bit v 1 = false := by
          have hh := bit_equation he 1
          cases hv : bit v 1 <;> simp_all
        have hsame (i : ℕ) (h : i ≠ 1) : bit v i = bit u i := by
          have hh := bit_equation he i
          by_cases h0 : i = 0
          · subst i; simpa [ha0,hc0] using hh
          · rw [hsameAC i (by omega)] at hh
            revert hh
            cases bit c i <;> cases bit v i <;> cases bit u i <;> decide
        have ht := and_lt_of_cleared (x := c) (u := u) (v := v) (fun i _ hv => by
          by_cases h : i = 1
          · simp [h,hv1] at hv
          · rwa [← hsame i h]) ⟨1,hc1,hv1,hu1⟩
        have hvle : polarity v ≤ 1 := by unfold polarity; cases bit v 0 <;> decide
        unfold expandedRank
        omega
      · have := hsub 0 hz0
        simp [hc0] at this
  · intro y hy hya hyc
    simp only [distance_two_order hac, Fin.lt_def, Fin.le_def] at hy
    have hne' : y.val ≠ a.val := fun e => hya (Fin.ext e)
    have hne'' : y.val ≠ c.val := fun e => hyc (Fin.ext e)
    change c.val < y.val
    omega
  · intro hpos
    exfalso
    simp only [distance_two_order hac, Fin.lt_def, Fin.le_def] at hpos
    omega

#check conj_6_1_even_aligned
#print axioms conj_6_1_even_aligned

end Rowswap
```

### `LatinQuarters.lean`

```lean
import LatinEvenAligned

namespace Rowswap

def low (x : Mask s) : ℕ := x.val % 4
def high (x : Mask s) : ℕ := x.val / 4

theorem low_lt (x : Mask s) : low x < 4 := Nat.mod_lt _ (by decide)

theorem low_eq (x y : Mask s) (hh : high x = high y) (hl : low x = low y) : x = y := by
  apply Fin.ext
  unfold low at hl
  unfold high at hh
  omega

theorem low_xor (x y : Mask s) : low (xor x y) = low x ^^^ low y :=
  Nat.xor_mod_two_pow (n := 2)

theorem high_xor (x y : Mask s) : high (xor x y) = high x ^^^ high y :=
  Nat.xor_div_two_pow (n := 2)

theorem bit_low (x : Mask s) (i : ℕ) (hi : i < 2) :
    (low x).testBit i = bit x i := by
  change (x.val % 2^2).testBit i = x.val.testBit i
  rw [Nat.testBit_mod_two_pow]
  simp [hi]

theorem low_order {x y : Mask s} (hh : high x ≤ high y) (hl : low x < low y) : x < y := by
  change x.val < y.val
  unfold high at hh
  unfold low at hl
  omega

theorem high_order {x y : Mask s} (hh : high x < high y) : x < y := by
  change x.val < y.val
  unfold high at hh
  omega

theorem high_bit (x : Mask s) (i : ℕ) : (high x).testBit i = bit x (i+2) := by
  exact Nat.testBit_div_two_pow (n := 2) _ _

theorem high_compare {x y : Mask s}
    (h : ∀ i, 2 ≤ i → bit x i = true → bit y i = true) : high x ≤ high y := by
  apply Nat.le_of_testBit
  intro i hi
  rw [high_bit] at hi ⊢
  exact h _ (by omega) hi

theorem high_strict {x y : Mask s}
    (h : ∀ i, 2 ≤ i → bit x i = true → bit y i = true)
    (h' : ∃ i, 2 ≤ i ∧ bit x i = false ∧ bit y i = true) : high x < high y := by
  apply lt_of_le_of_ne (high_compare h)
  obtain ⟨i,hi,hx,hy⟩ := h'
  intro he
  have hb := same_high_bits he i hi
  simp [hx,hy] at hb

def putLow (hs : 1 < s) (x : Mask s) (j : ℕ) (hj : j < 4) : Mask s :=
  xor (xor x ⟨low x, lt_of_lt_of_le (low_lt x) (Nat.pow_le_pow_right (show 0 < (2:ℕ) by decide) hs)⟩)
    ⟨j, lt_of_lt_of_le hj (Nat.pow_le_pow_right (show 0 < (2:ℕ) by decide) hs)⟩

@[simp] theorem low_putLow (hs : 1 < s) (x : Mask s) (j : ℕ) (hj : j < 4) :
    low (putLow hs x j hj) = j := by
  simp only [putLow,low_xor]
  change (low x ^^^ (low x % 4)) ^^^ (j % 4) = j
  rw [Nat.mod_eq_of_lt (low_lt x),Nat.mod_eq_of_lt hj,Nat.xor_self,Nat.zero_xor]

@[simp] theorem high_putLow (hs : 1 < s) (x : Mask s) (j : ℕ) (hj : j < 4) :
    high (putLow hs x j hj) = high x := by
  simp only [putLow,high_xor]
  change (high x ^^^ (low x / 4)) ^^^ (j / 4) = high x
  simp [Nat.div_eq_of_lt (low_lt x),Nat.div_eq_of_lt hj]

def WH (x u : Mask s) : Prop := ∀ i, 2 ≤ i → i < s → bit x i = false → bit u i = true

def WL (x u : ℕ) : Prop := x ||| u = 3

theorem WH_putLow (hs : 1 < s) (x y : Mask s) (j : ℕ) (hj : j < 4) :
    WH x (putLow hs y j hj) ↔ WH x y := by
  unfold WH
  have hh := same_high_bits (high_putLow hs y j hj)
  exact ⟨fun h i hi hS hx => (hh i hi).symm.trans (h i hi hS hx),
    fun h i hi hS hx => (hh i hi).trans (h i hi hS hx)⟩

theorem W_high_low (hs : 1 < s) (x u : Mask s) : W x u ↔ WH x u ∧ WL (low x) (low u) := by
  rw [W_iff]
  have hl : WL (low x) (low u) ↔
      ∀ i < 2, bit x i = false → bit u i = true := by
    unfold WL
    constructor
    · intro he i hi hx
      have h := congrArg (fun w : ℕ => w.testBit i) he
      rw [Nat.testBit_or, bit_low _ _ hi, bit_low _ _ hi, hx,
        show (3 : ℕ) = 2^2-1 from rfl, Nat.testBit_two_pow_sub_one] at h
      simpa [hi] using h
    · intro h
      apply Nat.eq_of_testBit_eq
      intro i
      by_cases hi : i < 2
      · simp only [Nat.testBit_or,bit_low _ _ hi,show (3:ℕ) = 2^2-1 from rfl,
          Nat.testBit_two_pow_sub_one,hi,decide_true]
        cases h' : bit x i <;> simp [h',h i hi]
      · have hx := Nat.testBit_lt_two_pow
          (lt_of_lt_of_le (low_lt x) (Nat.pow_le_pow_right (show 0 < (2:ℕ) by decide) (Nat.le_of_not_lt hi)))
        have hu := Nat.testBit_lt_two_pow
          (lt_of_lt_of_le (low_lt u) (Nat.pow_le_pow_right (show 0 < (2:ℕ) by decide) (Nat.le_of_not_lt hi)))
        rw [show (3:ℕ) = 2^2-1 from rfl, Nat.testBit_two_pow_sub_one]
        simp [hx,hu,hi]
  rw [hl]
  exact ⟨fun h => ⟨fun i _ hi => h i hi,fun i hi => h i (by omega)⟩,
    fun ⟨hH,hL⟩ i hi => if h : i < 2 then hL i h else hH i (by omega) hi⟩

def highJoin (x u : Mask s) : Mask s := join u (xor (full s) x)

theorem highJoin_bit (x u : Mask s) (i : ℕ) (hi : i < s) :
    bit (highJoin x u) i = (bit u i || !bit x i) := by simp [highJoin,hi]

theorem high_eq_of_bits {x y : Mask s} (h : ∀ i, 2 ≤ i → i < s → bit x i = bit y i) :
    high x = high y := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [high_bit,high_bit]
  by_cases hi : i+2 < s
  · exact h _ (by omega) hi
  · simp [bit_outside x (Nat.le_of_not_lt hi),bit_outside y (Nat.le_of_not_lt hi)]

def mate (x u v : Mask s) : Mask s := xor x (xor u v)

theorem mate_eq (x u v : Mask s) : xor x v = xor (mate x u v) u := by
  apply Fin.ext
  simp [mate,Nat.xor_comm u.val v.val,Nat.xor_assoc]

theorem mate_unique {x u v y : Mask s} (he : xor x v = xor y u) : y = mate x u v := by
  apply (xor_involutive u).injective
  rw [xor_comm u y, xor_comm u (mate x u v), ← mate_eq, he]

theorem low_mate (x u v : Mask s) : low (mate x u v) = low x ^^^ (low u ^^^ low v) := by
  simp only [mate,low_xor]

theorem high_mate (x u v : Mask s) : high (mate x u v) = high x ^^^ (high u ^^^ high v) := by
  simp only [mate,high_xor]

def highIntersect (x u : Mask s) : ℕ := high x &&& high u

theorem highIntersect_lt {x u v : Mask s}
    (hmon : ∀ i, 2 ≤ i → bit x i = true → bit v i = true → bit u i = true)
    (hloss : ∃ i, 2 ≤ i ∧ bit x i = true ∧ bit v i = false ∧ bit u i = true) :
    highIntersect x v < highIntersect x u := by
  apply lt_of_le_of_ne
  · apply Nat.le_of_testBit
    intro i h
    simp only [highIntersect,Nat.testBit_and, Bool.and_eq_true, high_bit] at h ⊢
    exact ⟨h.1,hmon _ (by omega) h.1 h.2⟩
  · obtain ⟨i,hi,hx,hv,hu⟩ := hloss
    intro h
    have hh := congrArg (fun q : ℕ => q.testBit (i-2)) h
    simp [highIntersect,high_bit,Nat.sub_add_cancel hi,hx,hv,hu] at hh

theorem wh_displacement {x u v : Mask s} (h : ∀ i, 2 ≤ i → i < s →
    (bit x i = true → bit v i = bit u i) ∧
    (bit x i = false → bit u i = true ∨ bit v i = true))
    (hg : ∃ i, 2 ≤ i ∧ i < s ∧ bit x i = false ∧ bit u i ≠ bit v i) :
    high x < high (mate x u v) ∧ WH (mate x u v) u ∧ WH (mate x u v) v := by
  have hY (i : ℕ) : bit (mate x u v) i = (bit x i ^^ (bit u i ^^ bit v i)) := by
    simp [mate]
  refine ⟨high_strict ?_ ?_,?_,?_⟩
  · intro i hi hx
    have hS : i < s := by
      by_contra! hn
      rw [bit_outside x hn] at hx
      contradiction
    simp [hY,hx,(h i hi hS).1 hx]
  · obtain ⟨i,hi,hS,hx,hd⟩ := hg
    refine ⟨i,hi,hx,?_⟩
    cases hU : bit u i <;> cases hV : bit v i <;> simp_all
  · intro i hi hS hy
    cases hx : bit x i
    · rcases (h i hi hS).2 hx with hU | hV
      · exact hU
      · cases hU : bit u i <;> simp_all
    · simp [hY,hx,(h i hi hS).1 hx] at hy
  · intro i hi hS hy
    cases hx : bit x i
    · rcases (h i hi hS).2 hx with hU | hV
      · cases hV : bit v i <;> simp_all
      · exact hV
    · simp [hY,hx,(h i hi hS).1 hx] at hy

end Rowswap
```

### `LatinLowCases.lean`

```lean
import LatinQuarters

namespace Rowswap

def coverLow (r u : ℕ) : Prop :=
  r = 1 ∨ (r = 2 ∧ 2 ≤ u) ∨ (r = 3 ∧ (u = 0 ∨ u = 3))

def extraLow (r u : ℕ) : Prop :=
  (r = 2 ∧ u < 2) ∨ (r = 3 ∧ (u = 1 ∨ u = 2))

def specialRank (r u : ℕ) : ℕ :=
  if r = 2 then u / 2 else u / 2 + u % 2

def lowRank (u : ℕ) : ℕ :=
  if u = 3 then 3 else if u = 0 then 2 else if u = 2 then 1 else 0

def lowSubset (x y : ℕ) : Prop := x &&& y = x
def lowPattern (x y u : ℕ) : Prop := u &&& (3 ^^^ x) = (3 ^^^ y)

instance (x u : ℕ) : Decidable (WL x u) := inferInstanceAs (Decidable (x ||| u = 3))
instance (r u : ℕ) : Decidable (coverLow r u) :=
  inferInstanceAs (Decidable (r = 1 ∨ (r = 2 ∧ 2 ≤ u) ∨ (r = 3 ∧ (u = 0 ∨ u = 3))))
instance (r u : ℕ) : Decidable (extraLow r u) :=
  inferInstanceAs (Decidable ((r = 2 ∧ u < 2) ∨ (r = 3 ∧ (u = 1 ∨ u = 2))))
instance (x y : ℕ) : Decidable (lowSubset x y) := inferInstanceAs (Decidable (x &&& y = x))
instance (x y u : ℕ) : Decidable (lowPattern x y u) :=
  inferInstanceAs (Decidable (u &&& (3 ^^^ x) = (3 ^^^ y)))

theorem cover_or_extra : ∀ (r u : Fin 4), 0 < r.val → coverLow r u ∨ extraLow r u := by decide


theorem local_clue : ∀ (r u : Fin 4), 0 < r.val → ¬ coverLow r u →
    ∃ t v : Fin 4, 0 < t.val ∧ t.val < r.val ∧ u.val < v.val ∧
      r.val ^^^ v.val = t.val ^^^ u.val ∧ coverLow r v ∧ coverLow t u ∧ coverLow t v := by
  decide

theorem local_union : ∀ (r u : Fin 4), 0 < r.val →
    let v := u.val ||| (3 ^^^ r.val)
    let y := r.val ^^^ (u.val ^^^ v)
    v < 4 ∧ WL y u ∧ WL y v ∧ (coverLow r u → coverLow r v) ∧
    (extraLow r u → extraLow r v) := by
  decide

theorem local_cover_arc : ∀ (r t u v : Fin 4), 0 < t.val → t.val < r.val →
    r.val ^^^ v.val = t.val ^^^ u.val → coverLow r u → coverLow r v →
    ¬ coverLow t u := by decide

theorem local_extra_arc : ∀ (r t u v : Fin 4), 0 < t.val → t.val < r.val →
    r.val ^^^ v.val = t.val ^^^ u.val → extraLow r u → extraLow r v →
    ¬ extraLow t u := by decide

theorem local_outer_arc : ∀ (r t u v : Fin 4), 0 < r.val →
    r.val ^^^ v.val = t.val ^^^ u.val → WL t u →
    ((coverLow r u ∧ extraLow r v) ∨ (extraLow r u ∧ coverLow r v)) →
    specialRank r v < specialRank r u := by decide

theorem local_canonical : ∀ (x y u v : Fin 4),
    (y.val = 2 ∨ y.val = 3) → lowSubset x y → lowPattern x y u →
    x.val ^^^ v.val = y.val ^^^ u.val →
    (x.val = 0 ∧ y.val = 2) ∨ (x.val = 1 ∧ y.val = 3) ∨
    (coverLow y u ∧ coverLow y v) ∨
    (y.val = 2 ∧ x.val = 2 ∧ u.val = 1) ∨ (y.val = 3 ∧ 2 ≤ x.val) := by
  have hc : ∀ (x y u v : Fin 4), ¬ (
      (y.val = 2 ∨ y.val = 3) ∧ lowSubset x y ∧ lowPattern x y u ∧
      x.val ^^^ v.val = y.val ^^^ u.val ∧
      ¬ ((x.val = 0 ∧ y.val = 2) ∨ (x.val = 1 ∧ y.val = 3) ∨
      (coverLow y u ∧ coverLow y v) ∨
      (y.val = 2 ∧ x.val = 2 ∧ u.val = 1) ∨ (y.val = 3 ∧ 2 ≤ x.val))) := by decide
  intro x y u v hy hsub hpat he
  by_contra hn
  exact hc x y u v ⟨hy,hsub,hpat,he,hn⟩

theorem local_reroute_a : ∀ (x u : Fin 4), 2 ≤ x.val → lowPattern x 3 u →
    let v := x.val ^^^ u.val ^^^ 1
    v < 4 ∧ WL x v ∧ x.val ^^^ v = 1 ^^^ u.val := by decide

theorem local_expanded : ∀ (x t y u v : Fin 4),
    ((x.val = 0 ∧ t.val = 2) ∨ (x.val = 1 ∧ t.val = 3)) →
    x.val ^^^ v.val = y.val ^^^ u.val →
    ((WL x u ∧ lowPattern x t v) ∨ (lowPattern x t u ∧ WL x v)) →
    (y.val = 2 ∨ y.val = 3) ∧
    (coverLow y u → lowRank v < lowRank u) := by decide

theorem lowSubset_of_submask {x y : Mask s} (h : Submask x y) : lowSubset (low x) (low y) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < 2
  · rw [bit_low _ _ hi,bit_low _ _ hi]
    cases hx : bit x i
    · rfl
    · simp [h i hx]
  · have hh : (low x).testBit i = false := Nat.testBit_lt_two_pow
      (lt_of_lt_of_le (low_lt x) (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (le_of_not_gt hi)))
    simp [hh]

theorem lowPattern_iff {x y u : Mask s} (_hs : 1 < s) (hsub : Submask x y) :
    lowPattern (low x) (low y) (low u) ↔
      ∀ i < 2, bit x i = false → bit u i = !bit y i := by
  unfold lowPattern
  have hh (i : ℕ) (hi : i < 2) : (3 : ℕ).testBit i = true := by
    rw [show (3:ℕ) = 2^2-1 from rfl, Nat.testBit_two_pow_sub_one]; simp [hi]
  constructor
  · intro h i hi hx
    have he := congrArg (fun a : ℕ => a.testBit i) h
    rw [Nat.testBit_and,Nat.testBit_xor,Nat.testBit_xor,hh i hi,
      bit_low _ _ hi,bit_low _ _ hi,bit_low _ _ hi,hx] at he
    simpa using he
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and,Nat.testBit_xor,Nat.testBit_xor]
    by_cases hi : i < 2
    · rw [hh i hi,bit_low _ _ hi,bit_low _ _ hi,bit_low _ _ hi]
      cases hx : bit x i
      · simp [h i hi hx]
      · simp [hsub i hx]
    · have hf (w : Mask s) : (low w).testBit i = false := Nat.testBit_lt_two_pow
        (lt_of_lt_of_le (low_lt _) (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (le_of_not_gt hi)))
      rw [show (3:ℕ) = 2^2-1 from rfl, Nat.testBit_two_pow_sub_one]
      simp [hf,hi]

theorem extra_lowPattern {x y u : Mask s} (_hs : 1 < s) (hsub : Submask x y)
    (h : Extra x y u) : lowPattern (low x) (low y) (low u) :=
  (lowPattern_iff _hs hsub).mpr (fun i hi => h i (by omega))

end Rowswap
```

### `LatinOddMasks.lean`

```lean
import LatinLowCases

namespace Rowswap

/-- The three swapped-block rows in the aligned odd-start case. -/
structure Quarter (s : ℕ) where
  a : Mask s
  b : Mask s
  c : Mask s
  ha : low a = 1
  hb : low b = 2
  hc : low c = 3
  hA : high a = high c
  hB : high b = high c

namespace Quarter

variable (Q : Quarter s)

def Inside (x : Mask s) : Prop := high x = high Q.c ∧ 0 < low x
instance (x : Mask s) : Decidable (Q.Inside x) :=
  inferInstanceAs (Decidable (high x = high Q.c ∧ 0 < low x))

theorem a_inside : Q.Inside Q.a := ⟨Q.hA, by rw [Q.ha]; decide⟩
theorem b_inside : Q.Inside Q.b := ⟨Q.hB, by rw [Q.hb]; decide⟩
theorem c_inside : Q.Inside Q.c := ⟨rfl, by rw [Q.hc]; decide⟩
theorem c_after_a : Q.a.val + 2 = Q.c.val := by
  have := Q.ha
  have := Q.hc
  have := Q.hA
  unfold low high at *
  omega

theorem inside_iff {x : Mask s} : Q.Inside x ↔ Q.a ≤ x ∧ x ≤ Q.c := by
  have ha := Q.ha
  have hc := Q.hc
  have hA := Q.hA
  simp only [Inside,low,high,Fin.le_def] at *
  omega

def pos : Equiv.Perm (Mask s) := Equiv.swap Q.a Q.c

theorem later {x y : Mask s} : Q.pos x < Q.pos y ↔
    (x < y ∧ ¬ (Q.Inside x ∧ Q.Inside y)) ∨
      (Q.Inside x ∧ Q.Inside y ∧ low y < low x) := by
  unfold pos
  rw [distance_two_order Q.c_after_a]
  simp only [Q.inside_iff,Fin.lt_def,Fin.le_def,low]
  have ha := Q.ha
  have hc := Q.hc
  have hA := Q.hA
  unfold low high at *
  omega

theorem later_high {x y : Mask s} (h : high x < high y) : Q.pos x < Q.pos y :=
  Q.later.mpr (Or.inl ⟨high_order h, fun h' => by
    have he := h'.1.1.trans h'.2.1.symm
    exact (ne_of_lt h) he⟩)

theorem later_inside {x y : Mask s} (hx : Q.Inside x) (hy : Q.Inside y) (h : low y < low x) :
    Q.pos x < Q.pos y := Q.later.mpr (Or.inr ⟨hx,hy,h⟩)

theorem later_special {x y : Mask s} (hx : Q.Inside x) (h : Q.pos x < Q.pos y) :
    high Q.c < high y ∨ (Q.Inside y ∧ low y < low x) := by
  rcases Q.later.mp h with ⟨hlt,hn⟩ | ⟨_,hy,hl⟩
  · left
    have hh := hx.1
    have hne : ¬ Q.Inside y := fun hy => hn ⟨hx,hy⟩
    have hL := hx.2
    have hU := low_lt x
    simp only [Inside,Fin.lt_def,high,low] at *
    omega
  · exact Or.inr ⟨hy,hl⟩

theorem s_two (Q : Quarter s) : 1 < s := by
  have hh := Q.hc
  have hc := Q.c.isLt
  unfold low at hh
  by_contra! hs
  interval_cases s <;> omega

theorem high_blank {x u : Mask s} (hx : Q.Inside x) : WH x u ↔ WH Q.c u := by
  simp only [WH]
  constructor <;> intro h i hi hS hz <;> apply h i hi hS
  · rwa [same_high_bits hx.1 i hi]
  · rwa [← same_high_bits hx.1 i hi]

def Special (q : ℕ) (x u : Mask s) : Prop :=
  (WH Q.c u ∧ coverLow (low x) (low u)) ∨
    (q < s ∧ bit u q = false ∧ extraLow (low x) (low u))

def Earlier (x t : Mask s) : Prop :=
  x < Q.a ∧ ((low x = 0 ∧ t = Q.b) ∨ (low x = 1 ∧ t = Q.c)) ∧ Submask x t

def blanks (q : ℕ) (x u : Mask s) : Prop :=
  if Q.Inside x then Q.Special q x u else W x u ∨ ∃ t, Q.Earlier x t ∧ Extra x t u

def rank (x u : Mask s) : ℕ :=
  if Q.Inside x then specialRank (low x) (low u) else
    4 * highIntersect x u + lowRank (low u)

theorem blank_inside {q : ℕ} {x u : Mask s} (hx : Q.Inside x) :
    Q.blanks q x u ↔ Q.Special q x u := by simp [blanks,hx]

theorem blank_outside {q : ℕ} {x u : Mask s} (hx : ¬ Q.Inside x) :
    Q.blanks q x u ↔ W x u ∨ ∃ t, Q.Earlier x t ∧ Extra x t u := by simp [blanks,hx]

theorem blank_ordinary {q : ℕ} {x u : Mask s} (hx : ¬ Q.Inside x) (hw : W x u) :
    Q.blanks q x u := (Q.blank_outside hx).mpr (Or.inl hw)

theorem blank_a {q : ℕ} {u : Mask s} (h : WH Q.c u) : Q.blanks q Q.a u :=
  (Q.blank_inside Q.a_inside).mpr (Or.inl ⟨h,Or.inl Q.ha⟩)

theorem no_inside_high {x : Mask s} (h : high x ≠ high Q.c) : ¬ Q.Inside x :=
  fun hx => h hx.1

theorem outside_of_before {x : Mask s} (hx : x < Q.a) : ¬ Q.Inside x :=
  fun h => (not_le_of_gt hx) (Q.inside_iff.mp h).1

theorem outside_of_after {x : Mask s} (hx : Q.c < x) : ¬ Q.Inside x :=
  fun h => (not_le_of_gt hx) (Q.inside_iff.mp h).2

theorem inside_cases {x : Mask s} (hx : Q.Inside x) : x = Q.a ∨ x = Q.b ∨ x = Q.c := by
  have hL := hx.2
  have hU := low_lt x
  rcases (show low x = 1 ∨ low x = 2 ∨ low x = 3 by omega) with h | h | h
  · exact Or.inl (low_eq _ _ (hx.1.trans Q.hA.symm) (h.trans Q.ha.symm))
  · exact Or.inr (Or.inl (low_eq _ _ (hx.1.trans Q.hB.symm) (h.trans Q.hb.symm)))
  · exact Or.inr (Or.inr (low_eq _ _ hx.1 (h.trans Q.hc.symm)))

theorem earlier_unique {x t t' : Mask s} (h : Q.Earlier x t) (h' : Q.Earlier x t') : t = t' := by
  rcases h.2.1 with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;>
    rcases h'.2.1 with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> first | rfl | omega

theorem special_hole {q : ℕ} (h : q < s → bit Q.c q = false) (hq : q < s) : 2 ≤ q := by
  by_contra! hn
  have hh := h hq
  have hC := bit_low Q.c q hn
  rw [Q.hc,show (3:ℕ) = 2^2-1 from rfl,Nat.testBit_two_pow_sub_one] at hC
  simp [hn,hh] at hC

theorem W_of_later_high {q : ℕ} {y u : Mask s} (hy : high Q.c < high y)
    (h : Q.blanks q y u) : W y u := by
  have hc := high_order hy
  rcases (Q.blank_outside (Q.outside_of_after hc)).mp h with h' | ⟨t,he,_⟩
  · exact h'
  · exact ((not_lt_of_ge (Q.inside_iff.mp Q.a_inside).2) (lt_trans hc he.1)).elim

end Quarter
end Rowswap
```

### `LatinOddSpecial.lean`

```lean
import LatinOddMasks

namespace Rowswap.Quarter

variable (Q : Quarter s)

theorem special_witness {q : ℕ} (hmin : ∀ i < q, bit Q.c i = true)
    (hmiss : q < s → bit Q.c q = false)
    {x u : Mask s} (hx : Q.Inside x) (hu : ¬ Q.blanks q x u) :
    ∃ y v, Q.pos x < Q.pos y ∧ u < v ∧ xor x v = xor y u ∧
      Q.blanks q x v ∧ Q.blanks q y u ∧ Q.blanks q y v := by
  let r : Fin 4 := ⟨low x,low_lt x⟩
  let l : Fin 4 := ⟨low u,low_lt u⟩
  have hr : 0 < r.val := hx.2
  by_cases hU : WH Q.c u
  · have hLC : ¬ coverLow r l := fun h =>
      hu ((Q.blank_inside hx).mpr (Or.inl ⟨hU,h⟩))
    obtain ⟨t,w,ht,htr,hlw,hxor,hv,hyu,hyv⟩ := local_clue r l hr hLC
    let y := putLow Q.s_two Q.c t t.isLt
    let v := putLow Q.s_two u w w.isLt
    have hY : Q.Inside y := ⟨by simp [y],by simpa [y] using ht⟩
    have hV : WH Q.c v := (WH_putLow ..).mpr hU
    have he : xor x v = xor y u := by
      apply low_eq
      · simp [high_xor,v,y,hx.1]
      · simpa [low_xor,v,y,r,l] using hxor
    exact ⟨y,v,Q.later_inside hx hY (by simpa [y,r] using htr),
      low_order (by simp [v]) (by simpa [v,l] using hlw),he,
      (Q.blank_inside hx).mpr (Or.inl ⟨hV,by simpa [v,r] using hv⟩),
      (Q.blank_inside hY).mpr (Or.inl ⟨hU,by simpa [y,l] using hyu⟩),
      (Q.blank_inside hY).mpr (Or.inl ⟨hV,by simpa [y,v] using hyv⟩)⟩
  have hm : ∃ i, 2 ≤ i ∧ i < s ∧ bit Q.c i = false ∧ bit u i = false := by
    by_contra! hn
    apply hU
    intro i hi hi' hc
    exact Bool.eq_true_of_not_eq_false (hn i hi hi' hc)
  obtain ⟨i,hi,his,hci,hui⟩ := hm
  let vl := l.val ||| (3 ^^^ r.val)
  obtain ⟨hvl,hYu,hYv,hCv,hEv⟩ := local_union r l hr
  have use (w : Mask s) (hg : high u < high w)
      (hw : ∀ j, 2 ≤ j → j < s →
        (bit Q.c j = true → bit w j = bit u j) ∧
        (bit Q.c j = false → bit u j = true ∨ bit w j = true))
      (hdiff : ∃ j, 2 ≤ j ∧ j < s ∧ bit Q.c j = false ∧ bit u j ≠ bit w j)
      (hv : Q.Special q x (putLow Q.s_two w vl hvl)) :
      ∃ y v, Q.pos x < Q.pos y ∧ u < v ∧ xor x v = xor y u ∧
        Q.blanks q x v ∧ Q.blanks q y u ∧ Q.blanks q y v := by
    let v := putLow Q.s_two w vl hvl
    let y := mate x u v
    have hsame (j : ℕ) (hj : 2 ≤ j) : bit v j = bit w j :=
      same_high_bits (high_putLow ..) j hj
    have hbits (j : ℕ) (hj : 2 ≤ j) : bit x j = bit Q.c j := same_high_bits hx.1 j hj
    have ⟨hy,huY,hvY⟩ := wh_displacement (x := x) (u := u) (v := v)
      (fun j hj hjs => by simpa only [hsame j hj,hbits j hj] using hw j hj hjs)
      (by obtain ⟨j,hj,hjs,hc,hd⟩ := hdiff
          exact ⟨j,hj,hjs,(hbits j hj).trans hc,by rwa [hsame j hj]⟩)
    have hY : high Q.c < high y := hx.1 ▸ hy
    have hOut := Q.no_inside_high (ne_of_gt hY)
    have hLow : low y = r.val ^^^ (l.val ^^^ vl) := by simp [y,v,low_mate,r,l]
    refine ⟨y,v,Q.later_high hy,high_order (by simpa [v] using hg),mate_eq _ _ _,
      (Q.blank_inside hx).mpr hv,Q.blank_ordinary hOut ?_,Q.blank_ordinary hOut ?_⟩
    · exact (W_high_low Q.s_two _ _).mpr ⟨huY,by simpa [hLow,l,vl] using hYu⟩
    · exact (W_high_low Q.s_two _ _).mpr ⟨hvY,by simpa [hLow,v,vl] using hYv⟩
  rcases cover_or_extra r l hr with hC | hE
  · let w := highJoin Q.c u
    have hW (j : ℕ) (hjs : j < s) : bit w j = (bit u j || !bit Q.c j) :=
      highJoin_bit _ _ _ hjs
    have hwi : bit w i = true := by simp [hW i his,hci]
    have hg : high u < high w := high_strict (fun j _ hju => by
      have hjs : j < s := by
        by_contra! hn
        rw [bit_outside u hn] at hju
        contradiction
      simp [hW j hjs,hju]) ⟨i,hi,hui,hwi⟩
    refine use w hg ?_ ⟨i,hi,his,hci,by simp [hui,hwi]⟩ ?_
    · intro j _ hjs
      constructor <;> intro h <;> simp [hW j hjs,h]
    · apply Or.inl
      refine ⟨(WH_putLow ..).mpr (fun j _ hj hc => by simp [hW j hj,hc]),?_⟩
      simpa [vl,r] using hCv hC
  · have hqi : q ≤ i := by
      by_contra! hn
      have := hmin i hn
      simp_all
    have hqs := hqi.trans_lt his
    have hq2 := Q.special_hole hmiss hqs
    have huq : bit u q = true := by
      cases h : bit u q
      · exact (hu ((Q.blank_inside hx).mpr (Or.inr ⟨hqs,h,hE⟩))).elim
      · rfl
    have hqi' : q < i := lt_of_le_of_ne hqi (fun he => by rw [← he,huq] at hui; contradiction)
    let w := modified Q.c u q hqs
    have hW (j : ℕ) (hj : j < s) :
        bit w j = ((bit u j || !bit Q.c j) ^^ decide (q=j)) := bit_modified hqs hj
    have hwi : bit w i = true := by simp [hW i his,ne_of_lt hqi',hci]
    have hwq : bit w q = false := by simp [hW q hqs,hmiss hqs]
    have hg : high u < high w := by
      apply lt_of_not_ge
      intro hn
      have hd : u.val / 2^(q+1) < w.val / 2^(q+1) := by
        apply lt_of_le_of_ne
        · apply Nat.le_of_testBit
          intro j hj
          rw [Nat.testBit_div_two_pow] at hj ⊢
          change bit u (j+(q+1)) = true at hj
          have hj' : j+(q+1) < s := by
            by_contra! h
            rw [bit_outside u h] at hj
            contradiction
          change bit w (j+(q+1)) = true
          simp [hW _ hj',show q ≠ j+(q+1) by omega,hj]
        · intro he
          have hb := congrArg (fun a : ℕ => a.testBit (i-(q+1))) he
          simp only [Nat.testBit_div_two_pow, Nat.sub_add_cancel (Nat.succ_le_of_lt hqi')] at hb
          change bit u i = bit w i at hb
          simp [hui,hwi] at hb
      have hf (x : Mask s) : x.val / 2^(q+1) = high x / 2^(q-1) := by
        simp only [high,Nat.div_div_eq_div_mul,show (4:ℕ) = 2^2 from rfl, ← pow_add]
        rw [show 2+(q-1) = q+1 by omega]
      rw [hf,hf] at hd
      exact not_le_of_gt hd (Nat.div_le_div_right hn)
    refine use w hg ?_ ⟨i,hi,his,hci,by simp [hui,hwi]⟩ ?_
    · intro j _ hjs
      by_cases he : q=j
      · subst j
        simp [hW q hqs,hmiss hqs,huq]
      · constructor <;> intro h <;> simp [hW j hjs,he,h]
    · exact Or.inr ⟨hqs, (same_high_bits (high_putLow ..) q hq2).trans hwq,
        by simpa [vl,r] using hEv hE⟩

theorem special_arc {q : ℕ} (hmiss : q < s → bit Q.c q = false) {x y u v : Mask s}
    (hx : Q.Inside x) (hy : Q.pos x < Q.pos y) (he : xor x v = xor y u)
    (hu : Q.blanks q x u) (hv : Q.blanks q x v) (hY : Q.blanks q y u) :
    Q.rank x v < Q.rank x u := by
  simp only [rank,hx,ite_true]
  have hl := congrArg low he
  simp only [low_xor] at hl
  have hU := (Q.blank_inside hx).mp hu
  have hV := (Q.blank_inside hx).mp hv
  have hQ := Q.later_special hx hy
  have no_cover (w : Mask s) (hq : q < s) (hw : bit w q = false) : ¬ WH Q.c w := by
    intro h
    have := h q (Q.special_hole hmiss hq) hq (hmiss hq)
    simp [hw] at this
  have no_outer (h : WH Q.c u) (h' : WH Q.c v) (hY' : high Q.c < high y) : False := by
    have hle : high y ≤ high Q.c := high_compare (fun i hi hYi => by
      cases hc : bit Q.c i
      · have hi' : i < s := by
          by_contra! hn
          rw [bit_outside y hn] at hYi
          contradiction
        have hh := bit_equation he i
        have hX := same_high_bits hx.1 i hi
        simp [hX,hc,hYi,h i hi hi' hc,h' i hi hi' hc] at hh
      · rfl)
    exact (not_le_of_gt hY') hle
  have mixed (h : WH Q.c u ∧ q < s ∧ bit v q = false ∨
      WH Q.c v ∧ q < s ∧ bit u q = false) : high Q.c < high y := by
    rcases hQ with hY' | ⟨hY',_⟩
    · exact hY'
    · exfalso
      rcases h with ⟨hW,hqs,hb⟩ | ⟨hW,hqs,hb⟩
      all_goals
        have hh := bit_equation he q
        have hq2 := Q.special_hole hmiss hqs
        have hX := same_high_bits hx.1 q hq2
        have hY := same_high_bits hY'.1 q hq2
        simp [hX,hY,hmiss hqs,hb,hW q hq2 hqs (hmiss hqs)] at hh
  let r : Fin 4 := ⟨low x,low_lt x⟩
  let t : Fin 4 := ⟨low y,low_lt y⟩
  let U : Fin 4 := ⟨low u,low_lt u⟩
  let V : Fin 4 := ⟨low v,low_lt v⟩
  rcases hU with ⟨hWu,hCu⟩ | ⟨hqs,huq,hEu⟩ <;>
    rcases hV with ⟨hWv,hCv⟩ | ⟨hqs',hvq,hEv⟩
  · exfalso
    rcases hQ with hy' | ⟨hy',hlt⟩
    · exact no_outer hWu hWv hy'
    · rcases (Q.blank_inside hy').mp hY with ⟨_,hC⟩ | ⟨hq,hb,_⟩
      · exact local_cover_arc r t U V hy'.2 hlt hl hCu hCv hC
      · exact no_cover u hq hb hWu
  · have h := mixed (Or.inl ⟨hWu,hqs',hvq⟩)
    exact local_outer_arc r t U V hx.2 hl
      ((W_high_low Q.s_two _ _).mp (Q.W_of_later_high h hY)).2 (Or.inl ⟨hCu,hEv⟩)
  · have h := mixed (Or.inr ⟨hWv,hqs,huq⟩)
    exact local_outer_arc r t U V hx.2 hl
      ((W_high_low Q.s_two _ _).mp (Q.W_of_later_high h hY)).2 (Or.inr ⟨hEu,hCv⟩)
  · exfalso
    rcases hQ with hy' | ⟨hy',hlt⟩
    · have hh := bit_equation he q
      have hX := same_high_bits hx.1 q (Q.special_hole hmiss hqs)
      have hb : bit y q = false := by cases h : bit y q <;> simp_all
      have := (W_iff _ _).mp (Q.W_of_later_high hy' hY) q hqs hb
      simp [huq] at this
    · rcases (Q.blank_inside hy').mp hY with ⟨hW,_⟩ | ⟨_,_,hE⟩
      · exact no_cover u hqs huq hW
      · exact local_extra_arc r t U V hy'.2 hlt hl hEu hEv hE

end Rowswap.Quarter
```

### `LatinOddEarlier.lean`

```lean
import LatinOddSpecial

namespace Rowswap.Quarter

variable (Q : Quarter s)

private theorem canonical_high_gain {x y u v : Mask s} (hxy : high x < high y)
    (hsub : Submask x y) (hUV : Submask u v) (hEx : Extra x y u) (hW : W x v) :
    high u < high v := by
  have hi : ∃ i, 2 ≤ i ∧ i < s ∧ bit x i ≠ bit y i := by
    by_contra! h
    exact (ne_of_lt hxy) (high_eq_of_bits h)
  obtain ⟨i,hi,his,hne⟩ := hi
  have hX : bit x i = false := by
    cases hx : bit x i
    · rfl
    · exact (hne (hx.trans (hsub i hx).symm)).elim
  have hY : bit y i = true := by cases h : bit y i <;> simp_all
  exact high_strict (fun i _ => hUV i)
    ⟨i,hi,by simpa [hY] using hEx i his hX,(W_iff _ _).mp hW i his hX⟩

private theorem canonical_retarget {x y y' u v v' : Mask s} (he : xor x v = xor y u)
    (hh : high y' = high y) (hV : high v' = high v)
    (hL : low x ^^^ low v' = low y' ^^^ low u) : xor x v' = xor y' u := by
  apply low_eq
  · simpa only [high_xor,hh,hV] using congrArg high he
  · simpa only [low_xor] using hL

theorem outside_witness {q : ℕ} {x u : Mask s} (hx : ¬ Q.Inside x)
    (hu : ¬ Q.blanks q x u) :
    ∃ y v, Q.pos x < Q.pos y ∧ u < v ∧ xor x v = xor y u ∧
      Q.blanks q x v ∧ Q.blanks q y u ∧ Q.blanks q y v := by
  obtain ⟨y,v,hsub,hxy,huv,hWv,hYu,hYv,_,he,hUV⟩ :=
    canonical_bits (fun h => hu (Q.blank_ordinary hx h))
  have hpos : Q.pos x < Q.pos y := Q.later.mpr (Or.inl ⟨hxy,fun h => hx h.1⟩)
  by_cases hy : Q.Inside y
  · have hxa : x < Q.a := by
      by_contra! hn
      exact hx (Q.inside_iff.mpr ⟨hn,hxy.le.trans (Q.inside_iff.mp hy).2⟩)
    have hU : WH Q.c u := (Q.high_blank hy).mp ((W_high_low Q.s_two _ _).mp hYu).1
    have hV : WH Q.c v := (Q.high_blank hy).mp ((W_high_low Q.s_two _ _).mp hYv).1
    by_cases hya : y = Q.a
    · subst y
      exact ⟨Q.a,v,hpos,huv,he,Q.blank_ordinary hx hWv,Q.blank_a hU,Q.blank_a hV⟩
    have hbc := (Q.inside_cases hy).resolve_left hya
    have hly : low y = 2 ∨ low y = 3 := by rcases hbc with rfl | rfl <;> simp [Q.hb,Q.hc]
    let X : Fin 4 := ⟨low x,low_lt x⟩
    let Y : Fin 4 := ⟨low y,low_lt y⟩
    let U : Fin 4 := ⟨low u,low_lt u⟩
    let V : Fin 4 := ⟨low v,low_lt v⟩
    have hex : Extra x y u := isExtra he hWv
    have heL := congrArg low he
    simp only [low_xor] at heL
    have hL := local_canonical X Y U V hly (lowSubset_of_submask hsub)
      (extra_lowPattern Q.s_two hsub hex) heL
    rcases hL with h0 | h1 | hcover | hb | hc
    · have hyb : y = Q.b := low_eq _ _ (hy.1.trans Q.hB.symm) (h0.2.trans Q.hb.symm)
      exact (hu ((Q.blank_outside hx).mpr
        (Or.inr ⟨y,⟨hxa,Or.inl ⟨h0.1,hyb⟩,hsub⟩,hex⟩))).elim
    · have hyc : y = Q.c := low_eq _ _ hy.1 (h1.2.trans Q.hc.symm)
      exact (hu ((Q.blank_outside hx).mpr
        (Or.inr ⟨y,⟨hxa,Or.inr ⟨h1.1,hyc⟩,hsub⟩,hex⟩))).elim
    · exact ⟨y,v,hpos,huv,he,Q.blank_ordinary hx hWv,
        (Q.blank_inside hy).mpr (Or.inl ⟨hU,hcover.1⟩),
        (Q.blank_inside hy).mpr (Or.inl ⟨hV,hcover.2⟩)⟩
    · obtain ⟨hyl,hxl,hul⟩ := hb
      let K := putLow Q.s_two Q.c 0 (by decide)
      let v' := putLow Q.s_two v 3 (by decide)
      have hK : high K = high Q.c := by simp [K]
      have hK0 : low K = 0 := by simp [K]
      have hVl : low v' = 3 := by simp [v']
      have hVh : high v' = high v := by simp [v']
      have hVh' : WH Q.c v' := (WH_putLow ..).mpr hV
      have hxK : high x < high K := by
        have hhh := Q.hA
        have hll := Q.ha
        change low x = 2 at hxl
        simp only [Fin.lt_def,low,high] at *
        omega
      have hKa : K < Q.a := low_order (by rw [hK,Q.hA]) (by simp [hK0,Q.ha])
      have hOut := Q.outside_of_before hKa
      have hKB : Submask K Q.b := by
        intro i hi
        by_cases h : 2 ≤ i
        · rwa [← same_high_bits (hK.trans Q.hB.symm) i h]
        · have hl := bit_low K i (by omega)
          rw [hK0,Nat.zero_testBit] at hl
          rw [hi] at hl
          contradiction
      have hXv : W x v' := by
        apply (W_high_low Q.s_two _ _).mpr
        refine ⟨(WH_putLow ..).mpr ((W_high_low Q.s_two _ _).mp hWv).1,?_⟩
        change low x = 2 at hxl
        simp [WL,hxl,hVl]
      have hKv : W K v' := by
        apply (W_high_low Q.s_two _ _).mpr
        exact ⟨fun i hi hs hbit => hVh' i hi hs (by rwa [← same_high_bits hK i hi]),
          by simp [WL,hK0,hVl]⟩
      have hKu : Extra K Q.b u := by
        intro i hi hi'
        by_cases h : 2 ≤ i
        · have hB := same_high_bits (hK.trans Q.hB.symm) i h
          have hC := same_high_bits hK i h
          simp [← hB,hi',hU i h hi (by rwa [← hC])]
        · apply (lowPattern_iff Q.s_two hKB).mp ?_ i (by omega) hi'
          change low u = 1 at hul
          simp [lowPattern,hK0,Q.hb,hul]
      have he' : xor x v' = xor K u := canonical_retarget he (hK.trans hy.1.symm) hVh (by
        change low x = 2 at hxl
        change low u = 1 at hul
        simp [hK0,hVl,hxl,hul])
      refine ⟨K,v',Q.later_high hxK,low_order ?_ ?_,he',
        Q.blank_ordinary hx hXv,(Q.blank_outside hOut).mpr
          (Or.inr ⟨Q.b,⟨hKa,Or.inl ⟨hK0,rfl⟩,hKB⟩,hKu⟩),
        Q.blank_ordinary hOut hKv⟩
      · rw [hVh]; exact high_compare (fun i _ => hUV i)
      · change low u = 1 at hul
        simp [hul,hVl]
    · obtain ⟨hyl,hxl⟩ := hc
      have hya : high y = high Q.a := hy.1.trans Q.hA.symm
      have hxc : high x < high y := by
        have hll := Q.ha
        change 2 ≤ low x at hxl
        simp only [low,high,Fin.lt_def] at *
        omega
      have hyc : y = Q.c := low_eq _ _ hy.1 (hyl.trans Q.hc.symm)
      have hpat : lowPattern X 3 U := by
        have := extra_lowPattern Q.s_two hsub hex
        simpa [X,U,hyc,Q.hc] using this
      let vl := X.val ^^^ U.val ^^^ 1
      obtain ⟨hvl,hWL,hxor⟩ := local_reroute_a X U hxl hpat
      let v' := putLow Q.s_two v vl hvl
      have hVh : high v' = high v := by simp [v']
      have he' : xor x v' = xor Q.a u := canonical_retarget he hya.symm hVh
        (by simpa [v',X,U,Q.ha] using hxor)
      have hV' : W x v' := (W_high_low Q.s_two _ _).mpr
        ⟨(WH_putLow ..).mpr ((W_high_low Q.s_two _ _).mp hWv).1,
          by simpa [v',X] using hWL⟩
      exact ⟨Q.a,v',Q.later_high (by rwa [← hya]),high_order (by
        rw [hVh]; exact canonical_high_gain hxc hsub hUV hex hWv),
        he',Q.blank_ordinary hx hV',Q.blank_a hU,Q.blank_a ((WH_putLow ..).mpr hV)⟩
  · exact ⟨y,v,hpos,huv,he,Q.blank_ordinary hx hWv,Q.blank_ordinary hy hYu,Q.blank_ordinary hy hYv⟩

private theorem high_rank_loss {x y t u v : Mask s} (he : xor x v = xor y u)
    (hWu : W y u) (hlt : high y < high t) (hsub : Submask y t)
    (hmatch : ∀ i, i < s → bit x i = false → bit y i = bit t i) :
    highIntersect x v < highIntersect x u := by
  have hh : ∃ i, 2 ≤ i ∧ i < s ∧ bit y i ≠ bit t i := by
    by_contra! h
    exact (ne_of_lt hlt) (high_eq_of_bits h)
  obtain ⟨i,hi,his,hne⟩ := hh
  have hx : bit x i = true := by
    cases h : bit x i
    · exact (hne (hmatch i his h)).elim
    · rfl
  have hy : bit y i = false := by
    cases h : bit y i
    · rfl
    · exact (hne (h.trans (hsub i h).symm)).elim
  have hu := (W_iff _ _).mp hWu i his hy
  have hv : bit v i = false := by
    have hh := bit_equation he i
    cases h : bit v i <;> simp_all
  apply highIntersect_lt (fun j _ hx' hv' => ?_) ⟨i,hi,hx,hv,hu⟩
  by_cases hjs : j < s
  · cases hy' : bit y j
    · exact (W_iff _ _).mp hWu j hjs hy'
    · have hh := bit_equation he j
      cases hu' : bit u j <;> simp_all
  · have := bit_outside x (Nat.le_of_not_lt hjs)
    simp_all

theorem outside_arc {q : ℕ} (hmiss : q < s → bit Q.c q = false) {x y u v : Mask s}
    (hx : ¬ Q.Inside x) (hpos : Q.pos x < Q.pos y) (he : xor x v = xor y u)
    (hu : Q.blanks q x u) (hv : Q.blanks q x v) (hy : Q.blanks q y u) :
    Q.rank x v < Q.rank x u := by
  have hxy := ((Q.later.mp hpos).resolve_right (fun h => hx h.1)).1
  have not_sub : ¬ Submask y x := fun h => (not_le_of_gt hxy) h.le
  have hl := congrArg low he
  simp only [low_xor] at hl
  have mixed {t : Mask s} (ht : Q.Earlier x t)
      (hmatch : Submask y t ∧ ∀ i, i < s → bit x i = false → bit y i = bit t i)
      (hpair : (W x u ∧ Extra x t v) ∨ (Extra x t u ∧ W x v)) :
      Q.rank x v < Q.rank x u := by
    have hTL : (low x = 0 ∧ low t = 2) ∨ (low x = 1 ∧ low t = 3) := by
      rcases ht.2.1 with ⟨hh,rfl⟩ | ⟨hh,rfl⟩
      · exact Or.inl ⟨hh,Q.hb⟩
      · exact Or.inr ⟨hh,Q.hc⟩
    have hTH : high t = high Q.c := by
      rcases ht.2.1 with ⟨_,rfl⟩ | ⟨_,rfl⟩
      · exact Q.hB
      · rfl
    have ht' : high y ≤ high t := high_compare (fun i _ => hmatch.1 i)
    have hW : WH Q.c u := by
      intro i hi his hc
      have htt : bit t i = false := by rw [same_high_bits hTH i hi,hc]
      have hxx : bit x i = false := by
        cases hh : bit x i
        · rfl
        · have := ht.2.2 i hh
          simp [htt] at this
      rcases hpair with ⟨hh,_⟩ | ⟨hh,_⟩
      · exact (W_iff _ _).mp hh i his hxx
      · simpa [htt] using hh i his hxx
    let X : Fin 4 := ⟨low x,low_lt x⟩
    let T : Fin 4 := ⟨low t,low_lt t⟩
    let Y : Fin 4 := ⟨low y,low_lt y⟩
    let U : Fin 4 := ⟨low u,low_lt u⟩
    let V : Fin 4 := ⟨low v,low_lt v⟩
    have hp : (WL X U ∧ lowPattern X T V) ∨ (lowPattern X T U ∧ WL X V) := by
      rcases hpair with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · exact Or.inl ⟨((W_high_low Q.s_two _ _).mp h1).2,
          extra_lowPattern Q.s_two ht.2.2 h2⟩
      · exact Or.inr ⟨extra_lowPattern Q.s_two ht.2.2 h1,
          ((W_high_low Q.s_two _ _).mp h2).2⟩
    obtain ⟨hYL,hRank⟩ := local_expanded X T Y U V hTL hl hp
    simp only [rank,hx,ite_false]
    by_cases heq : high y = high t
    · have hY : Q.Inside y := ⟨heq.trans hTH,by change low y = 2 ∨ low y = 3 at hYL; omega⟩
      have hC : coverLow (low y) (low u) := by
        rcases (Q.blank_inside hY).mp hy with ⟨_,hC⟩ | ⟨hq,hb,_⟩
        · exact hC
        · have hh := hW q (Q.special_hole hmiss hq) hq (hmiss hq)
          simp [hb] at hh
      have hr := hRank hC
      have hh : highIntersect x v = highIntersect x u := by
        apply Nat.eq_of_testBit_eq
        intro i
        simp only [highIntersect,Nat.testBit_and,high_bit]
        cases hX : bit x (i+2)
        · rfl
        · have hT := ht.2.2 _ hX
          have hY := (same_high_bits heq (i+2) (by omega)).trans hT
          have hb := bit_equation he (i+2)
          cases hU : bit u (i+2) <;> cases hV : bit v (i+2) <;> simp_all
      rw [hh]
      exact Nat.add_lt_add_left hr _
    · have hYout := Q.no_inside_high (fun h => heq (h.trans hTH.symm))
      have hWY : W y u := by
        rcases (Q.blank_outside hYout).mp hy with h | ⟨t',ht',_⟩
        · exact h
        · rcases ht'.2.1 with h0 | h1 <;>
            change low y = 2 ∨ low y = 3 at hYL <;> omega
      have hc := high_rank_loss he hWY (lt_of_le_of_ne ht' heq) hmatch.1 hmatch.2
      have hr : lowRank (low v) ≤ 3 := by
        unfold lowRank
        split
        · decide
        · split
          · decide
          · split <;> decide
      omega
  rcases (Q.blank_outside hx).mp hu with hu | ⟨t,ht,hu⟩ <;>
    rcases (Q.blank_outside hx).mp hv with hv | ⟨t',ht',hv⟩
  · exact (not_sub (submask_of_ordinary_arc hu hv he)).elim
  · exact mixed ht' (expanded_mixed he ht'.2.2 hu hv) (Or.inl ⟨hu,hv⟩)
  · exact mixed ht (expanded_mixed (opposite_diagonal he) ht.2.2 hv hu) (Or.inr ⟨hu,hv⟩)
  · cases Q.earlier_unique ht ht'
    exact (not_sub (expanded_same_class he
      (fun i hi hbit => (hu i hi hbit).trans (hv i hi hbit).symm))).elim

end Rowswap.Quarter
```

### `LatinConjecture.lean`

```lean
import LatinOddEarlier
import LatinOddAdjacent
import LatinEvenAdjacent
import LatinPrinted
import Mathlib.Data.Nat.Dist

namespace Rowswap

theorem conj_6_1_odd_aligned (s : ℕ) (a c : Fin (2^s))
    (hac : a.val + 2 = c.val) (hmod : a.val % 4 = 1) :
    let L := rowSwap (Ls s) a c
    TwoCritical (gcs L) L ∧ Strong (gcs L) L ∧ CompletesTopDown (gcs L) L := by
  classical
  let b : Mask s := ⟨a.val + 1, by have := c.isLt; omega⟩
  have hb : b.val = a.val + 1 := rfl
  let Q : Quarter s := ⟨a,b,c,hmod,by unfold low; omega,by unfold low; omega,
    by unfold high; omega,by unfold high; omega⟩
  obtain ⟨q,_,hmin,hmiss⟩ := least_hole c
  change TwoCritical (gcs (positioned Q.pos)) (positioned Q.pos) ∧
    Strong (gcs (positioned Q.pos)) (positioned Q.pos) ∧
    CompletesTopDown (gcs (positioned Q.pos)) (positioned Q.pos)
  apply mask_certificate Q.pos (Q.blanks q) Q.rank
  · intro x u hu
    obtain ⟨y,v,hpos,hlt,he,hV,hYu,hYv⟩ :=
      if hx : Q.Inside x then Q.special_witness hmin hmiss hx hu else Q.outside_witness hx hu
    exact ⟨y,v,hpos,hlt,opposite_diagonal he,he,hV,hYu,hYv⟩
  · intro x y u v hpos _ he hu hv hy
    by_cases hx : Q.Inside x
    · exact Q.special_arc hmiss hx hpos he hu hv hy
    · exact Q.outside_arc hmiss hx hpos he hu hv hy

private theorem ordered_conj (s : ℕ) (a b : Fin (2^s)) (hab : a ≤ b)
    (h : Nat.dist a.val b.val < 3) :
    let L := rowSwap (Ls s) a b
    TwoCritical (gcs L) L ∧ Strong (gcs L) L ∧ CompletesTopDown (gcs L) L := by
  have hle : a.val ≤ b.val := hab
  rw [Nat.dist_eq_sub_of_le hle] at h
  rcases (show a = b ∨ a.val+1 = b.val ∨ a.val+2 = b.val by simp only [Fin.ext_iff]; omega)
    with rfl | h₁ | h₂
  · exact conj_6_1_identity s a
  · by_cases he : a.val % 2 = 0
    · exact conj_6_1_even_adjacent s a b h₁ he
    · exact conj_6_1_odd_adjacent s a b h₁ (by omega)
  · rcases (show a.val % 4 = 0 ∨ a.val % 4 = 1 ∨ a.val % 4 = 2 ∨ a.val % 4 = 3 by omega)
      with h0 | h1 | h2 | h3
    · exact conj_6_1_even_aligned s a b h₂ h0
    · exact conj_6_1_odd_aligned s a b h₂ h1
    · exact conj_6_1_even_crossing s a b h₂ h2
    · exact conj_6_1_odd_crossing s a b h₂ h3

theorem conj_6_1 (s : ℕ) (k k' : Fin (2^s)) (h : Nat.dist k.val k'.val < 3) :
    let L := rowSwap (Ls s) k k'
    TwoCritical (gcs L) L ∧ Strong (gcs L) L ∧ CompletesTopDown (gcs L) L := by
  rcases le_total k k' with hle | hle
  · exact ordered_conj s k k' hle h
  · have hswap : rowSwap (Ls s) k k' = rowSwap (Ls s) k' k := by
      funext r c
      unfold rowSwap
      rw [Equiv.swap_comm k k']
    rw [hswap]
    exact ordered_conj s k' k hle (by rwa [Nat.dist_comm])

#check conj_6_1_odd_aligned
#check conj_6_1
#print axioms conj_6_1_odd_aligned
#print axioms conj_6_1

end Rowswap
```

