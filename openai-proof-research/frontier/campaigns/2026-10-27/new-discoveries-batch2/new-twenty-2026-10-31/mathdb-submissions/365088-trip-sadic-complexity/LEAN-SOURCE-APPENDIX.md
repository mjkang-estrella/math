# Lean source appendix — MathDB 365088 (complete formalization)

Modules follow in import order; each block is byte-identical to `src/<Module>.lean`. The endpoint `garrity_osterman_conj53` is in `TripMain.lean`; `TripAudit.lean` prints the definitions and axioms.

### `TripLanguage.lean`

```lean
import Mathlib.Data.List.Infix
import Mathlib.Data.Fintype.Vector
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases

/- Literal Definition 14 of Garrity--Osterman. 0,1,2 encode 1,2,3. -/
namespace Trip
abbrev Letter := Fin 3
abbrev Word := List Letter

def S0 (c : Letter) : Word := if c = 0 then [1] else if c = 1 then [0,2] else [2]
def S1 (c : Letter) : Word := if c = 0 then [0] else if c = 1 then [1] else [0,2]
def subst (b : Bool) (w : Word) : Word := w.flatMap (if b then S1 else S0)

def prefImage (d : ℕ → Bool) : ℕ → Word → Word
  | 0, w => w
  | r+1, w => prefImage d r (subst (d r) w)

def lang (d : ℕ → Bool) (w : Word) : Prop :=
  ∃ (r : ℕ) (c : Letter), w <:+: prefImage d r [c]

noncomputable def complexity (L : Word → Prop) (n : ℕ) : ℕ :=
  Nat.card {w : Word // w.length = n ∧ L w}

/-- This is a proposition definition, not a proof of the conjecture. -/
def Conjecture53 : Prop :=
  ∀ (d : ℕ → Bool) (n : ℕ), 1 ≤ n → complexity (lang d) n ≤ 3 * n

instance finiteWords (L : Word → Prop) (n : ℕ) :
    Finite {w : Word // w.length = n ∧ L w} := by
  let f : {w : Word // w.length = n ∧ L w} → List.Vector Letter n :=
    fun w => ⟨w.val, w.property.1⟩
  apply Finite.of_injective f
  intro a b h
  apply Subtype.ext
  exact congrArg (fun v : List.Vector Letter n => v.val) h

@[simp] theorem subst_append (b : Bool) (u v : Word) :
    subst b (u ++ v) = subst b u ++ subst b v := by
  simp [subst]

@[simp] theorem prefImage_append (d : ℕ → Bool) (r : ℕ) (u v : Word) :
    prefImage d r (u ++ v) = prefImage d r u ++ prefImage d r v := by
  induction r generalizing u v with
  | zero => rfl
  | succ r ih => simp only [prefImage, subst_append, ih]

@[simp] theorem prefImage_nil (d : ℕ → Bool) (r : ℕ) : prefImage d r [] = [] := by
  induction r with
  | zero => rfl
  | succ r ih => simpa [prefImage, subst] using ih

theorem lang_singleton (d : ℕ → Bool) (c : Letter) : lang d [c] :=
  ⟨0,c,⟨[],[],by simp [prefImage]⟩⟩

theorem lang_nil (d : ℕ → Bool) : lang d [] :=
  ⟨0,0,List.nil_infix⟩

theorem lang_factor (d : ℕ → Bool) {u v : Word}
    (hu : u <:+: v) (hv : lang d v) : lang d u := by
  obtain ⟨r,c,h⟩ := hv
  exact ⟨r,c,hu.trans h⟩

theorem lang_length_one (d : ℕ → Bool) (w : Word) (h : w.length = 1) :
    lang d w := by
  obtain ⟨c,rfl⟩ := List.length_eq_one_iff.mp h
  exact lang_singleton d c

def oneEquiv (d : ℕ → Bool) : {w : Word // w.length = 1 ∧ lang d w} ≃ Letter where
  toFun w := w.val.head (by intro h; have := w.property.1; simp [h] at this)
  invFun c := ⟨[c], rfl, lang_singleton d c⟩
  left_inv w := by
    apply Subtype.ext
    obtain ⟨c,hc⟩ := List.length_eq_one_iff.mp w.property.1
    simp [hc]
  right_inv c := rfl

theorem complexity_one (d : ℕ → Bool) : complexity (lang d) 1 = 3 := by
  unfold complexity
  rw [Nat.card_congr (oneEquiv d)]
  exact Nat.card_fin 3

theorem complexity_zero (d : ℕ → Bool) : complexity (lang d) 0 = 1 := by
  have he : {w : Word // w.length = 0 ∧ lang d w} ≃ Unit :=
    { toFun := fun _ => ()
      invFun := fun _ => ⟨[],rfl,lang_nil d⟩
      left_inv := fun w => Subtype.ext (List.length_eq_zero_iff.mp w.property.1).symm
      right_inv := fun _ => rfl }
  exact (Nat.card_congr he).trans (by simp)

#print axioms complexity_one
#print axioms complexity_zero
end Trip
```

### `TripSanity.lean`

```lean
import TripLanguage
import Mathlib.Data.List.Chain

set_option linter.unusedSimpArgs false

namespace Trip

def allS1 : ℕ → Bool := fun _ => true

@[simp] theorem allS1_image (r : ℕ) (c : Letter) :
    prefImage allS1 r [c] =
      if c = 0 then [0] else if c = 1 then [1]
      else List.replicate r 0 ++ [2] := by
  induction r generalizing c with
  | zero => fin_cases c <;> rfl
  | succ r ih =>
    have h02 := prefImage_append allS1 r [0] [2]
    fin_cases c <;>
      simp [prefImage, subst, allS1, S1, ih, List.replicate_succ,
        show prefImage allS1 r [0,2] = [0] ++ (List.replicate r 0 ++ [2]) by simpa [ih] using h02]

/-- The relation records the only possible adjacent letters in 1^r3. -/
def allowedAdjacent (a b : Letter) : Prop := a = 0 ∧ (b = 0 ∨ b = 2)

lemma run_chain (r : ℕ) :
    (List.replicate r (0 : Letter) ++ [2]).IsChain allowedAdjacent := by
  induction r with
  | zero => simp
  | succ r ih =>
    cases r with
    | zero => simp [List.replicate_succ, allowedAdjacent]
    | succ r =>
      simpa [List.replicate_succ, List.cons_append,
        List.isChain_cons_cons, allowedAdjacent] using ih

lemma allS1_pair_iff (a b : Letter) :
    lang allS1 [a,b] ↔ a = 0 ∧ (b = 0 ∨ b = 2) := by
  constructor
  · rintro ⟨r,c,h⟩
    rw [allS1_image] at h
    split at h
    · have hh := h.length_le
      simp at hh
    · split at h
      · have hh := h.length_le
        simp at hh
      · have hh := (run_chain r).infix h
        simpa only [List.isChain_cons_cons, List.isChain_singleton, and_true, allowedAdjacent]
          using hh
  · rintro ⟨rfl,h | h⟩
    · subst b
      exact ⟨2,2,[],[2],rfl⟩
    · subst b
      exact ⟨1,2,[],[],rfl⟩

def pairEquiv : {w : Word // w.length = 2 ∧ lang allS1 w} ≃ Bool where
  toFun w := decide (w.val = [0,2])
  invFun b := if b then ⟨[0,2], rfl, (allS1_pair_iff _ _).mpr ⟨rfl,Or.inr rfl⟩⟩
    else ⟨[0,0],rfl,(allS1_pair_iff _ _).mpr ⟨rfl,Or.inl rfl⟩⟩
  left_inv w := by
    apply Subtype.ext
    obtain ⟨a,b,h⟩ := List.length_eq_two.mp w.property.1
    have hp := (allS1_pair_iff a b).mp (h ▸ w.property.2)
    rcases hp with ⟨rfl,rfl | rfl⟩ <;> simp [h]
  right_inv b := by cases b <;> rfl

theorem allS1_small_complexities :
    complexity (lang allS1) 0 = 1 ∧
    complexity (lang allS1) 1 = 3 ∧
    complexity (lang allS1) 2 = 2 := by
  refine ⟨complexity_zero _,complexity_one _,?_⟩
  exact (Nat.card_congr pairEquiv).trans (by simp)

#print axioms allS1_image
#print axioms allS1_pair_iff
#print axioms allS1_small_complexities
end Trip
```

### `TripReduction.lean`

```lean
import TripLanguage

namespace Trip

/-- Every letter occurs in the union of the three images, even in a
    nonprimitive directive. This supports nesting of literal prefix languages. -/
theorem letter_occurs (b : Bool) (c : Letter) :
    ∃ e : Letter, [c] <:+: subst b [e] := by
  cases b <;> fin_cases c
  · exact ⟨1,[],[2],rfl⟩
  · exact ⟨0,[],[],rfl⟩
  · exact ⟨2,[],[],rfl⟩
  · exact ⟨0,[],[],rfl⟩
  · exact ⟨1,[],[],rfl⟩
  · exact ⟨2,[0],[],rfl⟩

theorem prefImage_infix (d : ℕ → Bool) (r : ℕ) {u v : Word}
    (h : u <:+: v) : prefImage d r u <:+: prefImage d r v := by
  obtain ⟨a,b,h⟩ := h
  refine ⟨prefImage d r a,prefImage d r b,?_⟩
  simpa only [prefImage_append] using congrArg (prefImage d r) h

def prefixLanguage (d : ℕ → Bool) (r : ℕ) (w : Word) : Prop :=
  ∃ c : Letter, w <:+: prefImage d r [c]

theorem prefixLanguage_succ (d : ℕ → Bool) (r : ℕ) {w : Word}
    (h : prefixLanguage d r w) : prefixLanguage d (r+1) w := by
  obtain ⟨c,hc⟩ := h
  obtain ⟨e,he⟩ := letter_occurs (d r) c
  exact ⟨e,hc.trans (prefImage_infix d r he)⟩

theorem prefixLanguage_mono (d : ℕ → Bool) {r s : ℕ} (hrs : r ≤ s)
    {w : Word} (h : prefixLanguage d r w) : prefixLanguage d s w := by
  induction hrs with
  | refl => exact h
  | step hs ih => exact prefixLanguage_succ d _ ih

theorem lang_iff_prefix (d : ℕ → Bool) (w : Word) :
    lang d w ↔ ∃ r, prefixLanguage d r w := Iff.rfl

/-- Every finite collection of literal factors already occurs at one finite
    level. There is no assumption on the directive. -/
theorem finite_factors_one_level (d : ℕ → Bool) (F : Finset Word)
    (hF : ∀ w ∈ F, lang d w) :
    ∃ r, ∀ w ∈ F, prefixLanguage d r w := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨0,by simp⟩
  | @insert w F hw ih =>
    obtain ⟨r,hr⟩ := hF w (by simp)
    obtain ⟨s,hs⟩ := ih (by intro v hv; exact hF v (by simp [hv]))
    refine ⟨max r s,?_⟩
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact prefixLanguage_mono d (le_max_left _ _) hr
    · exact prefixLanguage_mono d (le_max_right _ _) (hs v hv)

theorem complexity_mono (L K : Word → Prop) (h : ∀ w, L w → K w) (n : ℕ) :
    complexity L n ≤ complexity K n := by
  let f : {w : Word // w.length = n ∧ L w} → {w : Word // w.length = n ∧ K w} :=
    fun w => ⟨w.val,w.property.1,h w.val w.property.2⟩
  apply Nat.card_le_card_of_injective f
  intro a b hab
  exact Subtype.ext (congrArg (fun x : {w : Word // w.length = n ∧ K w} => x.val) hab)

/-- Honest bridge from an independently proved first-difference estimate.
    This theorem supplies no such estimate for the TRIP language. -/
theorem linear_bound_of_first_difference (p : ℕ → ℕ) (h1 : p 1 ≤ 3)
    (hs : ∀ n, 1 ≤ n → p (n+1) ≤ p n + 3) (n : ℕ) (hn : 1 ≤ n) :
    p n ≤ 3*n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hz : n = 0
    · subst n; simpa using h1
    · have hi := ih (by omega)
      have hh := hs n (by omega)
      omega

#print axioms finite_factors_one_level
#print axioms complexity_mono
#print axioms linear_bound_of_first_difference
end Trip
```

### `TripBlocks.lean`

```lean
import TripLanguage

set_option linter.unusedSimpArgs false

namespace Trip

def run (n : ℕ) (a : Letter) : Word := List.replicate n a

def block (j k : ℕ) (c : Letter) : Word :=
  if c = 0 then run (j+1) 0 ++ [2]
  else if c = 1 then run (k+1) 1 ++ run j 0 ++ [2]
  else run k 1 ++ run j 0 ++ [2]

def sigma (j k : ℕ) (w : Word) : Word := w.flatMap (block j k)

def s1Power : ℕ → Word → Word
  | 0, w => w
  | r+1, w => subst true (s1Power r w)

def gauss (k : ℕ) (w : Word) : Word := s1Power k (subst false w)

@[simp] lemma sigma_append (j k : ℕ) (u v : Word) :
    sigma j k (u ++ v) = sigma j k u ++ sigma j k v := by simp [sigma]

@[simp] lemma s1Power_append (r : ℕ) (u v : Word) :
    s1Power r (u ++ v) = s1Power r u ++ s1Power r v := by
  induction r with
  | zero => rfl
  | succ r ih => simp [s1Power, ih]

@[simp] lemma subst_run_zero (r : ℕ) : subst true (run r 0) = run r 0 := by
  induction r with
  | zero => rfl
  | succ r ih => simpa [subst,run,List.replicate_succ,S1] using congrArg (List.cons 0) ih

@[simp] lemma subst_run_one (r : ℕ) : subst true (run r 1) = run r 1 := by
  induction r with
  | zero => rfl
  | succ r ih => simpa [subst,run,List.replicate_succ,S1] using congrArg (List.cons 1) ih

@[simp] lemma s1Power_zero (r : ℕ) : s1Power r [0] = [0] := by
  induction r with
  | zero => rfl
  | succ r ih => simp [s1Power,ih,subst,S1]

@[simp] lemma s1Power_one (r : ℕ) : s1Power r [1] = [1] := by
  induction r with
  | zero => rfl
  | succ r ih => simp [s1Power,ih,subst,S1]

@[simp] lemma s1Power_two (r : ℕ) : s1Power r [2] = run r 0 ++ [2] := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [s1Power, ih, subst_append, subst_run_zero]
    simp [subst,S1,run,List.replicate_succ',List.append_assoc]

@[simp] lemma gauss_zero (k : ℕ) : gauss k [0] = [1] := by simp [gauss,subst,S0]
@[simp] lemma gauss_one (k : ℕ) : gauss k [1] = run (k+1) 0 ++ [2] := by
  change s1Power k ([0] ++ [2]) = _
  rw [s1Power_append,s1Power_zero,s1Power_two]
  rfl
@[simp] lemma gauss_two (k : ℕ) : gauss k [2] = run k 0 ++ [2] := by simp [gauss,subst,S0]

@[simp] lemma gauss_append (j : ℕ) (u v : Word) :
    gauss j (u ++ v) = gauss j u ++ gauss j v := by
  simp only [gauss,subst_append,s1Power_append]

@[simp] lemma s1Power_nil (j : ℕ) : s1Power j [] = [] := by
  induction j <;> simp_all [s1Power,subst]

lemma gauss_run (j r : ℕ) : gauss j (run r 0) = run r 1 := by
  induction r with
  | zero => simp [gauss,subst,run]
  | succ r ih =>
    change gauss j ([0] ++ run r 0) = [1] ++ run r 1
    rw [gauss_append,gauss_zero,ih]

/-- Equation (44), proved from the two concrete Farey substitutions. -/
theorem double_gauss_letter (j k : ℕ) (c : Letter) :
    gauss j (gauss k [c]) = block j k c := by
  fin_cases c
  · change gauss j (gauss k [0]) = _
    simp [block,run]
  · change gauss j (gauss k [1]) = _
    rw [gauss_one,gauss_append,gauss_run,gauss_two]
    simp [block,List.append_assoc]
  · change gauss j (gauss k [2]) = _
    rw [gauss_two,gauss_append,gauss_run,gauss_two]
    simp [block,List.append_assoc]

lemma block_ends (j k : ℕ) (c : Letter) : ∃ u : Word, block j k c = u ++ [2] := by
  fin_cases c
  · exact ⟨run (j+1) 0, rfl⟩
  · exact ⟨run (k+1) 1 ++ run j 0, by simp [block,List.append_assoc]⟩
  · exact ⟨run k 1 ++ run j 0, by simp [block,List.append_assoc]⟩

lemma block_length_pos (j k : ℕ) (c : Letter) : 0 < (block j k c).length := by
  obtain ⟨u,hu⟩ := block_ends j k c
  simp [hu]

lemma block_only_terminal_three (j k : ℕ) (c : Letter) :
    (block j k c).count 2 = 1 := by
  fin_cases c <;> simp [block,run,List.count_replicate]

#print axioms double_gauss_letter
#print axioms block_only_terminal_three
end Trip
```

### `ExtensionGraphs.lean`

```lean
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/- Finite graph computations for the written proof. This is NOT a formalization
   of the word parsing lemma or the MathDB endpoint. -/
namespace TripExtensionGraphs

abbrev Graph := Finset (ℕ × ℕ)

def decode (e : ℕ) : Graph :=
  ((Finset.range 9).filter fun i => e.testBit i).image fun i => (i / 3, i % 3)
def encode (g : Graph) : ℕ := ∑ p ∈ g, 2 ^ (3 * p.1 + p.2)
def leftVal (g : Graph) : ℕ := (g.image Prod.fst).card
def rightVal (g : Graph) : ℕ := (g.image Prod.snd).card
def bispecial (g : Graph) : Bool := decide (2 ≤ leftVal g ∧ 2 ≤ rightVal g)
def multiplicity (g : Graph) : ℤ := (g.card : ℤ) - leftVal g - rightVal g + 1

def leftMap (kp branch : Bool) (i : ℕ) : Option ℕ :=
  if branch then
    if kp then match i with | 1 => some 1 | 2 => some 2 | _ => none
    else none
  else if kp then match i with | 0 => some 0 | 1 => some 1 | 2 => some 1 | _ => none
  else if i < 3 then some i else none

def rightMap (jp kp branch : Bool) (i : ℕ) : Option ℕ :=
  if branch then
    if jp then
      if kp then match i with | 1 => some 1 | 2 => some 0 | _ => none
      else match i with | 0 => some 0 | 2 => some 2 | _ => none
    else if kp then match i with | 1 => some 1 | 2 => some 2 | _ => none
    else none
  else if jp && !kp then match i with | 0 => some 0 | 1 => some 1 | 2 => some 0 | _ => none
  else if jp || kp then match i with | 0 => some 0 | 1 => some 1 | 2 => some 1 | _ => none
  else if i < 3 then some i else none

def transform (e : ℕ) (jp kp l r : Bool) : Graph :=
  ((List.range 9).filterMap fun i =>
    if e.testBit i then do
      let a ← leftMap kp l (i / 3)
      let b ← rightMap jp kp r (i % 3)
      pure (a,b)
    else none).toFinset

def states : List ℕ :=
  [11,17,20,25,26,27,52,77,80,100,152,176,200,201,205,208,216,217,221,244,356,416,484]
def harmless : List ℕ := [11,25,26,52,77,152,176,200,201,208,356,416,484]
def positive : List ℕ := [27,216,217,221]
def negative : List ℕ := [17,20,80,100]
def critical : List ℕ := [17,20,80,100,27,216,217,221,205,244]
def bools : List Bool := [false,true]

def closedCheck : Bool := states.all fun e => bools.all fun j => bools.all fun k =>
  bools.all fun l => bools.all fun r =>
    let g := transform e j k l r
    !bispecial g || states.contains (encode g)

def harmlessCheck : Bool := harmless.all fun e => bools.all fun j => bools.all fun k =>
  bools.all fun l => bools.all fun r =>
    let g := transform e j k l r
    !bispecial g || harmless.contains (encode g)

def signsCheck : Bool := states.all fun e =>
  let m := multiplicity (decode e)
  (decide (m = 1) == positive.contains e) &&
  (decide (m = -1) == negative.contains e) && decide (-1 ≤ m ∧ m ≤ 1)

def nonneutralChildren (e : ℕ) (j k : Bool) : List ℕ :=
  (bools.flatMap fun l => bools.map fun r => transform e j k l r).filterMap fun g =>
    if bispecial g && decide (multiplicity g ≠ 0) then some (encode g) else none

def expected (e : ℕ) (j k : Bool) : List ℕ :=
  match e with
  | 17 => [17]
  | 20 => [if j then 17 else 20]
  | 80 => [80]
  | 100 => [if k then 80 else 100]
  | 27 => [27]
  | 216 => [216]
  | 217 => [if k then 216 else 217]
  | 221 => if k then [27,if j then 17 else 20,216] else [if j then 217 else 221]
  | 205 => if k then [27,if j then 17 else 20] else []
  | 244 => if j && !k then [217,100] else []
  | _ => []

def criticalCheck : Bool := critical.all fun e => bools.all fun j => bools.all fun k =>
  decide (nonneutralChildren e j k = expected e j k)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem classification_closed : closedCheck = true := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem harmless_stays_harmless : harmlessCheck = true := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem multiplicity_classification : signsCheck = true := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem critical_productions : criticalCheck = true := by decide

#print axioms classification_closed
#print axioms harmless_stays_harmless
#print axioms multiplicity_classification
#print axioms critical_productions
end TripExtensionGraphs
```

### `TripLocalMaps.lean`

```lean
import TripBlocks
import ExtensionGraphs

set_option linter.unusedSimpArgs false

namespace Trip

/-- The common terminal affix 1^j3. -/
def affixA (j : ℕ) : Word := run j 0 ++ [2]
/-- The longer terminal affix 2^k1^j3. -/
def affixC (j k : ℕ) : Word := run k 1 ++ affixA j

def leftAffix (j k : ℕ) (l : Bool) : Word := if l then affixC j k else affixA j

def rightAffix (j k : ℕ) (r : Bool) : Word :=
  if r then if k = 0 then run j 0 else run k 1 else []

/-- A preceding block contributes its final letter 3. This padding is essential
    when the selected affix fills the whole current block. -/
def localLeft (j k : ℕ) (l : Bool) (c a : Letter) : Prop :=
  [a] ++ leftAffix j k l <:+ [2] ++ block j k c

def localRight (j k : ℕ) (r : Bool) (c a : Letter) : Prop :=
  rightAffix j k r ++ [a] <+: block j k c

lemma block_zero (j k : ℕ) : block j k 0 = [0] ++ affixA j := by
  simp [block,affixA,run,List.replicate_succ]
lemma block_one (j k : ℕ) : block j k 1 = run (k+1) 1 ++ affixA j := by
  simp [block,affixA,List.append_assoc]
lemma block_two (j k : ℕ) : block j k 2 = run k 1 ++ affixA j := by
  simp [block,affixA,List.append_assoc]

def alphaL (kp l : Bool) (c : Letter) : Option Letter :=
  if l then if kp then if c = 0 then none else some c else none
  else if kp then if c = 0 then some 0 else some 1 else some c

lemma alphaL_bridge (kp l : Bool) (c : Letter) :
    (alphaL kp l c).map Fin.val = TripExtensionGraphs.leftMap kp l c.val := by
  cases kp <;> cases l <;> fin_cases c <;> rfl

/-- The first left-extension column for all j,k, including full-block k=0. -/
theorem left_A_exact (j k : ℕ) (c a : Letter) :
    localLeft j k false c a ↔ alphaL (decide (k ≠ 0)) false c = some a := by
  fin_cases c
  · change ([a] ++ affixA j <:+ [2] ++ block j k 0) ↔ _
    rw [block_zero, ← List.append_assoc,List.suffix_append_self_iff]
    rw [List.singleton_suffix_iff_getLast?_eq_some]
    cases k <;> fin_cases a <;> simp [alphaL]
  · change ([a] ++ affixA j <:+ [2] ++ block j k 1) ↔ _
    rw [block_one, ← List.append_assoc,List.suffix_append_self_iff]
    rw [List.singleton_suffix_iff_getLast?_eq_some,List.getLast?_append]
    cases k <;> fin_cases a <;> simp [run,List.getLast?_replicate,alphaL]
  · change ([a] ++ affixA j <:+ [2] ++ block j k 2) ↔ _
    rw [block_two, ← List.append_assoc,List.suffix_append_self_iff]
    cases k with
    | zero =>
      change ([a] <:+ [2]) ↔ _
      rw [List.singleton_suffix_iff_getLast?_eq_some]
      simp [alphaL,eq_comm]
    | succ k => simp [run,List.replicate_succ',List.append_assoc,alphaL,eq_comm]

lemma run_succ_tail (n : ℕ) (a : Letter) : run (n+1) a = run n a ++ [a] :=
  List.replicate_succ'
lemma run_succ_head (n : ℕ) (a : Letter) : run (n+1) a = [a] ++ run n a := rfl

/-- The second left-extension column, with the required nonempty 2-run. -/
theorem left_C_exact (j k : ℕ) (hk : 0 < k) (c a : Letter) :
    localLeft j k true c a ↔ alphaL true true c = some a := by
  fin_cases c
  · change ([a] ++ affixC j k <:+ [2] ++ block j k 0) ↔ _
    rw [block_zero]
    simp only [affixC,← List.append_assoc,List.suffix_append_self_iff]
    have hh : ¬ ([a] ++ run k 1 <:+ ([2,0] : Word)) := by
      intro h
      obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      have hs : ([1] : Word) <:+ [a] ++ run (k+1) 1 := by
        rw [run_succ_tail,← List.append_assoc]
        exact List.suffix_append _ _
      have ht := hs.trans h
      exact (by decide : ¬ ([1] : Word) <:+ [2,0]) ht
    simpa [alphaL] using hh
  · change ([a] ++ affixC j k <:+ [2] ++ block j k 1) ↔ _
    rw [block_one]
    simp only [affixC,← List.append_assoc,List.suffix_append_self_iff]
    rw [run_succ_head]
    simp only [← List.append_assoc,List.suffix_append_self_iff]
    rw [List.singleton_suffix_iff_getLast?_eq_some]
    simp [alphaL,eq_comm]
  · change ([a] ++ affixC j k <:+ [2] ++ block j k 2) ↔ _
    rw [block_two]
    simp only [affixC,← List.append_assoc,List.suffix_append_self_iff]
    rw [List.singleton_suffix_iff_getLast?_eq_some]
    simp [alphaL,eq_comm]

def alphaR (jp kp r : Bool) (c : Letter) : Option Letter :=
  if r then
    if kp then if c = 0 then none else if c = 1 then some 1
      else if jp then some 0 else some 2
    else if jp then if c = 1 then none else if c = 0 then some 0 else some 2
    else none
  else if c = 0 then some 0 else if c = 1 then some 1
    else if kp then some 1 else if jp then some 0 else some 2

lemma alphaR_bridge (jp kp r : Bool) (c : Letter) :
    (alphaR jp kp r c).map Fin.val = TripExtensionGraphs.rightMap jp kp r c.val := by
  cases jp <;> cases kp <;> cases r <;> fin_cases c <;> rfl

/-- All empty-right-affix columns, without any genericity assumption. -/
theorem right_empty_exact (j k : ℕ) (c a : Letter) :
    localRight j k false c a ↔
      alphaR (decide (j ≠ 0)) (decide (k ≠ 0)) false c = some a := by
  fin_cases c <;> cases j <;> cases k <;>
    simp [localRight,rightAffix,block,run,List.replicate_succ,alphaR,
      List.singleton_prefix_iff_head?_eq_some,eq_comm]

/-- All nonempty-right-affix columns; identical empty choices are excluded. -/
theorem right_run_exact (j k : ℕ) (hjk : 0 < j ∨ 0 < k) (c a : Letter) :
    localRight j k true c a ↔
      alphaR (decide (j ≠ 0)) (decide (k ≠ 0)) true c = some a := by
  fin_cases c
  · change (rightAffix j k true ++ [a] <+: block j k 0) ↔ _
    cases k with
    | zero =>
      change (run j 0 ++ [a] <+: run (j+1) 0 ++ [2]) ↔ _
      rw [run_succ_tail j 0,List.append_assoc,List.prefix_append_right_inj]
      simp [alphaR,show j ≠ 0 by omega,List.singleton_prefix_iff_head?_eq_some,eq_comm]
    | succ k =>
      simp [rightAffix,block,run,List.replicate_succ,alphaR]
  · change (rightAffix j k true ++ [a] <+: block j k 1) ↔ _
    cases k with
    | zero =>
      obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
      simp [rightAffix,block,run,List.replicate_succ,alphaR]
    | succ k =>
      simp only [rightAffix, Nat.succ_ne_zero,↓reduceIte,block_one]
      rw [run_succ_tail (k+1) 1, List.append_assoc,List.prefix_append_right_inj]
      simp [alphaR,List.singleton_prefix_iff_head?_eq_some,eq_comm]
  · change (rightAffix j k true ++ [a] <+: block j k 2) ↔ _
    cases k with
    | zero =>
      change (run j 0 ++ [a] <+: run j 0 ++ [2]) ↔ _
      rw [List.prefix_append_right_inj]
      simp [alphaR,show j ≠ 0 by omega,List.singleton_prefix_iff_head?_eq_some,eq_comm]
    | succ k =>
      simp only [rightAffix,Nat.succ_ne_zero,↓reduceIte,block_two]
      rw [List.prefix_append_right_inj]
      cases j <;> simp [affixA,run,List.replicate_succ,alphaR,
        List.singleton_prefix_iff_head?_eq_some,eq_comm]

#print axioms left_A_exact
#print axioms left_C_exact
#print axioms right_empty_exact
#print axioms right_run_exact
end Trip
```

### `TripLifting.lean`

```lean
import TripLocalMaps

set_option linter.unusedSimpArgs false
namespace Trip

def imageLanguage (L : Word → Prop) (j k : ℕ) (w : Word) : Prop :=
  ∃ u, L u ∧ w <:+: sigma j k u

def extensionEdge (L : Word → Prop) (w : Word) (a b : Letter) : Prop :=
  L ([a] ++ w ++ [b])

def LeftExtendable (L : Word → Prop) : Prop :=
  ∀ w, L w → ∃ x : Letter, L (x :: w)

/-- Direct concatenation proof of the lifting direction. The padding 3 is a
    real preceding block boundary, not an assumed extra factor. -/
theorem padded_context_lifts (j k : ℕ) (l r : Bool) (c d a b : Letter) (v : Word)
    (hl : localLeft j k l c a) (hr : localRight j k r d b) :
    [a] ++ (leftAffix j k l ++ sigma j k v ++ rightAffix j k r) ++ [b]
      <:+: [2] ++ sigma j k (c :: (v ++ [d])) := by
  obtain ⟨p,hp⟩ := hl
  obtain ⟨q,hq⟩ := hr
  refine ⟨p,q,?_⟩
  calc
    p ++ ([a] ++ (leftAffix j k l ++ sigma j k v ++ rightAffix j k r) ++ [b]) ++ q
      = (p ++ ([a] ++ leftAffix j k l)) ++ sigma j k v ++
          ((rightAffix j k r ++ [b]) ++ q) := by simp only [List.append_assoc]
    _ = ([2] ++ block j k c) ++ sigma j k v ++ block j k d := by rw [hp,hq]
    _ = [2] ++ sigma j k (c :: (v ++ [d])) := by simp [sigma,List.append_assoc]

/-- Turn the artificial boundary in the preceding lemma into a terminal letter
    of an actual substituted predecessor. -/
theorem context_lifts (j k : ℕ) (l r : Bool) (x c d a b : Letter) (v : Word)
    (hl : localLeft j k l c a) (hr : localRight j k r d b) :
    [a] ++ (leftAffix j k l ++ sigma j k v ++ rightAffix j k r) ++ [b]
      <:+: sigma j k (x :: c :: (v ++ [d])) := by
  have hp := padded_context_lifts j k l r c d a b v hl hr
  obtain ⟨u,hu⟩ := block_ends j k x
  have hs : [2] ++ sigma j k (c :: (v ++ [d]))
      <:+ sigma j k (x :: c :: (v ++ [d])) := by
    refine ⟨u,?_⟩
    simp only [sigma,List.flatMap_cons] at *
    rw [hu]
    simp only [List.append_assoc]
  exact hp.trans hs.isInfix

/-- Every antecedent edge whose two endpoint maps survive produces an actual
    edge of the morphic image language. The reverse inclusion and the unique
    parsing theorem are intentionally not asserted here. -/
theorem extension_edge_lifts (L : Word → Prop) (hL : LeftExtendable L)
    (j k : ℕ) (l r : Bool) (hlvalid : l = true → 0 < k)
    (hrvalid : r = true → 0 < j ∨ 0 < k) (v : Word) (c d a b : Letter)
    (he : extensionEdge L v c d)
    (ha : alphaL (decide (k ≠ 0)) l c = some a)
    (hb : alphaR (decide (j ≠ 0)) (decide (k ≠ 0)) r d = some b) :
    extensionEdge (imageLanguage L j k)
      (leftAffix j k l ++ sigma j k v ++ rightAffix j k r) a b := by
  have hl : localLeft j k l c a := by
    cases l with
    | false => exact (left_A_exact j k c a).mpr ha
    | true =>
      have hk := hlvalid rfl
      have hh : decide (k ≠ 0) = true := by simp [show k ≠ 0 by omega]
      exact (left_C_exact j k hk c a).mpr (hh ▸ ha)
  have hr : localRight j k r d b := by
    cases r with
    | false => exact (right_empty_exact j k d b).mpr hb
    | true => exact (right_run_exact j k (hrvalid rfl) d b).mpr hb
  obtain ⟨x,hx⟩ := hL _ he
  exact ⟨x :: c :: (v ++ [d]),hx,context_lifts j k l r x c d a b v hl hr⟩

#print axioms padded_context_lifts
#print axioms context_lifts
#print axioms extension_edge_lifts
end Trip
```

### `PairCones.lean`

```lean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/- Elementary algebra for PROOF-365088.md. This file does not formalize the
   S-adic language endpoint or the parsing/production lemma. -/
namespace TripPairCones

abbrev Vec := ℤ × ℤ × ℤ

def Nonneg (v : Vec) : Prop := 0 ≤ v.1 ∧ 0 ≤ v.2.1 ∧ 0 ≤ v.2.2
def Cone (v : Vec) : Prop := 0 ≤ v.1 ∧ 0 ≤ v.2.1 ∧ 1 ≤ v.2.2

def M (j k : ℤ) (v : Vec) : Vec :=
  ((j + 1) * v.1 + j * v.2.1 + j * v.2.2,
   (k + 1) * v.2.1 + k * v.2.2,
   v.1 + v.2.1 + v.2.2)

theorem nonneg_map (j k : ℤ) (hj : 0 ≤ j) (hk : 0 ≤ k)
    (v : Vec) (hv : Nonneg v) : Nonneg (M j k v) := by
  rcases hv with ⟨ha, hb, hc⟩
  dsimp [Nonneg, M]
  constructor
  · positivity
  constructor
  · positivity
  · omega

theorem cone_map (j k : ℤ) (hj : 0 ≤ j) (hk : 0 ≤ k)
    (v : Vec) (hv : Cone v) : Cone (M j k v) := by
  rcases hv with ⟨ha, hb, hc⟩
  dsimp [Cone, M]
  constructor
  · positivity
  constructor
  · have : 0 ≤ v.2.2 := by omega
    positivity
  · omega

theorem cone_sub_first (j k : ℤ) (hj : 0 ≤ j) (hk : 0 ≤ k)
    (v : Vec) (hv : Cone v) :
    Cone ((M j k v).1 - j, (M j k v).2.1, (M j k v).2.2) := by
  rcases hv with ⟨ha, hb, hc⟩
  dsimp [Cone, M]
  constructor
  · have h1 := mul_nonneg (show 0 ≤ j + 1 by omega) ha
    have h2 := mul_nonneg hj hb
    have h3 := mul_nonneg hj (show 0 ≤ v.2.2 - 1 by omega)
    nlinarith
  constructor
  · have : 0 ≤ v.2.2 := by omega
    positivity
  · omega

theorem cone_sub_second (j k : ℤ) (hj : 0 ≤ j) (hk : 0 ≤ k)
    (v : Vec) (hv : Cone v) :
    Cone ((M j k v).1, (M j k v).2.1 - k, (M j k v).2.2) := by
  rcases hv with ⟨ha, hb, hc⟩
  dsimp [Cone, M]
  constructor
  · have : 0 ≤ v.2.2 := by omega
    positivity
  constructor
  · have h1 := mul_nonneg (show 0 ≤ k + 1 by omega) hb
    have h2 := mul_nonneg hk (show 0 ≤ v.2.2 - 1 by omega)
    nlinarith
  · omega

theorem nonneg_add_second (j k : ℤ) (hj : 0 ≤ j) (hk : 0 ≤ k)
    (v : Vec) (hv : Nonneg v) :
    Nonneg ((M j k v).1, (M j k v).2.1 + k, (M j k v).2.2) := by
  have h := nonneg_map j k hj hk v hv
  dsimp [Nonneg] at *
  omega

theorem seed_first (j k : ℤ) (hj : 0 ≤ j) (hk : 0 ≤ k)
    (v : Vec) (hv : Nonneg v) :
    Cone ((M j k v).1, (M j k v).2.1, (M j k v).2.2 + 1) := by
  have h := nonneg_map j k hj hk v hv
  dsimp [Nonneg, Cone] at *
  omega

theorem seed_second (j k : ℤ) (hj : 0 ≤ j) (hk : 0 ≤ k)
    (v : Vec) (hv : Nonneg v) :
    Cone ((M j k v).1, (M j k v).2.1 + k, (M j k v).2.2 + 1) := by
  have h := nonneg_map j k hj hk v hv
  dsimp [Nonneg, Cone] at *
  omega

#print axioms cone_sub_first
#print axioms cone_sub_second
#print axioms seed_second
end TripPairCones
```

### `TripParse.lean`

```lean
import TripLifting

/-! Unique parsing (desubstitution) for the double-Gauss substitution sigma j k.
Every block is a 3-free body followed by the letter 3 (Lean letter 2), so every
3 of sigma u is a block end. Everything here holds for symbolic j, k. -/

set_option linter.unusedSimpArgs false

namespace Trip

def Factorial (L : Word → Prop) : Prop := ∀ u v, L u → v <:+: u → L v

def body (j k : ℕ) (c : Letter) : Word :=
  if c = 0 then run (j+1) 0 else if c = 1 then run (k+1) 1 ++ run j 0 else run k 1 ++ run j 0

lemma block_eq_body (j k : ℕ) (c : Letter) : block j k c = body j k c ++ [2] := by
  unfold block body; split_ifs <;> simp [List.append_assoc]

lemma two_not_mem_body (j k : ℕ) (c : Letter) : (2 : Letter) ∉ body j k c := by
  unfold body; split_ifs <;> simp [run, List.mem_replicate]

lemma body_inj {j k : ℕ} {c c' : Letter} (h : body j k c = body j k c') : c = c' := by
  have h0 := congrArg (List.count (0 : Letter)) h
  have h1 := congrArg (List.count (1 : Letter)) h
  fin_cases c <;> fin_cases c' <;> simp [body, run, List.count_replicate] at h0 h1 ⊢

lemma sigma_nil (j k : ℕ) : sigma j k [] = [] := rfl

lemma sigma_cons (j k : ℕ) (c : Letter) (u : Word) :
    sigma j k (c :: u) = body j k c ++ 2 :: sigma j k u := by
  simp [sigma, block_eq_body, List.append_assoc]

lemma sigma_singleton (j k : ℕ) (c : Letter) : sigma j k [c] = block j k c := by
  simp [sigma]

lemma sigma_eq_nil {j k : ℕ} {u : Word} (h : sigma j k u = []) : u = [] := by
  cases u with
  | nil => rfl
  | cons c u => rw [sigma_cons] at h; simp at h

/-- The first 3 of `X ++ 3 :: S`, with X 3-free, is the displayed one. -/
lemma split_first_two {X S A R : Word} (hX : (2 : Letter) ∉ X)
    (h : X ++ 2 :: S = A ++ 2 :: R) :
    (A = X ∧ R = S) ∨ ∃ A', A = X ++ 2 :: A' ∧ S = A' ++ 2 :: R := by
  rcases List.append_eq_append_iff.mp h with ⟨a', hA, hS⟩ | ⟨c', hX', hR⟩
  · cases a' with
    | nil => left; simp at hA hS; exact ⟨hA, hS.symm⟩
    | cons y a'' =>
      right; simp at hS; obtain ⟨rfl, hS⟩ := hS; exact ⟨a'', hA, hS⟩
  · cases c' with
    | nil => left; simp at hX' hR; exact ⟨hX'.symm, hR⟩
    | cons y c'' =>
      simp at hR; obtain ⟨rfl, -⟩ := hR
      exact absurd (by rw [hX']; simp) hX

lemma eq_of_first_two {X S X' S' : Word} (hX : (2 : Letter) ∉ X) (hX' : (2 : Letter) ∉ X')
    (h : X ++ 2 :: S = X' ++ 2 :: S') : X = X' ∧ S = S' := by
  rcases split_first_two hX h with ⟨h1, h2⟩ | ⟨A', h1, -⟩
  · exact ⟨h1.symm, h2.symm⟩
  · exact absurd (by rw [h1]; simp) hX'

/-- Split lemma: every 3 in sigma u ends a block. -/
theorem sigma_split {j k : ℕ} : ∀ (u A R : Word), sigma j k u = A ++ 2 :: R →
    ∃ u₁ u₂, u = u₁ ++ u₂ ∧ sigma j k u₁ = A ++ [2] ∧ sigma j k u₂ = R
  | [], A, R, h => by simp [sigma] at h
  | c :: u, A, R, h => by
    rw [sigma_cons] at h
    rcases split_first_two (two_not_mem_body j k c) h with ⟨rfl, rfl⟩ | ⟨A', rfl, hS⟩
    · exact ⟨[c], u, rfl, by simp [sigma_cons, sigma_nil], rfl⟩
    · obtain ⟨v₁, v₂, rfl, h1, h2⟩ := sigma_split u A' R hS
      exact ⟨c :: v₁, v₂, rfl, by rw [sigma_cons, h1]; simp, h2⟩

theorem sigma_inj {j k : ℕ} : ∀ (u v : Word), sigma j k u = sigma j k v → u = v
  | u, [], h => sigma_eq_nil h
  | u, c :: v, h => by
    rw [sigma_cons] at h
    obtain ⟨u₁, u₂, rfl, h1, h2⟩ := sigma_split u _ _ h
    have hv := sigma_inj u₂ v h2
    subst hv
    cases u₁ with
    | nil => simp [sigma] at h1
    | cons e u₁ =>
      rw [sigma_cons] at h1
      have := eq_of_first_two (two_not_mem_body j k e) (two_not_mem_body j k c) h1
      rw [body_inj this.1, sigma_eq_nil this.2]
      rfl

theorem sigma_prefix {j k : ℕ} : ∀ (v u R : Word), sigma j k u = sigma j k v ++ R →
    ∃ u', u = v ++ u' ∧ sigma j k u' = R
  | [], u, R, h => ⟨u, rfl, h⟩
  | c :: v, u, R, h => by
    rw [sigma_cons, List.append_assoc] at h
    obtain ⟨u₁, u₂, rfl, h1, h2⟩ := sigma_split u _ _ h
    have hc : u₁ = [c] := sigma_inj _ _ (h1.trans (by rw [sigma_cons]; rfl))
    subst hc
    obtain ⟨u', rfl, h'⟩ := sigma_prefix v u₂ R h2.symm.symm
    exact ⟨u', rfl, h'⟩

lemma sigma_concat (j k : ℕ) (u : Word) (c : Letter) :
    sigma j k (u ++ [c]) = sigma j k u ++ body j k c ++ [2] := by
  simp [sigma, block_eq_body, List.append_assoc]

lemma exists_concat {u : Word} (hu : u ≠ []) : ∃ u' c, u = u' ++ [c] := by
  obtain ⟨u', c, h⟩ := (List.eq_nil_or_concat u).resolve_left hu
  exact ⟨u', c, by simpa using h⟩

lemma sigma_last {j k : ℕ} {u : Word} (hu : u ≠ []) : ∃ S, sigma j k u = S ++ [2] := by
  obtain ⟨u', c, rfl⟩ := exists_concat hu
  exact ⟨sigma j k u' ++ body j k c, by rw [sigma_concat]⟩

/-- A 3-free word followed by z, read inside `body ++ 3 :: S`, is a prefix of the block. -/
lemma prefix_block_of {Bd S B Q : Word} {z : Letter} (hB : (2 : Letter) ∉ B)
    (h : Bd ++ 2 :: S = B ++ z :: Q) : B ++ [z] <+: Bd ++ [2] := by
  rcases List.append_eq_append_iff.mp h with ⟨a', hA, hS⟩ | ⟨c', hX', hR⟩
  · cases a' with
    | nil => simp at hA hS; rw [hA, hS.1]
    | cons y a'' =>
      simp at hS; obtain ⟨rfl, -⟩ := hS
      exact absurd (by rw [hA]; simp) hB
  · cases c' with
    | nil => simp at hX' hR; rw [hX', ← hR.1]
    | cons y c'' =>
      simp at hR; obtain ⟨rfl, -⟩ := hR
      rw [hX']
      exact ⟨c'' ++ [2], by simp⟩

/-- The letter before a 3-free word x read at the end of a block, padded by the
previous block's final 3. -/
lemma suffix_pad_of {P S Bd x : Word} {y : Letter} (hx : (2 : Letter) ∉ x)
    (hS : S = [] ∨ ∃ S', S = S' ++ [2]) (h : P ++ y :: x = S ++ Bd) :
    y :: x <:+ 2 :: Bd := by
  have h1 : y :: x <:+ S ++ Bd := ⟨P, h⟩
  have h2 : Bd <:+ S ++ Bd := List.suffix_append S Bd
  rcases le_or_gt (y :: x).length Bd.length with hl | hl
  · exact (List.suffix_of_suffix_length_le h1 h2 hl).trans (List.suffix_cons 2 Bd)
  · rcases hS with rfl | ⟨S', rfl⟩
    · have := h1.length_le; simp at this hl; omega
    · have h3 : 2 :: Bd <:+ S' ++ [2] ++ Bd := ⟨S', by simp⟩
      have h4 := List.suffix_of_suffix_length_le h3 h1 (by simp at hl ⊢; omega)
      rcases le_or_gt (y :: x).length (2 :: Bd).length with hl' | hl'
      · rw [List.IsSuffix.eq_of_length_le h4 hl']
      · -- then 2 :: Bd is a suffix of x, impossible
        have h5 : 2 :: Bd <:+ x := by
          obtain ⟨t, ht⟩ := h4
          cases t with
          | nil => exfalso; simp at ht; obtain ⟨-, rfl⟩ := ht; simp at hl'
          | cons a t => simp at ht; exact ⟨t, ht.2⟩
        exact absurd (h5.subset (by simp)) hx

/-- A 3-free infix of `X ++ 3 :: Y` lies in X or in Y. -/
lemma infix_two_split {T X Y : Word} (hT : (2 : Letter) ∉ T) (h : T <:+: X ++ 2 :: Y) :
    T <:+: X ∨ T <:+: Y := by
  obtain ⟨P, Q, h⟩ := h
  rw [List.append_assoc] at h
  rcases List.append_eq_append_iff.mp h with ⟨a', hA, hS⟩ | ⟨c', hX', hR⟩
  · -- X = P ++ a', T ++ Q = a' ++ 2 :: Y
    rcases List.append_eq_append_iff.mp hS with ⟨e, he1, he2⟩ | ⟨f, hf1, hf2⟩
    · left; exact ⟨P, e, by rw [hA, he1]; simp⟩
    · cases f with
      | nil => left; simp at hf1; exact ⟨P, [], by rw [hA, hf1]; simp⟩
      | cons b f =>
        simp at hf2; obtain ⟨rfl, -⟩ := hf2
        exact absurd (by rw [hf1]; simp) hT
  · -- P = X ++ c', 2 :: Y = c' ++ T ++ Q
    cases c' with
    | nil =>
      simp at hR
      cases T with
      | nil => left; exact List.nil_infix
      | cons t T => simp at hR; obtain ⟨rfl, -⟩ := hR; simp at hT
    | cons b c'' =>
      simp at hR; obtain ⟨rfl, hR⟩ := hR
      right; exact ⟨c'', Q, by rw [hR]; simp⟩

lemma infix_body_of_free {j k : ℕ} {T : Word} (hT : (2 : Letter) ∉ T) :
    ∀ u, T <:+: sigma j k u → T = [] ∨ ∃ c ∈ u, T <:+: body j k c
  | [], h => by left; simpa [sigma] using h
  | c :: u, h => by
    rw [sigma_cons] at h
    rcases infix_two_split hT h with h | h
    · right; exact ⟨c, by simp, h⟩
    · rcases infix_body_of_free hT u h with h | ⟨e, he, h⟩
      · left; exact h
      · right; exact ⟨e, by simp [he], h⟩

/-! Image languages and the exact extension characterisation. -/

theorem image_factorial (L : Word → Prop) (j k : ℕ) : Factorial (imageLanguage L j k) := by
  rintro u v ⟨x, hx, hu⟩ hv
  exact ⟨x, hx, hv.trans hu⟩

/-- Extension edges of a word containing a 3: exact characterisation by the
antecedent edges and the padded-block suffix/prefix relations. -/
theorem image_edge_iff (L : Word → Prop) (hfac : Factorial L) (hext : LeftExtendable L)
    (j k : ℕ) (x B v : Word) (hx : (2 : Letter) ∉ x) (hB : (2 : Letter) ∉ B) (y z : Letter) :
    extensionEdge (imageLanguage L j k) (x ++ 2 :: (sigma j k v ++ B)) y z ↔
      ∃ c d, L (c :: (v ++ [d])) ∧ y :: (x ++ [2]) <:+ 2 :: block j k c ∧
        B ++ [z] <+: block j k d := by
  constructor
  · rintro ⟨u, hu, P, Q, h⟩
    have h' : sigma j k u = (P ++ y :: x) ++ 2 :: (sigma j k v ++ (B ++ z :: Q)) := by
      rw [← h]; simp
    obtain ⟨u₁, u₂, rfl, h1, h2⟩ := sigma_split u _ _ h'
    obtain ⟨u₃, rfl, h3⟩ := sigma_prefix v u₂ _ h2
    cases u₃ with
    | nil => simp [sigma] at h3
    | cons d u₄ =>
      rw [sigma_cons] at h3
      have hd := prefix_block_of hB h3
      have hu₁ : u₁ ≠ [] := by rintro rfl; simp [sigma] at h1
      obtain ⟨u₅, c, rfl⟩ := exists_concat hu₁
      rw [sigma_concat] at h1
      have h1' : P ++ y :: x = sigma j k u₅ ++ body j k c := by
        have h2' : (P ++ y :: x) ++ [2] = (sigma j k u₅ ++ body j k c) ++ [2] := by
          simpa [List.append_assoc] using h1.symm
        exact List.append_cancel_right h2'
      have hS : sigma j k u₅ = [] ∨ ∃ S', sigma j k u₅ = S' ++ [2] := by
        rcases eq_or_ne u₅ [] with rfl | hne
        · left; rfl
        · right; exact sigma_last hne
      have hc := suffix_pad_of hx hS h1'
      refine ⟨c, d, hfac _ _ hu ⟨u₅, u₄, by simp⟩, ?_, ?_⟩
      · obtain ⟨t, ht⟩ := hc
        refine ⟨t, ?_⟩
        rw [block_eq_body, show 2 :: (body j k c ++ [2]) = (2 :: body j k c) ++ [2] by simp, ← ht]
        simp
      · rw [block_eq_body]; exact hd
  · rintro ⟨c, d, hcd, ⟨p, hp⟩, ⟨q, hq⟩⟩
    obtain ⟨e, he⟩ := hext _ hcd
    refine ⟨e :: c :: (v ++ [d]), he, ?_⟩
    obtain ⟨S, hS⟩ : ∃ S, block j k e = S ++ [2] := ⟨body j k e, block_eq_body j k e⟩
    refine ⟨S ++ p, q, ?_⟩
    have : sigma j k (e :: c :: (v ++ [d])) =
        S ++ (2 :: block j k c) ++ sigma j k v ++ block j k d := by
      simp [sigma, hS, List.append_assoc]
    rw [this, ← hp, ← hq]
    simp [List.append_assoc]

/-- Extension edges of a 3-free word: they are exactly the windows of the
padded blocks. -/
theorem image_edge_free_iff (L : Word → Prop) (hext : LeftExtendable L)
    (hall : ∀ c : Letter, L [c]) (j k : ℕ) (w : Word) (hw : (2 : Letter) ∉ w) (y z : Letter) :
    extensionEdge (imageLanguage L j k) w y z ↔
      ∃ c, [y] ++ w ++ [z] <:+: 2 :: block j k c := by
  constructor
  · rintro ⟨u, hu, P, Q, h⟩
    by_cases hy : y = 2
    · subst hy
      have h' : sigma j k u = P ++ 2 :: (w ++ z :: Q) := by rw [← h]; simp
      obtain ⟨u₁, u₂, rfl, -, h2⟩ := sigma_split u _ _ h'
      cases u₂ with
      | nil => simp [sigma] at h2
      | cons d u₄ =>
        rw [sigma_cons] at h2
        have hd := prefix_block_of hw h2
        refine ⟨d, ?_⟩
        rw [block_eq_body]
        obtain ⟨t, ht⟩ := hd
        exact ⟨[], t, by simp [← ht]⟩
    · by_cases hz : z = 2
      · subst hz
        have h' : sigma j k u = (P ++ y :: w) ++ 2 :: Q := by rw [← h]; simp
        obtain ⟨u₁, u₂, rfl, h1, -⟩ := sigma_split u _ _ h'
        have hu₁ : u₁ ≠ [] := by rintro rfl; simp [sigma] at h1
        obtain ⟨u₅, c, rfl⟩ := exists_concat hu₁
        rw [sigma_concat] at h1
        have h1' : P ++ y :: w = sigma j k u₅ ++ body j k c := by
          have h2' : (P ++ y :: w) ++ [2] = (sigma j k u₅ ++ body j k c) ++ [2] := by
            simpa [List.append_assoc] using h1.symm
          exact List.append_cancel_right h2'
        have hS : sigma j k u₅ = [] ∨ ∃ S', sigma j k u₅ = S' ++ [2] := by
          rcases eq_or_ne u₅ [] with rfl | hne
          · left; rfl
          · right; exact sigma_last hne
        have hc := suffix_pad_of hw hS h1'
        refine ⟨c, ?_⟩
        obtain ⟨t, ht⟩ := hc
        refine ⟨t, [], ?_⟩
        rw [block_eq_body, show 2 :: (body j k c ++ [2]) = (2 :: body j k c) ++ [2] by simp, ← ht]
        simp
      · have hT : (2 : Letter) ∉ [y] ++ w ++ [z] := by
          simp [hw, Ne.symm hy, Ne.symm hz]
        rcases infix_body_of_free hT u ⟨P, Q, h⟩ with h0 | ⟨c, -, hc⟩
        · simp at h0
        · refine ⟨c, hc.trans ?_⟩
          rw [block_eq_body]
          exact ⟨[2], [2], by simp⟩
  · rintro ⟨c, hc⟩
    obtain ⟨e, he⟩ := hext _ (hall c)
    refine ⟨[e, c], he, hc.trans ?_⟩
    refine ⟨body j k e, [], ?_⟩
    simp [sigma, block_eq_body, List.append_assoc]

/-- Unique parse: x, B and v are recovered from x 3 sigma(v) B. -/
theorem parse_unique {j k : ℕ} {x B v x' B' v' : Word} (hx : (2 : Letter) ∉ x)
    (hB : (2 : Letter) ∉ B) (hx' : (2 : Letter) ∉ x') (hB' : (2 : Letter) ∉ B')
    (h : x ++ 2 :: (sigma j k v ++ B) = x' ++ 2 :: (sigma j k v' ++ B')) :
    x = x' ∧ v = v' ∧ B = B' := by
  obtain ⟨rfl, h'⟩ := eq_of_first_two hx hx' h
  refine ⟨rfl, ?_⟩
  -- compare the last 3
  have key : ∀ {v v' B B' : Word}, (2 : Letter) ∉ B → (2 : Letter) ∉ B' →
      sigma j k v ++ B = sigma j k v' ++ B' → v.length ≤ v'.length → v = v' ∧ B = B' := by
    intro v v' B B' hB hB' h hl
    rcases List.append_eq_append_iff.mp h with ⟨a', hA, hS⟩ | ⟨c', hX', hR⟩
    · -- sigma v' = sigma v ++ a', B = a' ++ B'
      obtain ⟨u', rfl, hu'⟩ := sigma_prefix v v' a' hA
      cases u' with
      | nil => simp [sigma] at hu'; subst hu'; simp at hS; exact ⟨by simp, hS⟩
      | cons d u => rw [sigma_cons] at hu'; exact absurd (by rw [hS, ← hu']; simp) hB
    · obtain ⟨u', rfl, hu'⟩ := sigma_prefix v' v c' hX'
      cases u' with
      | nil => simp [sigma] at hu'; subst hu'; simp at hR; exact ⟨by simp, hR.symm⟩
      | cons d u => simp at hl
  rcases le_total v.length v'.length with hl | hl
  · exact key hB hB' h' hl
  · obtain ⟨h1, h2⟩ := key hB' hB h'.symm hl
    exact ⟨h1.symm, h2.symm⟩

#print axioms sigma_split
#print axioms image_edge_iff
#print axioms image_edge_free_iff
#print axioms parse_unique
end Trip
```

### `TripAffixes.lean`

```lean
import TripParse

/-! Exclusion of all other special affixes, without enumerating affixes: if two
different letters precede the same suffix in two padded blocks, that suffix is
the longest common suffix of the two padded blocks. Then the exact extension
maps of a child aσ(v)b and the parse of every bispecial factor containing 3. -/

set_option linter.unusedSimpArgs false

namespace Trip

lemma suffix_same_len {s P : Word} {y y' : Letter} (h1 : y :: s <:+ P) (h2 : y' :: s <:+ P) :
    y = y' := by
  have := (List.suffix_of_suffix_length_le h1 h2 (by simp)).eq_of_length_le (by simp)
  simpa using this

lemma prefix_same_len {s P : Word} {y y' : Letter} (h1 : s ++ [y] <+: P) (h2 : s ++ [y'] <+: P) :
    y = y' := by
  have := (List.prefix_of_prefix_length_le h1 h2 (by simp)).eq_of_length_le (by simp)
  simpa using this

/-- Two equal-length suffixes of a common word coincide: the longest common suffix. -/
lemma common_suffix {P Q s t : Word} {y y' z z' : Letter} (hy : y ≠ y') (hz : z ≠ z')
    (h1 : y :: s <:+ P) (h2 : y' :: s <:+ Q) (h3 : z :: t <:+ P) (h4 : z' :: t <:+ Q) :
    s = t := by
  have key : ∀ {s t : Word} {y y' z z' : Letter}, y ≠ y' → y :: s <:+ P → y' :: s <:+ Q →
      z :: t <:+ P → z' :: t <:+ Q → s.length < t.length → False := by
    intro s t y y' z z' hy h1 h2 h3 h4 hl
    have ht : t <:+ P := (List.suffix_cons z t).trans h3
    have ht' : t <:+ Q := (List.suffix_cons z' t).trans h4
    have a1 := List.suffix_of_suffix_length_le h1 ht (by simp; omega)
    have a2 := List.suffix_of_suffix_length_le h2 ht' (by simp; omega)
    exact hy (suffix_same_len a1 a2)
  rcases lt_trichotomy s.length t.length with hl | hl | hl
  · exact (key hy h1 h2 h3 h4 hl).elim
  · have hs : s <:+ P := (List.suffix_cons y s).trans h1
    have ht : t <:+ P := (List.suffix_cons z t).trans h3
    exact (List.suffix_of_suffix_length_le hs ht hl.le).eq_of_length_le hl.ge
  · exact (key hz h3 h4 h1 h2 hl).elim

lemma common_prefix {P Q s t : Word} {y y' z z' : Letter} (hy : y ≠ y') (hz : z ≠ z')
    (h1 : s ++ [y] <+: P) (h2 : s ++ [y'] <+: Q) (h3 : t ++ [z] <+: P) (h4 : t ++ [z'] <+: Q) :
    s = t := by
  have h1' := List.reverse_suffix.mpr h1
  have h2' := List.reverse_suffix.mpr h2
  have h3' := List.reverse_suffix.mpr h3
  have h4' := List.reverse_suffix.mpr h4
  simp only [List.reverse_append, List.reverse_singleton, List.singleton_append] at h1' h2' h3' h4'
  exact List.reverse_injective (common_suffix hy hz h1' h2' h3' h4')

/-- Distinguishing witnesses for the left maps, one per pair of blocks. -/
lemma left_witness (j k : ℕ) (c c' : Letter) (hcc : c ≠ c') :
    ∃ a a' s0, a ≠ a' ∧ a :: s0 <:+ 2 :: block j k c ∧ a' :: s0 <:+ 2 :: block j k c' ∧
      (s0 = run j 0 ++ [2] ∨ (0 < k ∧ s0 = run k 1 ++ run j 0 ++ [2])) := by
  have w0 : (0 : Letter) :: (run j 0 ++ [2]) <:+ 2 :: block j k 0 :=
    ⟨[2], by rw [block_zero]; simp [affixA]⟩
  have w1 : (1 : Letter) :: (run j 0 ++ [2]) <:+ 2 :: block j k 1 :=
    ⟨2 :: run k 1, by rw [block_one, run_succ_tail]; simp [affixA]⟩
  have v1 : (1 : Letter) :: (run k 1 ++ run j 0 ++ [2]) <:+ 2 :: block j k 1 :=
    ⟨[2], by rw [block_one]; simp [affixA, run, List.replicate_succ]⟩
  have v2 : (2 : Letter) :: (run k 1 ++ run j 0 ++ [2]) <:+ 2 :: block j k 2 :=
    ⟨[], by rw [block_two]; simp [affixA]⟩
  have w2 : ∃ a : Letter, a ≠ 0 ∧ a :: (run j 0 ++ [2]) <:+ 2 :: block j k 2 := by
    cases k with
    | zero => exact ⟨2, by decide, ⟨[], by rw [block_two]; simp [affixA, run]⟩⟩
    | succ k => exact ⟨1, by decide, ⟨2 :: run k 1, by rw [block_two, run_succ_tail]; simp [affixA]⟩⟩
  obtain ⟨a2, ha2, w2⟩ := w2
  have hk : ∀ s0 : Word, s0 = run j 0 ++ [2] → s0 = run j 0 ++ [2] ∨
      (0 < k ∧ s0 = run k 1 ++ run j 0 ++ [2]) := fun s0 h => Or.inl h
  fin_cases c <;> fin_cases c' <;> simp at hcc
  · exact ⟨0, 1, _, by decide, w0, w1, Or.inl rfl⟩
  · exact ⟨0, a2, _, Ne.symm ha2, w0, w2, Or.inl rfl⟩
  · exact ⟨1, 0, _, by decide, w1, w0, Or.inl rfl⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact ⟨1, 2, _, by decide, v1, v2, Or.inl (by simp [run])⟩
    · exact ⟨1, 2, _, by decide, v1, v2, Or.inr ⟨hk0, rfl⟩⟩
  · exact ⟨a2, 0, _, ha2, w2, w0, Or.inl rfl⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact ⟨2, 1, _, by decide, v2, v1, Or.inl (by simp [run])⟩
    · exact ⟨2, 1, _, by decide, v2, v1, Or.inr ⟨hk0, rfl⟩⟩

/-- A left-special affix is 1^j 3, or 2^k 1^j 3 with k > 0. -/
theorem left_affix_cases {j k : ℕ} {x : Word} {c c' y y' : Letter}
    (h1 : y :: (x ++ [2]) <:+ 2 :: block j k c) (h2 : y' :: (x ++ [2]) <:+ 2 :: block j k c')
    (hy : y ≠ y') : x = run j 0 ∨ (0 < k ∧ x = run k 1 ++ run j 0) := by
  by_cases hcc : c = c'
  · subst hcc; exact absurd (suffix_same_len h1 h2) hy
  obtain ⟨a, a', s0, ha, wa, wa', hs0⟩ := left_witness j k c c' hcc
  have := common_suffix hy ha h1 h2 wa wa'
  rcases hs0 with rfl | ⟨hk, rfl⟩
  · left; exact List.append_cancel_right this
  · right; exact ⟨hk, List.append_cancel_right (by simpa [List.append_assoc] using this)⟩

lemma right_witness (j k : ℕ) (c c' : Letter) (hcc : c ≠ c') :
    ∃ a a' s0, a ≠ a' ∧ s0 ++ [a] <+: block j k c ∧ s0 ++ [a'] <+: block j k c' ∧
      (s0 = [] ∨ s0 = rightAffix j k true) := by
  have b0 : block j k 0 = (0 : Letter) :: (run j 0 ++ [2]) := by
    simp [block, run, List.replicate_succ]
  have b1 : block j k 1 = run k 1 ++ (1 : Letter) :: (run j 0 ++ [2]) := by
    simp [block, run, List.replicate_succ', List.append_assoc]
  have b2 : block j k 2 = run k 1 ++ run j 0 ++ [2] := by simp [block, List.append_assoc]
  -- the first letters
  have f0 : [] ++ [(0 : Letter)] <+: block j k 0 := by rw [b0]; simp
  have f1 : [] ++ [(1 : Letter)] <+: block j k 1 := by
    rw [b1]; cases k <;> simp [run, List.replicate_succ]
  -- block 3 against blocks 1 and 2
  have g12 : ∃ a : Letter, a ≠ 1 ∧ run k 1 ++ [a] <+: block j k 2 := by
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · exact ⟨2, by decide, by rw [b2]; simp [run]⟩
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
      exact ⟨0, by decide, by rw [b2]; simp [run, List.replicate_succ, List.append_assoc]⟩
  have h12 : run k 1 ++ [(1 : Letter)] <+: block j k 1 := by
    rw [b1]; simp [run, List.replicate_succ, List.append_assoc]
  obtain ⟨a12, ha12, g12⟩ := g12
  have g02 : ∃ a a' s0, a ≠ a' ∧ s0 ++ [a] <+: block j k 0 ∧ s0 ++ [a'] <+: block j k 2 ∧
      (s0 = [] ∨ s0 = rightAffix j k true) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rcases Nat.eq_zero_or_pos j with rfl | hj
      · exact ⟨0, 2, [], by decide, by rw [b0]; simp [run], by rw [b2]; simp [run], Or.inl rfl⟩
      · refine ⟨0, 2, run j 0, by decide, ?_, ?_, Or.inr (by simp [rightAffix])⟩
        · rw [b0]; exact ⟨[2], by simp [run, ← List.replicate_succ', List.replicate_succ]⟩
        · rw [b2]; simp [run]
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      exact ⟨0, 1, [], by decide, f0, by rw [b2]; simp [run, List.replicate_succ], Or.inl rfl⟩
  have hra : run k 1 = [] ∨ run k 1 = rightAffix j k true := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · left; rfl
    · right; simp [rightAffix, show k ≠ 0 by omega]
  fin_cases c <;> fin_cases c' <;> simp at hcc
  · exact ⟨0, 1, [], by decide, f0, f1, Or.inl rfl⟩
  · exact g02
  · exact ⟨1, 0, [], by decide, f1, f0, Or.inl rfl⟩
  · exact ⟨1, a12, _, Ne.symm ha12, h12, g12, hra⟩
  · obtain ⟨a, a', s0, h, h1, h2, h3⟩ := g02
    exact ⟨a', a, s0, Ne.symm h, h2, h1, h3⟩
  · exact ⟨a12, 1, _, ha12, g12, h12, hra⟩

/-- A right-special affix is empty or the run displayed by `rightAffix j k true`. -/
theorem right_affix_cases {j k : ℕ} {B : Word} {d d' z z' : Letter}
    (h1 : B ++ [z] <+: block j k d) (h2 : B ++ [z'] <+: block j k d') (hz : z ≠ z') :
    B = [] ∨ B = rightAffix j k true := by
  by_cases hdd : d = d'
  · subst hdd; exact absurd (prefix_same_len h1 h2) hz
  obtain ⟨a, a', s0, ha, wa, wa', hs0⟩ := right_witness j k d d' hdd
  have := common_prefix hz ha h1 h2 wa wa'
  rw [this]; exact hs0

lemma two_not_mem_run_zero (n : ℕ) : (2 : Letter) ∉ run n 0 := by simp [run, List.mem_replicate]
lemma two_not_mem_run_one (n : ℕ) : (2 : Letter) ∉ run n 1 := by simp [run, List.mem_replicate]

lemma two_not_mem_rightAffix (j k : ℕ) (r : Bool) : (2 : Letter) ∉ rightAffix j k r := by
  unfold rightAffix; split_ifs <;> simp [run, List.mem_replicate]

/-- The 3-free part of the left affix. -/
def leftCore (j k : ℕ) (l : Bool) : Word := if l then run k 1 ++ run j 0 else run j 0

lemma two_not_mem_leftCore (j k : ℕ) (l : Bool) : (2 : Letter) ∉ leftCore j k l := by
  unfold leftCore; split_ifs <;> simp [run, List.mem_replicate]

/-- The child word of v for affix choices l, r. -/
def child (j k : ℕ) (l r : Bool) (v : Word) : Word :=
  leftAffix j k l ++ sigma j k v ++ rightAffix j k r

lemma child_eq (j k : ℕ) (l r : Bool) (v : Word) :
    child j k l r v = leftCore j k l ++ 2 :: (sigma j k v ++ rightAffix j k r) := by
  cases l <;> simp [child, leftAffix, leftCore, affixC, affixA, List.append_assoc]

/-- Exact extension edges of a child: Proposition 71 of the source, both inclusions. -/
theorem child_edge_iff (L : Word → Prop) (hfac : Factorial L) (hext : LeftExtendable L)
    (j k : ℕ) (l r : Bool) (hl : l = true → 0 < k) (hr : r = true → 0 < j ∨ 0 < k)
    (v : Word) (y z : Letter) :
    extensionEdge (imageLanguage L j k) (child j k l r v) y z ↔
      ∃ c d, extensionEdge L v c d ∧ alphaL (decide (k ≠ 0)) l c = some y ∧
        alphaR (decide (j ≠ 0)) (decide (k ≠ 0)) r d = some z := by
  rw [child_eq, image_edge_iff L hfac hext j k _ _ v (two_not_mem_leftCore j k l)
    (two_not_mem_rightAffix j k r) y z]
  have hL : ∀ c, (y :: (leftCore j k l ++ [2]) <:+ 2 :: block j k c) ↔
      alphaL (decide (k ≠ 0)) l c = some y := by
    intro c
    cases l with
    | false =>
      have := left_A_exact j k c y
      simpa [localLeft, leftAffix, affixA, leftCore] using this
    | true =>
      have hk := hl rfl
      have := left_C_exact j k hk c y
      simpa [localLeft, leftAffix, affixC, affixA, leftCore, show k ≠ 0 by omega,
        List.append_assoc] using this
  have hR : ∀ d, (rightAffix j k r ++ [z] <+: block j k d) ↔
      alphaR (decide (j ≠ 0)) (decide (k ≠ 0)) r d = some z := by
    intro d
    cases r with
    | false => exact right_empty_exact j k d z
    | true => exact right_run_exact j k (hr rfl) d z
  simp only [hL, hR, extensionEdge]
  constructor
  · rintro ⟨c, d, h, h1, h2⟩; exact ⟨c, d, by simpa using h, h1, h2⟩
  · rintro ⟨c, d, h, h1, h2⟩; exact ⟨c, d, by simpa using h, h1, h2⟩

/-- First-3 / last-3 decomposition of any factor of the image containing 3. -/
lemma first_two_split : ∀ (w : Word), (2 : Letter) ∈ w → ∃ x R, w = x ++ 2 :: R ∧ (2 : Letter) ∉ x
  | [], h => by simp at h
  | a :: w, h => by
    by_cases ha : a = 2
    · exact ⟨[], w, by simp [ha], by simp⟩
    · have hw : (2 : Letter) ∈ w := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm ha
        · exact h
      obtain ⟨x, R, rfl, hx⟩ := first_two_split w hw
      exact ⟨a :: x, R, rfl, by simp [hx, Ne.symm ha]⟩

lemma last_two_split : ∀ (R : Word), ∃ M B, R = M ++ B ∧ (2 : Letter) ∉ B ∧
    (M = [] ∨ ∃ M', M = M' ++ [2])
  | [] => ⟨[], [], rfl, by simp, Or.inl rfl⟩
  | a :: R => by
    obtain ⟨M, B, rfl, hB, hM⟩ := last_two_split R
    rcases hM with rfl | ⟨M', rfl⟩
    · by_cases ha : a = 2
      · exact ⟨[2], B, by simp [ha], hB, Or.inr ⟨[], rfl⟩⟩
      · exact ⟨[], a :: B, rfl, by simp [hB, Ne.symm ha], Or.inl rfl⟩
    · exact ⟨a :: M' ++ [2], B, by simp, hB, Or.inr ⟨a :: M', rfl⟩⟩

theorem image_parse (L : Word → Prop) (j k : ℕ) (w : Word) (hw : imageLanguage L j k w)
    (h2 : (2 : Letter) ∈ w) :
    ∃ x v B, (2 : Letter) ∉ x ∧ (2 : Letter) ∉ B ∧ w = x ++ 2 :: (sigma j k v ++ B) := by
  obtain ⟨x, R, rfl, hx⟩ := first_two_split w h2
  obtain ⟨M, B, rfl, hB, hM⟩ := last_two_split R
  obtain ⟨u, -, P, Q, h⟩ := hw
  have h' : sigma j k u = (P ++ x) ++ 2 :: (M ++ (B ++ Q)) := by rw [← h]; simp
  obtain ⟨u₁, u₂, rfl, -, h2⟩ := sigma_split u _ _ h'
  rcases hM with rfl | ⟨M', rfl⟩
  · exact ⟨x, [], B, hx, hB, by simp [sigma]⟩
  · have h2' : sigma j k u₂ = M' ++ 2 :: (B ++ Q) := by rw [h2]; simp
    obtain ⟨v, u₃, rfl, hv, -⟩ := sigma_split u₂ _ _ h2'
    exact ⟨x, v, B, hx, hB, by rw [hv]⟩

/-- Every factor containing 3 with two left extensions and two right extensions
is a child aσ(v)b for valid affix choices. -/
theorem special_parse (L : Word → Prop) (hfac : Factorial L) (hext : LeftExtendable L)
    (j k : ℕ) (w : Word) (h2 : (2 : Letter) ∈ w)
    (hl : ∃ y1 z1 y2 z2, extensionEdge (imageLanguage L j k) w y1 z1 ∧
      extensionEdge (imageLanguage L j k) w y2 z2 ∧ y1 ≠ y2)
    (hr : ∃ y1 z1 y2 z2, extensionEdge (imageLanguage L j k) w y1 z1 ∧
      extensionEdge (imageLanguage L j k) w y2 z2 ∧ z1 ≠ z2) :
    ∃ v l r, (l = true → 0 < k) ∧ (r = true → 0 < j ∨ 0 < k) ∧ w = child j k l r v := by
  obtain ⟨y1, z1, y2, z2, e1, e2, hy⟩ := hl
  have hw : imageLanguage L j k w := image_factorial L j k _ _ e1 ⟨[y1], [z1], by simp⟩
  obtain ⟨x, v, B, hx, hB, rfl⟩ := image_parse L j k w hw h2
  rw [image_edge_iff L hfac hext j k x B v hx hB] at e1 e2
  obtain ⟨c1, -, -, l1, -⟩ := e1
  obtain ⟨c2, -, -, l2, -⟩ := e2
  obtain ⟨y1', z1', y2', z2', f1, f2, hz⟩ := hr
  rw [image_edge_iff L hfac hext j k x B v hx hB] at f1 f2
  obtain ⟨-, d1, -, -, r1⟩ := f1
  obtain ⟨-, d2, -, -, r2⟩ := f2
  have hxl := left_affix_cases l1 l2 hy
  have hBr := right_affix_cases r1 r2 hz
  have hrB : ∃ r : Bool, (r = true → 0 < j ∨ 0 < k) ∧ B = rightAffix j k r := by
    rcases hBr with rfl | rfl
    · exact ⟨false, by simp, rfl⟩
    · rcases Nat.eq_zero_or_pos j with rfl | hj
      · rcases Nat.eq_zero_or_pos k with rfl | hk
        · exact ⟨false, by simp, by simp [rightAffix, run]⟩
        · exact ⟨true, fun _ => Or.inr hk, rfl⟩
      · exact ⟨true, fun _ => Or.inl hj, rfl⟩
  obtain ⟨r, hr, rfl⟩ := hrB
  rcases hxl with rfl | ⟨hk, rfl⟩
  · exact ⟨v, false, r, by simp, hr, by rw [child_eq]; rfl⟩
  · exact ⟨v, true, r, fun _ => hk, hr, by rw [child_eq]; rfl⟩

#print axioms child_edge_iff
#print axioms special_parse
end Trip
```

### `TripTypes.lean`

```lean
import TripLocalMaps
import Mathlib.Data.Fintype.Prod

/-! Finite extension-graph types. A graph is a Boolean relation on the three
letters; the 23 types are 9-bit masks (bit 3a+b is the edge (a,b)). The child
table below is checked by `decide` against the transform built from the exact
local maps alphaL, alphaR of `TripLocalMaps` (proved equal to the word-level
extension maps in `TripAffixes`). -/

namespace Trip

abbrev Gr := Letter → Letter → Bool

def toG (t : ℕ) : Gr := fun a b => t.testBit (3 * a.val + b.val)

def TG (g : Gr) (jp kp l r : Bool) : Gr := fun y z =>
  (List.finRange 3).any fun c => (List.finRange 3).any fun d =>
    g c d && (alphaL kp l c == some y) && (alphaR jp kp r d == some z)

def leftSet (g : Gr) : Finset Letter := Finset.univ.filter fun a => ∃ b, g a b = true
def rightSet (g : Gr) : Finset Letter := Finset.univ.filter fun b => ∃ a, g a b = true
def edgeSet (g : Gr) : Finset (Letter × Letter) := Finset.univ.filter fun p => g p.1 p.2 = true
def bisp (g : Gr) : Bool := decide (2 ≤ (leftSet g).card ∧ 2 ≤ (rightSet g).card)
def multG (g : Gr) : ℤ := ((edgeSet g).card : ℤ) - (leftSet g).card - (rightSet g).card + 1

def enc (g : Gr) : ℕ :=
  ((List.finRange 3).flatMap fun a => (List.finRange 3).map fun b =>
    if g a b then 2 ^ (3 * a.val + b.val) else 0).sum

def childOf (t : ℕ) (jp kp l r : Bool) : Option ℕ :=
  if bisp (TG (toG t) jp kp l r) then some (enc (TG (toG t) jp kp l r)) else none

def states : List ℕ :=
  [11,17,20,25,26,27,52,77,80,100,152,176,200,201,205,208,216,217,221,244,356,416,484]
def harmless : List ℕ := [11,25,26,52,77,152,176,200,201,208,356,416,484]
def pos3 : List ℕ := [27,216,217]
def negs : List ℕ := [17,20,80,100]
def heads : List ℕ := [205,244,221]

def lrChoices : List (Bool × Bool) := [(false,false),(false,true),(true,false),(true,true)]

def computedChildren (t : ℕ) (jp kp : Bool) : List (ℕ × Bool × Bool) :=
  lrChoices.filterMap fun p => (childOf t jp kp p.1 p.2).map fun t' => (t', p.1, p.2)

/-- The explicit child table (type, l, r), generated by script and checked below. -/
def childTab : ℕ → Bool → Bool → List (ℕ × Bool × Bool)
  | 11, false, false => [(11, false, false)]
  | 11, false, true => [(11, false, false)]
  | 11, true, false => [(11, false, false)]
  | 11, true, true => [(11, false, false)]
  | 17, false, false => [(17, false, false)]
  | 17, false, true => [(17, false, false)]
  | 17, true, false => [(17, false, false)]
  | 17, true, true => [(17, false, false)]
  | 20, false, false => [(20, false, false)]
  | 20, false, true => [(20, false, true)]
  | 20, true, false => [(17, false, false)]
  | 20, true, true => [(17, false, true)]
  | 25, false, false => [(25, false, false)]
  | 25, false, true => [(25, false, false)]
  | 25, true, false => [(25, false, false)]
  | 25, true, true => [(25, false, false)]
  | 26, false, false => [(26, false, false)]
  | 26, false, true => [(26, false, false)]
  | 26, true, false => [(26, false, false)]
  | 26, true, true => [(26, false, false)]
  | 27, false, false => [(27, false, false)]
  | 27, false, true => [(27, false, false)]
  | 27, true, false => [(27, false, false)]
  | 27, true, true => [(27, false, false)]
  | 52, false, false => [(52, false, false)]
  | 52, false, true => [(52, false, true)]
  | 52, true, false => [(25, false, false)]
  | 52, true, true => [(25, false, true)]
  | 77, false, false => [(77, false, false)]
  | 77, false, true => [(11, false, false)]
  | 77, true, false => [(77, false, true)]
  | 77, true, true => [(11, false, false)]
  | 80, false, false => [(80, false, false)]
  | 80, false, true => [(80, true, false)]
  | 80, true, false => [(80, false, false)]
  | 80, true, true => [(80, true, false)]
  | 100, false, false => [(100, false, false)]
  | 100, false, true => [(26, false, false), (80, true, false)]
  | 100, true, false => [(100, false, true)]
  | 100, true, true => [(26, false, false), (80, true, false)]
  | 152, false, false => [(152, false, false)]
  | 152, false, true => [(152, true, false)]
  | 152, true, false => [(152, false, false)]
  | 152, true, true => [(152, true, false)]
  | 176, false, false => [(176, false, false)]
  | 176, false, true => [(176, true, true)]
  | 176, true, false => [(152, false, false)]
  | 176, true, true => [(152, true, true)]
  | 200, false, false => [(200, false, false)]
  | 200, false, true => [(200, true, false)]
  | 200, true, false => [(200, false, false)]
  | 200, true, true => [(200, true, false)]
  | 201, false, false => [(201, false, false)]
  | 201, false, true => [(25, false, false), (200, true, false)]
  | 201, true, false => [(201, false, false)]
  | 201, true, true => [(25, false, false), (200, true, false)]
  | 205, false, false => [(205, false, false)]
  | 205, false, true => [(27, false, false), (20, false, true), (200, true, false)]
  | 205, true, false => [(201, false, false), (77, false, true)]
  | 205, true, true => [(27, false, false), (17, false, true), (200, true, false)]
  | 208, false, false => [(208, false, false)]
  | 208, false, true => [(208, true, false)]
  | 208, true, false => [(208, false, false)]
  | 208, true, true => [(208, true, false)]
  | 216, false, false => [(216, false, false)]
  | 216, false, true => [(216, true, false)]
  | 216, true, false => [(216, false, false)]
  | 216, true, true => [(216, true, false)]
  | 217, false, false => [(217, false, false)]
  | 217, false, true => [(25, false, false), (216, true, false)]
  | 217, true, false => [(217, false, false)]
  | 217, true, true => [(25, false, false), (216, true, false)]
  | 221, false, false => [(221, false, false)]
  | 221, false, true => [(27, false, false), (20, false, true), (216, true, false)]
  | 221, true, false => [(217, false, false), (77, false, true)]
  | 221, true, true => [(27, false, false), (17, false, true), (216, true, false)]
  | 244, false, false => [(244, false, false)]
  | 244, false, true => [(26, false, false), (52, false, true), (208, true, false), (176, true, true)]
  | 244, true, false => [(217, false, false), (100, false, true)]
  | 244, true, true => [(26, false, false), (25, false, true), (208, true, false), (152, true, true)]
  | 356, false, false => [(356, false, false)]
  | 356, false, true => [(26, false, false), (208, true, false)]
  | 356, true, false => [(356, false, true)]
  | 356, true, true => [(26, false, false), (208, true, false)]
  | 416, false, false => [(416, false, false)]
  | 416, false, true => [(416, true, true)]
  | 416, true, false => [(200, false, false)]
  | 416, true, true => [(200, true, true)]
  | 484, false, false => [(484, false, false)]
  | 484, false, true => [(26, false, false), (52, false, true), (208, true, false), (416, true, true)]
  | 484, true, false => [(201, false, false), (356, false, true)]
  | 484, true, true => [(26, false, false), (25, false, true), (208, true, false), (200, true, true)]
  | _, _, _ => []

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem childTab_check : (states.all fun t => [false,true].all fun jp => [false,true].all fun kp =>
    childTab t jp kp == computedChildren t jp kp) = true := by decide

def eqG (g h : Gr) : Bool :=
  (List.finRange 3).all fun a => (List.finRange 3).all fun b => g a b == h a b

lemma eqG_spec {g h : Gr} (e : eqG g h = true) : g = h := by
  funext a b
  simp only [eqG, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at e
  exact e a b

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem child_types_check : (states.all fun t => [false,true].all fun jp => [false,true].all fun kp =>
    lrChoices.all fun p => match childOf t jp kp p.1 p.2 with
      | some t' => eqG (TG (toG t) jp kp p.1 p.2) (toG t') && states.contains t'
      | none => true) = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem states_check : (states.all fun t => bisp (toG t) && enc (toG t) == t &&
    (if pos3.contains t || t == 221 then multG (toG t) == 1
     else if negs.contains t then multG (toG t) == -1 else multG (toG t) == 0) &&
    (harmless.contains t || pos3.contains t || negs.contains t || heads.contains t)) = true := by
  decide

#print axioms childTab_check
#print axioms child_types_check
#print axioms states_check
end Trip
```

### `TripWindows.lean`

```lean
import TripAffixes

/-! Windows of the padded blocks 3·2^p·1^q·3 (Lean letters 2, 1, 0), with
symbolic p, q. These give closed forms for the extension pairs of the 3-free
words 1^a, 2^b, 2^b 1^a and the empty word. -/

set_option linter.unusedSimpArgs false

namespace Trip

def pad (p q : ℕ) : Word := 2 :: (run p 1 ++ (run q 0 ++ [2]))

def padF (p q m : ℕ) : Letter := if m = 0 then 2 else if m ≤ p then 1 else if m ≤ p + q then 0 else 2

lemma padF_two {p q m : ℕ} : padF p q m = 2 ↔ (m = 0 ∨ p + q < m) := by
  unfold padF; split_ifs <;> simp <;> omega
lemma padF_one {p q m : ℕ} : padF p q m = 1 ↔ (1 ≤ m ∧ m ≤ p) := by
  unfold padF; split_ifs <;> simp <;> omega
lemma padF_zero {p q m : ℕ} : padF p q m = 0 ↔ (p < m ∧ m ≤ p + q) := by
  unfold padF; split_ifs <;> simp <;> omega

lemma letter_cases (y : Letter) : y = 0 ∨ y = 1 ∨ y = 2 := by fin_cases y <;> simp

lemma padF_cases (p q m : ℕ) : (padF p q m = 2 ∧ (m = 0 ∨ p + q < m)) ∨
    (padF p q m = 1 ∧ 1 ≤ m ∧ m ≤ p) ∨ (padF p q m = 0 ∧ p < m ∧ m ≤ p + q) := by
  unfold padF; split_ifs <;> simp <;> omega

lemma pad_length (p q : ℕ) : (pad p q).length = p + q + 2 := by
  simp [pad, run]; omega

lemma pad_getElem? (p q m : ℕ) :
    (pad p q)[m]? = if m < p + q + 2 then some (padF p q m) else none := by
  unfold pad padF
  cases m with
  | zero => simp
  | succ m =>
    simp only [List.getElem?_cons_succ, List.getElem?_append, List.getElem?_replicate, run,
      List.length_replicate, List.getElem?_singleton]
    split_ifs <;> first | rfl | omega | simp_all

lemma pad_get_lt {p q m : ℕ} (h : m < p + q + 2) : (pad p q)[m]? = some (padF p q m) := by
  simp [pad_getElem?, h]

/-- The window form of infixes of a padded block. -/
lemma window_iff (p q : ℕ) (w : Word) (y z : Letter) :
    ([y] ++ w ++ [z] <:+: pad p q) ↔ ∃ n, n + w.length ≤ p + q ∧ padF p q n = y ∧
      padF p q (n + w.length + 1) = z ∧
      ∀ i (h : i < w.length), padF p q (n + 1 + i) = w[i] := by
  rw [List.infix_iff_getElem?]
  simp only [List.length_append, List.length_singleton, pad_length]
  constructor
  · rintro ⟨n, hn, hall⟩
    refine ⟨n, by omega, ?_, ?_, ?_⟩
    · have := hall 0 (by omega)
      rw [pad_get_lt (by omega)] at this
      simpa using this
    · have := hall (w.length + 1) (by omega)
      rw [pad_get_lt (by omega)] at this
      simp only [Option.some.injEq] at this
      rw [show n + w.length + 1 = w.length + 1 + n by omega, this]
      simp [List.getElem_append_right]
    · intro i hi
      have := hall (i + 1) (by omega)
      rw [pad_get_lt (by omega)] at this
      simp only [Option.some.injEq] at this
      rw [show n + 1 + i = i + 1 + n by omega, this]
      rw [List.getElem_append_left (by simp; omega)]
      simp
  · rintro ⟨n, hn, hy, hz, hall⟩
    refine ⟨n, by omega, ?_⟩
    intro i hi
    rw [pad_get_lt (by omega)]
    congr 1
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simpa using hy
    · rcases lt_or_ge i (w.length + 1) with hi1 | hi1
      · obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
        rw [List.getElem_append_left (by simp; omega)]
        rw [show i.succ + n = n + 1 + i by omega, hall i (by omega)]
        simp
      · have hi2 : i = w.length + 1 := by omega
        subst hi2
        rw [show w.length + 1 + n = n + w.length + 1 by omega, hz]
        simp [List.getElem_append_right]

lemma all_run_zero (p q n a : ℕ) :
    (∀ i (h : i < (run a 0).length), padF p q (n + 1 + i) = (run a 0)[i]) ↔
      (a = 0 ∨ (p ≤ n ∧ n + a ≤ p + q)) := by
  simp only [run, List.length_replicate, List.getElem_replicate, padF_zero]
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · left; rfl
    · right; have h1 := h 0 ha; have h2 := h (a - 1) (by omega); omega
  · rintro (rfl | h) i hi
    · omega
    · omega

lemma all_run_one (p q n b : ℕ) :
    (∀ i (h : i < (run b 1).length), padF p q (n + 1 + i) = (run b 1)[i]) ↔
      (b = 0 ∨ n + b ≤ p) := by
  simp only [run, List.length_replicate, List.getElem_replicate, padF_one]
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · left; rfl
    · right; have h2 := h (b - 1) (by omega); omega
  · rintro (rfl | h) i hi
    · omega
    · omega

lemma all_mixed (p q n a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : ∀ i (h : i < (run b 1 ++ run a 0).length),
      padF p q (n + 1 + i) = (run b 1 ++ run a 0)[i]) :
    n + b = p ∧ n + b + a ≤ p + q := by
  have h1 := h (b - 1) (by simp [run]; omega)
  have h2 := h b (by simp [run]; omega)
  have h3 := h (b + a - 1) (by simp [run]; omega)
  rw [List.getElem_append_left (by simp [run]; omega)] at h1
  rw [List.getElem_append_right (by simp [run])] at h2
  rw [List.getElem_append_right (by simp [run]; omega)] at h3
  simp only [run, List.getElem_replicate, List.length_replicate, padF_one, padF_zero] at h1 h2 h3
  omega

/-! Closed forms of the extension pairs inside one padded block. -/

def cfA (p q a : ℕ) (y z : Letter) : Prop :=
  ((p = 0 ∧ y = 2 ∨ 0 < p ∧ y = 1) ∧ ((z = 0 ∧ a + 1 ≤ q) ∨ (z = 2 ∧ a = q))) ∨
  (y = 0 ∧ ((z = 0 ∧ a + 2 ≤ q) ∨ (z = 2 ∧ a + 1 ≤ q)))

def cfB (p q b : ℕ) (y z : Letter) : Prop :=
  (y = 2 ∧ ((z = 1 ∧ b + 1 ≤ p) ∨ (b = p ∧ (q = 0 ∧ z = 2 ∨ 0 < q ∧ z = 0)))) ∨
  (y = 1 ∧ ((z = 1 ∧ b + 2 ≤ p) ∨ (b + 1 ≤ p ∧ (q = 0 ∧ z = 2 ∨ 0 < q ∧ z = 0))))

def cf0 (p q : ℕ) (y z : Letter) : Prop :=
  (y = 2 ∧ (0 < p ∧ z = 1 ∨ p = 0 ∧ 0 < q ∧ z = 0 ∨ p = 0 ∧ q = 0 ∧ z = 2)) ∨
  (y = 1 ∧ ((z = 1 ∧ 2 ≤ p) ∨ (1 ≤ p ∧ (q = 0 ∧ z = 2 ∨ 0 < q ∧ z = 0)))) ∨
  (y = 0 ∧ ((z = 0 ∧ 2 ≤ q) ∨ (z = 2 ∧ 1 ≤ q)))

lemma cfA_iff (p q a : ℕ) (ha : 1 ≤ a) (y z : Letter) :
    ([y] ++ run a 0 ++ [z] <:+: pad p q) ↔ cfA p q a y z := by
  rw [window_iff]
  simp only [all_run_zero]
  simp only [show (run a 0).length = a by simp [run], show a ≠ 0 by omega, false_or]
  constructor
  · rintro ⟨n, -, hy, hz, h1, h2⟩
    rcases padF_cases p q n with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    rcases padF_cases p q (n + a + 1) with ⟨h5, h6⟩ | ⟨h5, h6⟩ | ⟨h5, h6⟩ <;>
    rw [h3] at hy <;> rw [h5] at hz <;> subst hy hz <;> simp [cfA] <;> omega
  · intro h
    refine ⟨if y = 0 then (if z = 0 then p + 1 else p + q - a) else p, ?_⟩
    rcases letter_cases y with rfl | rfl | rfl <;> rcases letter_cases z with rfl | rfl | rfl <;>
      simp [cfA] at h <;> simp [padF_two, padF_one, padF_zero] <;> omega

lemma cfB_iff (p q b : ℕ) (hb : 1 ≤ b) (y z : Letter) :
    ([y] ++ run b 1 ++ [z] <:+: pad p q) ↔ cfB p q b y z := by
  rw [window_iff]
  simp only [all_run_one]
  simp only [show (run b 1).length = b by simp [run], show b ≠ 0 by omega, false_or]
  constructor
  · rintro ⟨n, -, hy, hz, h1⟩
    rcases padF_cases p q n with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    rcases padF_cases p q (n + b + 1) with ⟨h5, h6⟩ | ⟨h5, h6⟩ | ⟨h5, h6⟩ <;>
    rw [h3] at hy <;> rw [h5] at hz <;> subst hy hz <;> simp [cfB] <;> omega
  · intro h
    refine ⟨if y = 2 then 0 else if z = 1 then 1 else p - b, ?_⟩
    rcases letter_cases y with rfl | rfl | rfl <;> rcases letter_cases z with rfl | rfl | rfl <;>
      simp [cfB] at h <;> simp [padF_two, padF_one, padF_zero] <;> omega

lemma cf0_iff (p q : ℕ) (y z : Letter) :
    ([y] ++ [] ++ [z] <:+: pad p q) ↔ cf0 p q y z := by
  rw [window_iff]
  simp only [List.length_nil, add_zero]
  constructor
  · rintro ⟨n, hn, hy, hz, -⟩
    rcases padF_cases p q n with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    rcases padF_cases p q (n + 1) with ⟨h5, h6⟩ | ⟨h5, h6⟩ | ⟨h5, h6⟩ <;>
    rw [h3] at hy <;> rw [h5] at hz <;> subst hy hz <;> simp [cf0] <;> omega
  · intro h
    refine ⟨if y = 2 then 0 else if y = 1 then (if z = 1 then 1 else p) else (if z = 0 then p + 1 else p + q), ?_⟩
    rcases letter_cases y with rfl | rfl | rfl <;> rcases letter_cases z with rfl | rfl | rfl <;>
      simp [cf0] at h <;> simp [padF_two, padF_one, padF_zero] <;> omega

lemma mixed_right (p q a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (y z : Letter)
    (h : [y] ++ (run b 1 ++ run a 0) ++ [z] <:+: pad p q) :
    b ≤ p ∧ a ≤ q ∧ (a < q ∧ z = 0 ∨ a = q ∧ z = 2) := by
  rw [window_iff] at h
  obtain ⟨n, hn, -, hz, hall⟩ := h
  have := all_mixed p q n a b ha hb hall
  simp only [List.length_append, run, List.length_replicate] at hz hn
  rcases padF_cases p q (n + (b + a) + 1) with ⟨h5, h6⟩ | ⟨h5, h6⟩ | ⟨h5, h6⟩ <;>
    rw [h5] at hz <;> subst hz <;> simp <;> omega

/-- The padded blocks. -/
def bp (k : ℕ) (c : Letter) : ℕ := if c = 0 then 0 else if c = 1 then k + 1 else k
def bq (j : ℕ) (c : Letter) : ℕ := if c = 0 then j + 1 else j

lemma pad_block (j k : ℕ) (c : Letter) : 2 :: block j k c = pad (bp k c) (bq j c) := by
  fin_cases c <;> simp [block, pad, bp, bq, run, List.append_assoc]

#print axioms cfA_iff
#print axioms cfB_iff
#print axioms cf0_iff
#print axioms mixed_right
end Trip
```

### `TripSeeds.lean`

```lean
import TripWindows
import TripTypes

/-! The bispecial factors without 3 ("seeds") of an image language, with
their exact extension graphs, for symbolic j, k. -/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

namespace Trip

open Classical in
/-- The extension graph of a word in a language. -/
noncomputable def edges (L : Word → Prop) (w : Word) : Gr := fun a b => decide (extensionEdge L w a b)

lemma edges_apply (L : Word → Prop) (w : Word) (a b : Letter) :
    edges L w a b = true ↔ extensionEdge L w a b := by simp [edges]

lemma exists_letter (P : Letter → Prop) : (∃ c, P c) ↔ P 0 ∨ P 1 ∨ P 2 := by
  constructor
  · rintro ⟨c, hc⟩; fin_cases c <;> simp_all
  · rintro (h | h | h) <;> exact ⟨_, h⟩

lemma free_edge (L : Word → Prop) (hext : LeftExtendable L) (hall : ∀ c : Letter, L [c])
    (j k : ℕ) (w : Word) (hw : (2 : Letter) ∉ w) (y z : Letter) :
    extensionEdge (imageLanguage L j k) w y z ↔
      [y] ++ w ++ [z] <:+: pad 0 (j + 1) ∨ [y] ++ w ++ [z] <:+: pad (k + 1) j ∨
      [y] ++ w ++ [z] <:+: pad k j := by
  rw [image_edge_free_iff L hext hall j k w hw y z, exists_letter]
  simp only [pad_block, bp, bq]
  simp

def emptyType (j k : ℕ) : ℕ :=
  if j = 0 then (if k = 0 then 484 else 244) else (if k = 0 then 205 else 221)

def oneRuns (j k : ℕ) : List (Word × ℕ) :=
  (if j = 0 then [] else [(run j 0, if k = 0 then 356 else 100)]) ++
    (List.range (j - 1)).map fun a => (run (a + 1) 0, 77)

def twoRuns (j k : ℕ) : List (Word × ℕ) :=
  (if k = 0 then [] else [(run k 1, if j = 0 then 416 else 200)]) ++
    (List.range (k - 1)).map fun b => (run (b + 1) 1, if j = 0 then 176 else 152)

/-- All seeds: the empty word and the runs, with their types. -/
def seedList (j k : ℕ) : List (Word × ℕ) := ([], emptyType j k) :: (oneRuns j k ++ twoRuns j k)

section
variable (L : Word → Prop) (hext : LeftExtendable L) (hall : ∀ c : Letter, L [c]) (j k : ℕ)
include hext hall

lemma seed_empty : edges (imageLanguage L j k) [] = toG (emptyType j k) := by
  funext y z
  apply Bool.eq_iff_iff.mpr
  rw [edges_apply, free_edge L hext hall j k [] (by simp)]
  simp only [cf0_iff]
  unfold emptyType
  cases j <;> cases k <;>
    rcases letter_cases y with rfl | rfl | rfl <;> rcases letter_cases z with rfl | rfl | rfl <;>
    simp +decide [cf0, toG]

lemma seed_oneRun (a : ℕ) (ha : 1 ≤ a) (haj : a ≤ j) :
    edges (imageLanguage L j k) (run a 0) =
      toG (if a < j then 77 else if k = 0 then 356 else 100) := by
  funext y z
  apply Bool.eq_iff_iff.mpr
  rw [edges_apply, free_edge L hext hall j k _ (by simp [run, List.mem_replicate])]
  simp only [cfA_iff _ _ _ ha]
  rcases lt_or_eq_of_le haj with haj | rfl
  · simp only [haj, ↓reduceIte]
    rcases letter_cases y with rfl | rfl | rfl <;> rcases letter_cases z with rfl | rfl | rfl <;>
      simp +decide [cfA, toG] <;> omega
  · cases k <;>
    rcases letter_cases y with rfl | rfl | rfl <;> rcases letter_cases z with rfl | rfl | rfl <;>
      simp +decide [cfA, toG] <;> omega

lemma seed_twoRun (b : ℕ) (hb : 1 ≤ b) (hbk : b ≤ k) :
    edges (imageLanguage L j k) (run b 1) =
      toG (if b < k then (if j = 0 then 176 else 152) else (if j = 0 then 416 else 200)) := by
  funext y z
  apply Bool.eq_iff_iff.mpr
  rw [edges_apply, free_edge L hext hall j k _ (by simp [run, List.mem_replicate])]
  simp only [cfB_iff _ _ _ hb]
  rcases lt_or_eq_of_le hbk with hbk | rfl
  · simp only [hbk, ↓reduceIte]
    cases j <;>
    rcases letter_cases y with rfl | rfl | rfl <;> rcases letter_cases z with rfl | rfl | rfl <;>
      simp +decide [cfB, toG] <;> omega
  · cases j <;>
    rcases letter_cases y with rfl | rfl | rfl <;> rcases letter_cases z with rfl | rfl | rfl <;>
      simp +decide [cfB, toG] <;> omega

theorem seeds_sound : ∀ p ∈ seedList j k, edges (imageLanguage L j k) p.1 = toG p.2 := by
  intro p hp
  simp only [seedList, oneRuns, twoRuns, List.mem_cons, List.mem_append, List.mem_map,
    List.mem_range] at hp
  rcases hp with rfl | (h | ⟨a, ha, rfl⟩) | (h | ⟨b, hb, rfl⟩)
  · exact seed_empty L hext hall j k
  · by_cases hj : j = 0
    · simp [hj] at h
    · simp only [hj, ↓reduceIte, List.mem_singleton] at h; subst h
      have := seed_oneRun L hext hall j k j (by omega) le_rfl
      simpa using this
  · have := seed_oneRun L hext hall j k (a + 1) (by omega) (by omega)
    simpa [show a + 1 < j by omega] using this
  · by_cases hk : k = 0
    · simp [hk] at h
    · simp only [hk, ↓reduceIte, List.mem_singleton] at h; subst h
      have := seed_twoRun L hext hall j k k (by omega) le_rfl
      simpa using this
  · have := seed_twoRun L hext hall j k (b + 1) (by omega) (by omega)
    simpa [show b + 1 < k by omega] using this

end

/-! Completeness: every 3-free bispecial factor is a seed. -/

lemma card_le_one_of_fst {g : Gr} (y0 : Letter) (h : ∀ y z, g y z = true → y = y0) :
    (leftSet g).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [leftSet, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  obtain ⟨z, hz⟩ := ha; obtain ⟨z', hz'⟩ := hb
  rw [h _ _ hz, h _ _ hz']

lemma card_le_one_of_snd {g : Gr} (z0 : Letter) (h : ∀ y z, g y z = true → z = z0) :
    (rightSet g).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [rightSet, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  obtain ⟨z, hz⟩ := ha; obtain ⟨z', hz'⟩ := hb
  rw [h _ _ hz, h _ _ hz']

lemma bisp_false_of_fst {g : Gr} (y0 : Letter) (h : ∀ y z, g y z = true → y = y0) :
    bisp g = false := by
  have := card_le_one_of_fst y0 h
  simp only [bisp, decide_eq_false_iff_not, not_and, not_le]
  omega

lemma bisp_false_of_snd {g : Gr} (z0 : Letter) (h : ∀ y z, g y z = true → z = z0) :
    bisp g = false := by
  have := card_le_one_of_snd z0 h
  simp only [bisp, decide_eq_false_iff_not, not_and, not_le]
  intro; omega

lemma exists_edge_of_bisp {g : Gr} (h : bisp g = true) : ∃ y z, g y z = true := by
  simp only [bisp, decide_eq_true_eq] at h
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < (leftSet g).card)
  simp only [leftSet, Finset.mem_filter, Finset.mem_univ, true_and] at ha
  obtain ⟨b, hb⟩ := ha
  exact ⟨a, b, hb⟩

lemma window_shape {p q n : ℕ} {w : Word} (hn : n + w.length ≤ p + q)
    (h : ∀ i (h : i < w.length), padF p q (n + 1 + i) = w[i]) :
    ∃ a b, w = run b 1 ++ run a 0 := by
  refine ⟨w.length - min w.length (p - n), min w.length (p - n), ?_⟩
  apply List.ext_getElem (by simp [run])
  intro i h1 h2
  rw [← h i h1]
  by_cases hi : i < min w.length (p - n)
  · rw [List.getElem_append_left (by simp [run]; omega)]
    simp only [run, List.getElem_replicate]
    rw [padF_one]; omega
  · rw [List.getElem_append_right (by simp [run]; omega)]
    simp only [run, List.getElem_replicate]
    rw [padF_zero]; omega

theorem seeds_complete (L : Word → Prop) (hext : LeftExtendable L) (hall : ∀ c : Letter, L [c])
    (j k : ℕ) (w : Word) (hw : (2 : Letter) ∉ w) (hb : bisp (edges (imageLanguage L j k) w) = true) :
    ∃ t, (w, t) ∈ seedList j k := by
  have hfe := free_edge L hext hall j k w hw
  -- the shape of w
  obtain ⟨y0, z0, e0⟩ := exists_edge_of_bisp hb
  rw [edges_apply, hfe] at e0
  have hshape : ∃ a b, w = run b 1 ++ run a 0 := by
    rcases e0 with e | e | e <;> rw [window_iff] at e <;> obtain ⟨n, hn, -, -, hall'⟩ := e <;>
      exact window_shape hn hall'
  obtain ⟨a, b, rfl⟩ := hshape
  rcases Nat.eq_zero_or_pos b with rfl | hb1
  · rcases Nat.eq_zero_or_pos a with rfl | ha1
    · exact ⟨_, List.mem_cons_self⟩
    · -- w = 1^a
      simp only [run, List.replicate_zero, List.nil_append] at hb ⊢
      by_cases haj : a ≤ j
      · rcases lt_or_eq_of_le haj with haj | rfl
        · refine ⟨77, List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _ ?_))⟩
          simp only [List.mem_map, List.mem_range]
          exact ⟨a - 1, by omega, by simp [run, show a - 1 + 1 = a by omega]⟩
        · refine ⟨if k = 0 then 356 else 100,
            List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ ?_))⟩
          simp [show a ≠ 0 by omega, run]
      · exfalso
        have : bisp (edges (imageLanguage L j k) (List.replicate a 0)) = false := by
          apply bisp_false_of_fst 2
          intro y z e
          rw [edges_apply, free_edge L hext hall j k _ (by simp [List.mem_replicate])] at e
          simp only [show List.replicate a (0 : Letter) = run a 0 from rfl, cfA_iff _ _ _ ha1,
            cfA] at e
          rcases letter_cases y with rfl | rfl | rfl <;> rcases letter_cases z with rfl | rfl | rfl <;>
            simp at e ⊢ <;> omega
        rw [this] at hb; exact Bool.false_ne_true hb
  · rcases Nat.eq_zero_or_pos a with rfl | ha1
    · -- w = 2^b
      simp only [run, List.replicate_zero, List.append_nil] at hb ⊢
      by_cases hbk : b ≤ k
      · rcases lt_or_eq_of_le hbk with hbk | rfl
        · refine ⟨if j = 0 then 176 else 152,
            List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_append_right _ ?_))⟩
          simp only [List.mem_map, List.mem_range]
          exact ⟨b - 1, by omega, by simp [run, show b - 1 + 1 = b by omega]⟩
        · refine ⟨if j = 0 then 416 else 200,
            List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_append_left _ ?_))⟩
          simp [show b ≠ 0 by omega, run]
      · exfalso
        have : bisp (edges (imageLanguage L j k) (List.replicate b 1)) = false := by
          apply bisp_false_of_fst 2
          intro y z e
          rw [edges_apply, free_edge L hext hall j k _ (by simp [List.mem_replicate])] at e
          simp only [show List.replicate b (1 : Letter) = run b 1 from rfl, cfB_iff _ _ _ hb1,
            cfB] at e
          rcases letter_cases y with rfl | rfl | rfl <;> rcases letter_cases z with rfl | rfl | rfl <;>
            simp at e ⊢ <;> omega
        rw [this] at hb; exact Bool.false_ne_true hb
    · -- mixed words are not right special
      exfalso
      have : bisp (edges (imageLanguage L j k) (run b 1 ++ run a 0)) = false := by
        apply bisp_false_of_snd (if a < j then 0 else 2)
        intro y z e
        rw [edges_apply, free_edge L hext hall j k _ (by simp [run, List.mem_replicate])] at e
        rcases e with e | e | e <;>
          obtain ⟨h1, h2, ⟨h3, rfl⟩ | ⟨h3, rfl⟩⟩ := mixed_right _ _ a b ha1 hb1 y z e <;>
          split_ifs <;> first | rfl | omega
      rw [this] at hb; exact Bool.false_ne_true hb

#print axioms seeds_sound
#print axioms seeds_complete
end Trip
```

### `TripMatch.lean`

```lean
import TripSeeds
import PairCones
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-! The abstract production forest (types and Parikh vectors) and the
matching invariant of the written proof, section 3. -/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

namespace Trip
open TripPairCones

abbrev Node := ℕ × Vec

def νw (w : Word) : Vec := ((w.count 0 : ℤ), (w.count 1 : ℤ), (w.count 2 : ℤ))

/-- Parikh vector of leftAffix l plus rightAffix r. -/
def off (j k : ℕ) (l r : Bool) : Vec :=
  ((j : ℤ) + (if r = true ∧ k = 0 then (j : ℤ) else 0),
   (if l = true then (k : ℤ) else 0) + (if r = true ∧ k ≠ 0 then (k : ℤ) else 0), 1)

def childN (j k : ℕ) (x : Node) : List Node :=
  (childTab x.1 (decide (j ≠ 0)) (decide (k ≠ 0))).map fun e =>
    (e.1, M (j : ℤ) (k : ℤ) x.2 + off j k e.2.1 e.2.2)

def seedN (j k : ℕ) : List Node := (seedList j k).map fun p => (p.2, νw p.1)

/-- Abstract forest at level i, depth D. -/
def forestN (g : ℕ → ℕ × ℕ) : ℕ → ℕ → List Node
  | i, 0 => seedN (g i).1 (g i).2
  | i, D + 1 => seedN (g i).1 (g i).2 ++ (forestN g (i + 1) D).flatMap (childN (g i).1 (g i).2)

/-- The unique non-harmless child of a negative or paired positive type. -/
def mainTab : ℕ → Bool → Bool → ℕ × Bool × Bool
  | 17, false, false => (17, false, false)
  | 17, false, true => (17, false, false)
  | 17, true, false => (17, false, false)
  | 17, true, true => (17, false, false)
  | 20, false, false => (20, false, false)
  | 20, false, true => (20, false, true)
  | 20, true, false => (17, false, false)
  | 20, true, true => (17, false, true)
  | 80, false, false => (80, false, false)
  | 80, false, true => (80, true, false)
  | 80, true, false => (80, false, false)
  | 80, true, true => (80, true, false)
  | 100, false, false => (100, false, false)
  | 100, false, true => (80, true, false)
  | 100, true, false => (100, false, true)
  | 100, true, true => (80, true, false)
  | 27, false, false => (27, false, false)
  | 27, false, true => (27, false, false)
  | 27, true, false => (27, false, false)
  | 27, true, true => (27, false, false)
  | 216, false, false => (216, false, false)
  | 216, false, true => (216, true, false)
  | 216, true, false => (216, false, false)
  | 216, true, true => (216, true, false)
  | 217, false, false => (217, false, false)
  | 217, false, true => (216, true, false)
  | 217, true, false => (217, false, false)
  | 217, true, true => (216, true, false)
  | _, _, _ => (0, false, false)

set_option maxRecDepth 100000 in
theorem inert_tab : ((harmless ++ negs).all fun t => [false, true].all fun jp =>
    [false, true].all fun kp => (childTab t jp kp).all fun e =>
      harmless.contains e.1 || negs.contains e.1) = true := by decide

set_option maxRecDepth 100000 in
theorem main_tab : ((negs ++ pos3).all fun t => [false, true].all fun jp =>
    [false, true].all fun kp =>
      (((childTab t jp kp).filter fun e => !harmless.contains e.1) == [mainTab t jp kp]) &&
      (negs.contains (mainTab t jp kp).1 == negs.contains t) &&
      (pos3.contains (mainTab t jp kp).1 == pos3.contains t)) = true := by decide

lemma bool_mem (b : Bool) : b ∈ [false, true] := by cases b <;> simp

def Inert (x : Node) : Prop := x.1 ∈ harmless ∨ x.1 ∈ negs

lemma inert_children {t : ℕ} (ht : t ∈ harmless ∨ t ∈ negs) (jp kp : Bool) :
    ∀ e ∈ childTab t jp kp, e.1 ∈ harmless ∨ e.1 ∈ negs := by
  have h := List.all_eq_true.mp inert_tab t (by simp only [List.mem_append]; exact ht)
  have h := List.all_eq_true.mp h jp (bool_mem jp)
  have h := List.all_eq_true.mp h kp (bool_mem kp)
  intro e he
  have := List.all_eq_true.mp h e he
  simpa [List.elem_iff] using this

lemma main_children {t : ℕ} (ht : t ∈ negs ∨ t ∈ pos3) (jp kp : Bool) :
    ((childTab t jp kp).filter fun e => !harmless.contains e.1) = [mainTab t jp kp] ∧
    ((mainTab t jp kp).1 ∈ negs ↔ t ∈ negs) ∧ ((mainTab t jp kp).1 ∈ pos3 ↔ t ∈ pos3) := by
  have h := List.all_eq_true.mp main_tab t (by simp only [List.mem_append]; exact ht)
  have h := List.all_eq_true.mp h jp (bool_mem jp)
  have h := List.all_eq_true.mp h kp (bool_mem kp)
  simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, ?_, ?_⟩
  · rw [← List.contains_iff_mem, ← List.contains_iff_mem, h2]
  · rw [← List.contains_iff_mem, ← List.contains_iff_mem, h3]

lemma inert_childN {j k : ℕ} {x : Node} (hx : Inert x) : ∀ y ∈ childN j k x, Inert y := by
  intro y hy
  simp only [childN, List.mem_map] at hy
  obtain ⟨e, he, rfl⟩ := hy
  exact inert_children hx _ _ e he

def mainNode (j k : ℕ) (x : Node) : Node :=
  ((mainTab x.1 (decide (j ≠ 0)) (decide (k ≠ 0))).1,
    M (j : ℤ) (k : ℤ) x.2 + off j k (mainTab x.1 (decide (j ≠ 0)) (decide (k ≠ 0))).2.1
      (mainTab x.1 (decide (j ≠ 0)) (decide (k ≠ 0))).2.2)

lemma childN_main {j k : ℕ} {x : Node} (hx : x.1 ∈ negs ∨ x.1 ∈ pos3) :
    ∃ H : Multiset Node, (childN j k x : Multiset Node) = mainNode j k x ::ₘ H ∧
      ∀ y ∈ H, y.1 ∈ harmless := by
  obtain ⟨h1, -, -⟩ := main_children hx (decide (j ≠ 0)) (decide (k ≠ 0))
  set l := childTab x.1 (decide (j ≠ 0)) (decide (k ≠ 0)) with hl
  have hp := List.filter_append_perm (fun e : ℕ × Bool × Bool => harmless.contains e.1) l
  have hneg : (l.filter fun e => !harmless.contains e.1) = [mainTab x.1 (decide (j ≠ 0)) (decide (k ≠ 0))] := h1
  rw [hneg] at hp
  let f : ℕ × Bool × Bool → Node := fun e => (e.1, M (j : ℤ) (k : ℤ) x.2 + off j k e.2.1 e.2.2)
  refine ⟨((l.filter fun e => harmless.contains e.1).map f : List Node), ?_, ?_⟩
  · have hp' := (hp.map f).symm
    have : childN j k x = l.map f := rfl
    rw [this, Multiset.coe_eq_coe.mpr hp']
    simp only [List.map_append, List.map_cons, List.map_nil, ← Multiset.coe_add]
    rw [add_comm]; rfl
  · intro y hy
    simp only [Multiset.mem_coe, List.mem_map, List.mem_filter] at hy
    obtain ⟨e, ⟨-, he⟩, rfl⟩ := hy
    simpa [List.elem_iff] using he

/-! Admissible pairs. -/

def coneType (nt pt : ℕ) : Prop := nt = 100 ∨ (pt = 27 ∧ (nt = 80 ∨ nt = 20))

def adm (nt pt : ℕ) (δ : Vec) : Prop := TripPairCones.Nonneg δ ∧ (coneType nt pt → Cone δ)

def PairOK (x : Node × Node) : Prop :=
  x.1.1 ∈ negs ∧ x.2.1 ∈ pos3 ∧ adm x.1.1 x.2.1 (x.2.2 - x.1.2)

lemma M_sub (j k : ℤ) (a b : Vec) : M j k (a - b) = M j k a - M j k b := by
  ext <;> simp [M] <;> ring

lemma M_add (j k : ℤ) (a b : Vec) : M j k (a + b) = M j k a + M j k b := by
  ext <;> simp [M] <;> ring

lemma M_nonneg (j k : ℕ) {v : Vec} (hv : TripPairCones.Nonneg v) :
    0 ≤ (M (j : ℤ) k v).1 ∧ 0 ≤ (M (j : ℤ) k v).2.1 ∧ 0 ≤ (M (j : ℤ) k v).2.2 :=
  nonneg_map j k (by positivity) (by positivity) v hv

lemma M_cone (j k : ℕ) {v : Vec} (hv : Cone v) :
    (j : ℤ) ≤ (M (j : ℤ) k v).1 ∧ (k : ℤ) ≤ (M (j : ℤ) k v).2.1 ∧ 1 ≤ (M (j : ℤ) k v).2.2 := by
  obtain ⟨h1, h2, h3⟩ := hv
  simp only [M]
  have hj : (0 : ℤ) ≤ j := by positivity
  have hk : (0 : ℤ) ≤ k := by positivity
  refine ⟨?_, ?_, by omega⟩
  · nlinarith [mul_nonneg hj h1, mul_nonneg hj h2, mul_nonneg hj (show (0 : ℤ) ≤ v.2.2 - 1 by omega)]
  · nlinarith [mul_nonneg hk h2, mul_nonneg hk (show (0 : ℤ) ≤ v.2.2 - 1 by omega)]

lemma neg_mem {t : ℕ} (h : t ∈ negs) : t = 17 ∨ t = 20 ∨ t = 80 ∨ t = 100 := by
  simpa [negs] using h
lemma pos3_mem {t : ℕ} (h : t ∈ pos3) : t = 27 ∨ t = 216 ∨ t = 217 := by
  simpa [pos3] using h

/-- Pair propagation: every admissible pair has an admissible pair of main children. -/
theorem adm_step (j k : ℕ) {tn tp : ℕ} (htn : tn ∈ negs) (htp : tp ∈ pos3) {δ : Vec}
    (h : adm tn tp δ) :
    adm (mainTab tn (decide (j ≠ 0)) (decide (k ≠ 0))).1
      (mainTab tp (decide (j ≠ 0)) (decide (k ≠ 0))).1
      (M (j : ℤ) k δ + (off j k (mainTab tp (decide (j ≠ 0)) (decide (k ≠ 0))).2.1
          (mainTab tp (decide (j ≠ 0)) (decide (k ≠ 0))).2.2 -
        off j k (mainTab tn (decide (j ≠ 0)) (decide (k ≠ 0))).2.1
          (mainTab tn (decide (j ≠ 0)) (decide (k ≠ 0))).2.2)) := by
  obtain ⟨hN, hC⟩ := h
  have b0 := M_nonneg j k hN
  have b1 : coneType tn tp → (j : ℤ) ≤ (M (j : ℤ) k δ).1 ∧ (k : ℤ) ≤ (M (j : ℤ) k δ).2.1 ∧
      1 ≤ (M (j : ℤ) k δ).2.2 := fun hc => M_cone j k (hC hc)
  generalize M (j : ℤ) k δ = X at b0 b1 ⊢
  obtain ⟨X1, X2, X3⟩ := X
  rcases neg_mem htn with rfl | rfl | rfl | rfl <;> rcases pos3_mem htp with rfl | rfl | rfl <;>
    cases j <;> cases k <;>
    simp [mainTab, off, adm, coneType, TripPairCones.Nonneg, Cone] at b0 b1 ⊢ <;> omega

theorem pair_step (j k : ℕ) (x : Node × Node) (hx : PairOK x) :
    ∃ (x' : Node × Node) (H : Multiset Node),
      (childN j k x.1 : Multiset Node) + childN j k x.2 = x'.1 ::ₘ x'.2 ::ₘ H ∧ PairOK x' ∧
      ∀ y ∈ H, Inert y := by
  obtain ⟨hn, hp, hadm⟩ := hx
  obtain ⟨Hn, eHn, hHn⟩ := childN_main (j := j) (k := k) (x := x.1) (Or.inl hn)
  obtain ⟨Hp, eHp, hHp⟩ := childN_main (j := j) (k := k) (x := x.2) (Or.inr hp)
  refine ⟨(mainNode j k x.1, mainNode j k x.2), Hn + Hp, ?_, ?_, ?_⟩
  · rw [eHn, eHp]; simp only [Multiset.cons_add, Multiset.add_cons]
    exact Multiset.cons_swap _ _ _
  · refine ⟨(main_children (Or.inl hn) _ _).2.1.mpr hn, (main_children (Or.inr hp) _ _).2.2.mpr hp, ?_⟩
    have := adm_step j k hn hp hadm
    have e : (mainNode j k x.2).2 - (mainNode j k x.1).2 =
        M (j : ℤ) k (x.2.2 - x.1.2) +
          (off j k (mainTab x.2.1 (decide (j ≠ 0)) (decide (k ≠ 0))).2.1
              (mainTab x.2.1 (decide (j ≠ 0)) (decide (k ≠ 0))).2.2 -
            off j k (mainTab x.1.1 (decide (j ≠ 0)) (decide (k ≠ 0))).2.1
              (mainTab x.1.1 (decide (j ≠ 0)) (decide (k ≠ 0))).2.2) := by
      simp only [mainNode, M_sub]; abel
    show adm _ _ ((mainNode j k x.2).2 - (mainNode j k x.1).2)
    rw [e]; exact this
  · intro y hy
    rcases Multiset.mem_add.mp hy with hy | hy
    · exact Or.inl (hHn y hy)
    · exact Or.inl (hHp y hy)

/-! Weights and the bound. -/

def lenV (v : Vec) : ℤ := v.1 + v.2.1 + v.2.2
def mval (t : ℕ) : ℤ := if t ∈ pos3 ∨ t = 221 then 1 else if t ∈ negs then -1 else 0
def wt (n : ℤ) (x : Node) : ℤ := if lenV x.2 < n then mval x.1 else 0

lemma mval_harmless {t : ℕ} (h : t ∈ harmless) : mval t = 0 := by
  simp only [harmless, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [mval, pos3, negs]

lemma mval_neg {t : ℕ} (h : t ∈ negs) : mval t = -1 := by
  rcases neg_mem h with rfl | rfl | rfl | rfl <;> simp [mval, pos3, negs]

/-- The matching invariant. -/
def MInv (F : Multiset Node) : Prop :=
  ∃ (P : Multiset (Node × Node)) (h f : Option Node) (R : Multiset Node),
    F = P.map Prod.fst + P.map Prod.snd + (h.toList : Multiset Node) +
      (f.toList : Multiset Node) + R ∧
    (∀ x ∈ P, PairOK x) ∧ (∀ x ∈ R, Inert x) ∧
    (∀ x ∈ h, x.1 ∈ heads ∧ TripPairCones.Nonneg x.2) ∧ (∀ x ∈ f, x.1 ∈ pos3 ∧ TripPairCones.Nonneg x.2) ∧
    (h = none → f = none) ∧ (∀ x ∈ h, x.1 = 221 → f = none) ∧
    (∀ x ∈ h, ∀ y ∈ f, Cone (y.2 - x.2))

lemma sum_nonpos_of {s : Multiset Node} (g : Node → ℤ) (h : ∀ x ∈ s, g x ≤ 0) :
    (s.map g).sum ≤ 0 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    have := h a (Multiset.mem_cons_self a s)
    have := ih (fun x hx => h x (Multiset.mem_cons_of_mem hx))
    omega

lemma sum_pairs_nonpos {P : Multiset (Node × Node)} (g : Node × Node → ℤ)
    (h : ∀ x ∈ P, g x ≤ 0) : (P.map g).sum ≤ 0 := by
  induction P using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    have := h a (Multiset.mem_cons_self a s)
    have := ih (fun x hx => h x (Multiset.mem_cons_of_mem hx))
    omega

theorem minv_bound {F : Multiset Node} (hF : MInv F) (n : ℤ) : (F.map (wt n)).sum ≤ 1 := by
  obtain ⟨P, h, f, R, rfl, hP, hR, hh, hf, hhf, h221, -⟩ := hF
  simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_map]
  have e1 : (P.map (wt n ∘ Prod.fst)).sum + (P.map (wt n ∘ Prod.snd)).sum =
      (P.map fun x => wt n x.1 + wt n x.2).sum := by
    rw [← Multiset.sum_map_add]; rfl
  have hpair : (P.map fun x => wt n x.1 + wt n x.2).sum ≤ 0 := by
    apply sum_pairs_nonpos
    intro x hx
    obtain ⟨hn, hp, hN, -⟩ := hP x hx
    obtain ⟨d1, d2, d3⟩ := hN
    have hn' : mval x.1.1 = -1 := by
      rcases neg_mem hn with h | h | h | h <;> simp [mval, h, pos3, negs]
    have hp' : mval x.2.1 = 1 := by simp [mval, hp]
    simp only [wt, lenV, hn', hp']
    simp only [Prod.fst_sub, Prod.snd_sub] at d1 d2 d3
    split_ifs <;> omega
  have hrest : (R.map (wt n)).sum ≤ 0 := by
    apply sum_nonpos_of
    intro x hx
    have : mval x.1 ≤ 0 := by
      rcases hR x hx with h1 | h1
      · rw [mval_harmless h1]
      · rw [mval_neg h1]; omega
    simp only [wt]; split_ifs <;> omega
  have hwt : ∀ x : Node, wt n x ≤ max (mval x.1) 0 := by
    intro x; simp only [wt]; split_ifs <;> omega
  cases h with
  | none =>
    have := hhf rfl; subst this
    simp only [Option.toList_none, Multiset.coe_nil, Multiset.map_zero, Multiset.sum_zero]
    rw [show ∀ a b : ℤ, a + b + 0 + 0 + (R.map (wt n)).sum = a + b + (R.map (wt n)).sum
      from fun a b => by ring] at *
    simp only [Function.comp_def] at e1 ⊢
    omega
  | some x =>
    obtain ⟨hx1, -⟩ := hh x rfl
    have hx2 := hwt x
    simp only [Function.comp_def] at e1 ⊢
    cases f with
    | none =>
      have : mval x.1 ≤ 1 := by
        simp only [heads, List.mem_cons, List.not_mem_nil, or_false] at hx1
        rcases hx1 with h1 | h1 | h1 <;> simp [mval, h1, pos3, negs]
      simp only [Option.toList_some, Option.toList_none, Multiset.coe_singleton,
        Multiset.coe_nil, Multiset.map_singleton, Multiset.sum_singleton, Multiset.map_zero,
        Multiset.sum_zero]
      omega
    | some y =>
      obtain ⟨hy1, -⟩ := hf y rfl
      have hy2 := hwt y
      have hx3 : mval x.1 = 0 := by
        simp only [heads, List.mem_cons, List.not_mem_nil, or_false] at hx1
        rcases hx1 with h1 | h1 | h1
        · simp [mval, h1, pos3, negs]
        · simp [mval, h1, pos3, negs]
        · exact absurd (h221 x rfl h1) (by simp)
      have hy3 : mval y.1 = 1 := by simp [mval, hy1]
      simp only [Option.toList_some, Multiset.coe_singleton, Multiset.map_singleton,
        Multiset.sum_singleton]
      rw [hx3] at hx2; rw [hy3] at hy2
      omega

#print axioms minv_bound
end Trip
```

### `TripMatchStep.lean`

```lean
import TripMatch

/-! The head/free exchanges (written proof §3b) and preservation of the
matching invariant along the abstract production forest. -/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

namespace Trip
open TripPairCones

lemma νw_nil : νw [] = 0 := rfl

lemma νw_run0 (n : ℕ) : νw (run n 0) = ((n : ℤ), 0, 0) := by
  simp [νw, run, List.count_replicate]

lemma νw_run1 (n : ℕ) : νw (run n 1) = (0, (n : ℤ), 0) := by
  simp [νw, run, List.count_replicate]

lemma seedN_decomp (j k : ℕ) : ∃ H : Multiset Node,
    (seedN j k : Multiset Node) = (emptyType j k, 0) ::ₘ
      ((if j ≠ 0 ∧ k ≠ 0 then ({(100, ((j : ℤ), 0, 0))} : Multiset Node) else 0) + H) ∧
    ∀ x ∈ H, x.1 ∈ harmless := by
  let f : Word × ℕ → Node := fun p => (p.2, νw p.1)
  let A : List Node := ((List.range (j - 1)).map fun a => (run (a + 1) 0, 77)).map f
  let B : List Node := (twoRuns j k).map f
  have hA : ∀ x ∈ A, x.1 ∈ harmless := by
    intro x hx; simp only [A, f, List.mem_map] at hx
    obtain ⟨_, ⟨_, _, rfl⟩, rfl⟩ := hx; simp [harmless]
  have hB : ∀ x ∈ B, x.1 ∈ harmless := by
    intro x hx; simp only [B, f, twoRuns, List.mem_map, List.mem_append] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    rcases hp with hp | ⟨_, _, rfl⟩
    · by_cases hk : k = 0
      · simp [hk] at hp
      · simp only [hk, ↓reduceIte, List.mem_singleton] at hp; subst hp
        dsimp only; split_ifs <;> simp [harmless]
    · dsimp only; split_ifs <;> simp [harmless]
  have hs : seedN j k = f ([], emptyType j k) ::
      (((if j = 0 then [] else [(run j 0, if k = 0 then 356 else 100)]).map f) ++ A ++ B) := by
    simp [seedN, seedList, oneRuns, A, B, f]
  by_cases hj : j = 0
  · refine ⟨↑A + ↑B, ?_, ?_⟩
    · rw [hs]; simp [hj, f, νw_nil]
    · intro x hx; rcases Multiset.mem_add.mp hx with h | h
      · exact hA x h
      · exact hB x h
  · by_cases hk : k = 0
    · refine ⟨(356, ((j : ℤ), 0, 0)) ::ₘ (↑A + ↑B), ?_, ?_⟩
      · rw [hs]; simp [hj, hk, f, νw_nil, νw_run0]
      · intro x hx; rcases Multiset.mem_cons.mp hx with rfl | hx
        · simp [harmless]
        · rcases Multiset.mem_add.mp hx with h | h
          · exact hA x h
          · exact hB x h
    · refine ⟨↑A + ↑B, ?_, ?_⟩
      · rw [hs]; simp [hj, hk, f, νw_nil, νw_run0]
      · intro x hx; rcases Multiset.mem_add.mp hx with h | h
        · exact hA x h
        · exact hB x h

set_option maxRecDepth 10000 in
lemma free_tab : (pos3.all fun t => [false, true].all fun jp => [false, true].all fun kp =>
    (mainTab t jp kp).2.2 == false && (!(mainTab t jp kp).2.1 || kp)) = true := by decide

/-- The unique positive child of a free positive node. -/
lemma free_child (j k : ℕ) {y : Node} (hy : y.1 ∈ pos3) :
    ∃ (tP : ℕ) (l : Bool) (Hf : Multiset Node),
      (childN j k y : Multiset Node) = (tP, M (j : ℤ) k y.2 + off j k l false) ::ₘ Hf ∧
      tP ∈ pos3 ∧ (l = true → k ≠ 0) ∧ ∀ z ∈ Hf, z.1 ∈ harmless := by
  obtain ⟨Hf, e, hHf⟩ := childN_main (j := j) (k := k) (x := y) (Or.inr hy)
  have hm := (main_children (Or.inr hy) (decide (j ≠ 0)) (decide (k ≠ 0))).2.2.mpr hy
  have h := List.all_eq_true.mp free_tab y.1 hy
  have h := List.all_eq_true.mp h (decide (j ≠ 0)) (bool_mem _)
  have h := List.all_eq_true.mp h (decide (k ≠ 0)) (bool_mem _)
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨(mainTab y.1 (decide (j ≠ 0)) (decide (k ≠ 0))).1,
    (mainTab y.1 (decide (j ≠ 0)) (decide (k ≠ 0))).2.1, Hf, ?_, hm, ?_, hHf⟩
  · rw [e]; simp only [mainNode, h1]
  · intro hl; rcases h2 with h2 | h2
    · rw [hl] at h2; exact absurd h2 (by simp)
    · exact h2

/-! Helpers for the exchanges. -/

lemma cone_shift (j k : ℕ) {δ : Vec} (hδ : Cone δ) (c : Vec) (h1 : -(j : ℤ) ≤ c.1)
    (h2 : -(k : ℤ) ≤ c.2.1) (h3 : 0 ≤ c.2.2) : Cone (M (j : ℤ) k δ + c) := by
  obtain ⟨b1, b2, b3⟩ := M_cone j k hδ
  simp only [Cone, Prod.fst_add, Prod.snd_add]; omega

lemma cone_of_nonneg (j k : ℕ) {v : Vec} (hv : TripPairCones.Nonneg v) (c : Vec) (h1 : 0 ≤ c.1)
    (h2 : 0 ≤ c.2.1) (h3 : 1 ≤ c.2.2) : Cone (M (j : ℤ) k v + c) := by
  obtain ⟨b1, b2, b3⟩ := M_nonneg j k hv
  simp only [Cone, Prod.fst_add, Prod.snd_add]; omega

lemma nonneg_child (j k : ℕ) {v : Vec} (hv : TripPairCones.Nonneg v) (l r : Bool) :
    TripPairCones.Nonneg (M (j : ℤ) k v + off j k l r) := by
  obtain ⟨b1, b2, b3⟩ := M_nonneg j k hv
  simp only [TripPairCones.Nonneg, Prod.fst_add, Prod.snd_add, off]
  refine ⟨?_, ?_, ?_⟩ <;> (try split_ifs) <;> omega

lemma adm_of_cone {a b : ℕ} {δ : Vec} (h : Cone δ) : adm a b δ :=
  ⟨by obtain ⟨h1, h2, h3⟩ := h; exact ⟨h1, h2, by omega⟩, fun _ => h⟩

lemma diff_eq (j k : ℤ) (v u c1 c2 : Vec) :
    (M j k v + c1) - (M j k u + c2) = M j k (v - u) + (c1 - c2) := by
  rw [M_sub]; abel

lemma head_mem {t : ℕ} (h : t ∈ heads) : t = 205 ∨ t = 244 ∨ t = 221 := by
  simpa [heads] using h

/-- Multiset of a two-element list. -/
lemma ms_pair (a b : Node) : ((a, b) : Node × Node) ∈ ({(a, b)} : Multiset (Node × Node)) :=
  Multiset.mem_singleton_self _

lemma minv_add_inert {S T : Multiset Node} (hS : MInv S) (hT : ∀ x ∈ T, Inert x) :
    MInv (S + T) := by
  obtain ⟨P, h, f, R, rfl, h1, h2, h3, h4, h5, h6, h7⟩ := hS
  refine ⟨P, h, f, R + T, by abel, h1, ?_, h3, h4, h5, h6, h7⟩
  intro x hx; rcases Multiset.mem_add.mp hx with hx | hx
  · exact h2 x hx
  · exact hT x hx

lemma minv_add_pair {S : Multiset Node} (hS : MInv S) (x : Node × Node) (hx : PairOK x) :
    MInv (S + {x.1} + {x.2}) := by
  obtain ⟨P, h, f, R, rfl, h1, h2, h3, h4, h5, h6, h7⟩ := hS
  refine ⟨x ::ₘ P, h, f, R, ?_, ?_, h2, h3, h4, h5, h6, h7⟩
  · simp only [Multiset.map_cons, ← Multiset.singleton_add, Multiset.map_add,
      Multiset.map_singleton]; abel
  · intro y hy; rcases Multiset.mem_cons.mp hy with rfl | hy
    · exact hx
    · exact h1 y hy

lemma minv_head_free (h f : Option Node) (hh : ∀ x ∈ h, x.1 ∈ heads ∧ TripPairCones.Nonneg x.2)
    (hf : ∀ x ∈ f, x.1 ∈ pos3 ∧ TripPairCones.Nonneg x.2) (hhf : h = none → f = none)
    (h221 : ∀ x ∈ h, x.1 = 221 → f = none) (hc : ∀ x ∈ h, ∀ y ∈ f, Cone (y.2 - x.2)) :
    MInv ((h.toList : Multiset Node) + (f.toList : Multiset Node)) :=
  ⟨0, h, f, 0, by simp, by simp, by simp, hh, hf, hhf, h221, hc⟩

lemma inert_of_harmless {x : Node} (h : x.1 ∈ harmless) : Inert x := Or.inl h
lemma inert_of_neg {x : Node} (h : x.1 ∈ negs) : Inert x := Or.inr h

/-- Rearrangement used in every exchange: a multiset equation reduces MInv. -/
lemma minv_congr {S T : Multiset Node} (h : S = T) (hT : MInv T) : MInv S := h ▸ hT

lemma pairOK_cone {nt pt : ℕ} (hn : nt ∈ negs) (hp : pt ∈ pos3) {a b : Vec}
    (h : Cone (b - a)) : PairOK ((nt, a), (pt, b)) := ⟨hn, hp, adm_of_cone h⟩

lemma pairOK_zero {nt pt : ℕ} (hn : nt ∈ negs) (hp : pt ∈ pos3) (hc : ¬ coneType nt pt)
    {a b : Vec} (h : b = a) : PairOK ((nt, a), (pt, b)) :=
  ⟨hn, hp, ⟨by subst h; simp [TripPairCones.Nonneg], fun h' => absurd h' hc⟩⟩

lemma sub_eq_M (j k : ℤ) (v c w : Vec) : (M j k v + c) - w = M j k v + (c - w) := by abel

-- Close a multiset rearrangement after expanding children.
set_option hygiene false in
macro "ms_eq" : tactic => `(tactic| (
  simp only [Option.toList_some, Option.toList_none, ← Multiset.cons_coe, Multiset.coe_nil,
    Multiset.zero_bind, Multiset.cons_bind, Multiset.singleton_bind, add_zero, zero_add]
  all_goals (try rw [hd])
  all_goals (try simp only [childTab, List.map_cons, List.map_nil, ← Multiset.cons_coe,
    Multiset.coe_nil])
  all_goals (try rw [eF])
  all_goals (try simp only [← Multiset.singleton_add, add_zero, zero_add])
  all_goals (try abel)))

/-- Regime j > 0, k > 0: the new empty seed is the free head 221. -/
lemma hf_jk (j k : ℕ) (hj : j ≠ 0) (hk : k ≠ 0) (h f : Option Node)
    (hh : ∀ x ∈ h, x.1 ∈ heads ∧ TripPairCones.Nonneg x.2)
    (hf : ∀ x ∈ f, x.1 ∈ pos3 ∧ TripPairCones.Nonneg x.2) (hhf : h = none → f = none)
    (h221 : ∀ x ∈ h, x.1 = 221 → f = none) (hc : ∀ x ∈ h, ∀ y ∈ f, Cone (y.2 - x.2)) :
    MInv ((seedN j k : Multiset Node) +
      (h.toList : Multiset Node).bind (fun x => (childN j k x : Multiset Node)) +
      (f.toList : Multiset Node).bind (fun x => (childN j k x : Multiset Node))) := by
  obtain ⟨H, eS, hH⟩ := seedN_decomp j k
  have hHi : ∀ x ∈ H, Inert x := fun x hx => Or.inl (hH x hx)
  have et : emptyType j k = 221 := by simp [emptyType, hj, hk]
  simp only [et, hj, hk, ne_eq, not_false_eq_true, and_self, ↓reduceIte] at eS
  rw [eS]
  set z : Node := (100, ((j : ℤ), 0, 0)) with hz
  have hd : ∀ (t : ℕ) (u : Vec), (childN j k (t, u) : Multiset Node) =
      ((childTab t true true).map fun e => (e.1, M (j : ℤ) k u + off j k e.2.1 e.2.2) : List Node) := by
    intro t u; simp [childN, hj, hk]
  have o1 : off j k false false = ((j : ℤ), 0, 1) := by simp [off]
  have o2 : off j k false true = ((j : ℤ), (k : ℤ), 1) := by simp [off, hk]
  have o3 : off j k true false = ((j : ℤ), (k : ℤ), 1) := by simp [off]
  have head0 : MInv (((some ((221 : ℕ), (0 : Vec))).toList : Multiset Node) +
      ((none : Option Node).toList : Multiset Node)) :=
    minv_head_free _ _ (by simp [heads, TripPairCones.Nonneg]) (by simp) (by simp) (by simp)
      (by simp)
  rcases h with _ | ⟨th, u⟩
  · have := hhf rfl; subst this
    refine minv_congr ?_ (minv_add_inert head0 (T := z ::ₘ H) ?_)
    · ms_eq
    · intro x hx; rcases Multiset.mem_cons.mp hx with rfl | hx
      · exact inert_of_neg (by simp [negs, hz])
      · exact hHi x hx
  · obtain ⟨hth, hu⟩ := hh _ rfl
    have hu' := M_nonneg j k hu
    rcases head_mem hth with rfl | rfl | rfl
    · -- head 205: children 27, 17, 200
      rcases f with _ | y
      · refine minv_congr ?_ (minv_add_inert (minv_add_pair head0 (z, (27, M (j : ℤ) k u +
          off j k false false)) ?_) (T := (17, M (j : ℤ) k u + off j k false true) ::ₘ
          (200, M (j : ℤ) k u + off j k true false) ::ₘ H) ?_)
        · ms_eq
        · apply pairOK_cone (by simp [negs]) (by simp [pos3])
          rw [sub_eq_M]; apply cone_of_nonneg j k hu <;> simp [o1, hz]
        · intro x hx; simp only [Multiset.mem_cons] at hx
          rcases hx with rfl | rfl | hx
          · exact inert_of_neg (by simp [negs, hz])
          · exact inert_of_harmless (by simp [harmless])
          · exact hHi x hx
      · obtain ⟨hy1, hy2⟩ := hf y rfl
        obtain ⟨tP, l, Hf, eF, htP, hl, hHf⟩ := free_child j k hy1
        have hcone := hc _ rfl y rfl
        refine minv_congr ?_ (minv_add_inert (minv_add_pair (minv_add_pair head0 (z, (27,
          M (j : ℤ) k u + off j k false false)) ?_) ((17, M (j : ℤ) k u + off j k false true),
          (tP, M (j : ℤ) k y.2 + off j k l false)) ?_)
          (T := (200, M (j : ℤ) k u + off j k true false) ::ₘ (H + Hf)) ?_)
        · ms_eq
        · apply pairOK_cone (by simp [negs]) (by simp [pos3])
          rw [sub_eq_M]; apply cone_of_nonneg j k hu <;> simp [o1, hz]
        · apply pairOK_cone (by simp [negs]) htP
          rw [diff_eq]; apply cone_shift j k hcone <;> cases l <;> simp [off, o2, hk]
        · intro x hx; simp only [Multiset.mem_cons, Multiset.mem_add] at hx
          rcases hx with rfl | hx | hx
          · exact inert_of_harmless (by simp [harmless])
          · exact hHi x hx
          · exact inert_of_harmless (hHf x hx)
    · -- head 244: only harmless children
      rcases f with _ | y
      · refine minv_congr ?_ (minv_add_inert head0 (T := z ::ₘ
          (H + (childN j k (244, u) : Multiset Node))) ?_)
        · ms_eq
        · intro x hx; simp only [Multiset.mem_cons, Multiset.mem_add] at hx
          rcases hx with rfl | hx | hx
          · exact inert_of_neg (by simp [negs, hz])
          · exact hHi x hx
          · rw [hd] at hx; simp [childTab, harmless] at hx
            rcases hx with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> left <;> simp [harmless]
      · obtain ⟨hy1, hy2⟩ := hf y rfl
        obtain ⟨tP, l, Hf, eF, htP, hl, hHf⟩ := free_child j k hy1
        refine minv_congr ?_ (minv_add_inert (minv_add_pair head0 (z,
          (tP, M (j : ℤ) k y.2 + off j k l false)) ?_)
          (T := H + Hf + (childN j k (244, u) : Multiset Node)) ?_)
        · ms_eq
        · apply pairOK_cone (by simp [negs]) htP
          rw [sub_eq_M]; apply cone_of_nonneg j k hy2 <;> cases l <;> simp [off, hz]
        · intro x hx; simp only [Multiset.mem_add] at hx
          rcases hx with (hx | hx) | hx
          · exact hHi x hx
          · exact inert_of_harmless (hHf x hx)
          · rw [hd] at hx; simp [childTab, harmless] at hx
            rcases hx with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> left <;> simp [harmless]
    · -- head 221 (no free): children 27, 17, 216
      have := h221 _ rfl rfl; subst this
      refine minv_congr ?_ (minv_add_inert (minv_add_pair (minv_add_pair head0 (z, (27,
          M (j : ℤ) k u + off j k false false)) ?_) ((17, M (j : ℤ) k u + off j k false true),
          (216, M (j : ℤ) k u + off j k true false)) ?_) (T := H) hHi)
      · ms_eq
      · apply pairOK_cone (by simp [negs]) (by simp [pos3])
        rw [sub_eq_M]; apply cone_of_nonneg j k hu <;> simp [o1, hz]
      · apply pairOK_zero (by simp [negs]) (by simp [pos3]) (by simp [coneType])
        rw [o2, o3]

/-- Regime j > 0, k = 0: the new empty seed is the neutral head 205. -/
lemma hf_j0 (j : ℕ) (hj : j ≠ 0) (h f : Option Node)
    (hh : ∀ x ∈ h, x.1 ∈ heads ∧ TripPairCones.Nonneg x.2)
    (hf : ∀ x ∈ f, x.1 ∈ pos3 ∧ TripPairCones.Nonneg x.2) (hhf : h = none → f = none)
    (h221 : ∀ x ∈ h, x.1 = 221 → f = none) (hc : ∀ x ∈ h, ∀ y ∈ f, Cone (y.2 - x.2)) :
    MInv ((seedN j 0 : Multiset Node) +
      (h.toList : Multiset Node).bind (fun x => (childN j 0 x : Multiset Node)) +
      (f.toList : Multiset Node).bind (fun x => (childN j 0 x : Multiset Node))) := by
  obtain ⟨H, eS, hH⟩ := seedN_decomp j 0
  have hHi : ∀ x ∈ H, Inert x := fun x hx => Or.inl (hH x hx)
  have et : emptyType j 0 = 205 := by simp [emptyType, hj]
  simp only [et, ne_eq, not_true_eq_false, and_false, ↓reduceIte, zero_add] at eS
  rw [eS]
  have hd : ∀ (t : ℕ) (u : Vec), (childN j 0 (t, u) : Multiset Node) =
      ((childTab t true false).map fun e => (e.1, M (j : ℤ) 0 u + off j 0 e.2.1 e.2.2) : List Node) := by
    intro t u; simp [childN, hj]
  have o1 : off j 0 false false = ((j : ℤ), 0, 1) := by simp [off]
  have o2 : off j 0 false true = ((j : ℤ) + j, 0, 1) := by simp [off]
  have oP : ∀ l : Bool, off j 0 l false = ((j : ℤ), 0, 1) := by intro l; cases l <;> simp [off]
  have base : ∀ f' : Option Node, (∀ x ∈ f', x.1 ∈ pos3 ∧ TripPairCones.Nonneg x.2) →
      (∀ y ∈ f', Cone (y.2 - 0)) →
      MInv (((some ((205 : ℕ), (0 : Vec))).toList : Multiset Node) + (f'.toList : Multiset Node)) :=
    fun f' h1 h2 => minv_head_free _ _ (by simp [heads, TripPairCones.Nonneg]) h1 (by simp)
      (by simp) (by simpa using h2)
  rcases h with _ | ⟨th, u⟩
  · have := hhf rfl; subst this
    refine minv_congr ?_ (minv_add_inert (base none (by simp) (by simp)) (T := H) hHi)
    · ms_eq
  · obtain ⟨hth, hu⟩ := hh _ rfl
    rcases head_mem hth with rfl | rfl | rfl
    · -- head 205: harmless children only
      rcases f with _ | y
      · refine minv_congr ?_ (minv_add_inert (base none (by simp) (by simp))
          (T := H + (childN j 0 (205, u) : Multiset Node)) ?_)
        · ms_eq
        · intro x hx; rcases Multiset.mem_add.mp hx with hx | hx
          · exact hHi x hx
          · rw [hd] at hx; simp [childTab] at hx
            rcases hx with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> left <;> simp [harmless]
      · obtain ⟨hy1, hy2⟩ := hf y rfl
        obtain ⟨tP, l, Hf, eF, htP, hl, hHf⟩ := free_child j 0 hy1
        simp only [Nat.cast_zero] at eF
        refine minv_congr ?_ (minv_add_inert (base (some (tP, M (j : ℤ) 0 y.2 + off j 0 l false))
          (by simpa using ⟨htP, nonneg_child j 0 hy2 l false⟩) ?_)
          (T := H + Hf + (childN j 0 (205, u) : Multiset Node)) ?_)
        · ms_eq
        · simp only [Option.mem_def, Option.some.injEq, forall_eq', sub_zero]
          apply cone_of_nonneg j 0 hy2 <;> simp [oP]
        · intro x hx; simp only [Multiset.mem_add] at hx
          rcases hx with (hx | hx) | hx
          · exact hHi x hx
          · exact inert_of_harmless (hHf x hx)
          · rw [hd] at hx; simp [childTab] at hx
            rcases hx with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> left <;> simp [harmless]
    · -- head 244: children 217 and 100
      have c217 : TripPairCones.Nonneg (M (j : ℤ) 0 u + off j 0 false false) := nonneg_child j 0 hu _ _
      have bc : MInv (((some ((205 : ℕ), (0 : Vec))).toList : Multiset Node) +
          ((some ((217 : ℕ), M (j : ℤ) 0 u + off j 0 false false)).toList : Multiset Node)) :=
        base _ (by simpa [pos3] using c217) (by
          simp only [Option.mem_def, Option.some.injEq, forall_eq', sub_zero]
          apply cone_of_nonneg j 0 hu <;> simp [o1])
      rcases f with _ | y
      · refine minv_congr ?_ (minv_add_inert bc (T := (100, M (j : ℤ) 0 u + off j 0 false true) ::ₘ H) ?_)
        · ms_eq
        · intro x hx; rcases Multiset.mem_cons.mp hx with rfl | hx
          · exact inert_of_neg (by simp [negs])
          · exact hHi x hx
      · obtain ⟨hy1, hy2⟩ := hf y rfl
        obtain ⟨tP, l, Hf, eF, htP, hl, hHf⟩ := free_child j 0 hy1
        simp only [Nat.cast_zero] at eF
        have hcone := hc _ rfl y rfl
        refine minv_congr ?_ (minv_add_inert (minv_add_pair bc ((100, M (j : ℤ) 0 u + off j 0 false true),
          (tP, M (j : ℤ) 0 y.2 + off j 0 l false)) ?_) (T := H + Hf) ?_)
        · ms_eq
        · apply pairOK_cone (by simp [negs]) htP
          rw [diff_eq]; apply cone_shift j 0 hcone <;> simp [oP, o2]
        · intro x hx; rcases Multiset.mem_add.mp hx with hx | hx
          · exact hHi x hx
          · exact inert_of_harmless (hHf x hx)
    · -- head 221: child 217 becomes free
      have := h221 _ rfl rfl; subst this
      have c217 : TripPairCones.Nonneg (M (j : ℤ) 0 u + off j 0 false false) := nonneg_child j 0 hu _ _
      refine minv_congr ?_ (minv_add_inert (base (some (217, M (j : ℤ) 0 u + off j 0 false false))
        (by simpa [pos3] using c217) ?_) (T := (77, M (j : ℤ) 0 u + off j 0 false true) ::ₘ H) ?_)
      · ms_eq
      · simp only [Option.mem_def, Option.some.injEq, forall_eq', sub_zero]
        apply cone_of_nonneg j 0 hu <;> simp [o1]
      · intro x hx; rcases Multiset.mem_cons.mp hx with rfl | hx
        · exact inert_of_harmless (by simp [harmless])
        · exact hHi x hx

/-- Regime j = 0, k > 0: the new empty seed is the neutral head 244. -/
lemma hf_0k (k : ℕ) (hk : k ≠ 0) (h f : Option Node)
    (hh : ∀ x ∈ h, x.1 ∈ heads ∧ TripPairCones.Nonneg x.2)
    (hf : ∀ x ∈ f, x.1 ∈ pos3 ∧ TripPairCones.Nonneg x.2) (hhf : h = none → f = none)
    (h221 : ∀ x ∈ h, x.1 = 221 → f = none) (hc : ∀ x ∈ h, ∀ y ∈ f, Cone (y.2 - x.2)) :
    MInv ((seedN 0 k : Multiset Node) +
      (h.toList : Multiset Node).bind (fun x => (childN 0 k x : Multiset Node)) +
      (f.toList : Multiset Node).bind (fun x => (childN 0 k x : Multiset Node))) := by
  obtain ⟨H, eS, hH⟩ := seedN_decomp 0 k
  have hHi : ∀ x ∈ H, Inert x := fun x hx => Or.inl (hH x hx)
  have et : emptyType 0 k = 244 := by simp [emptyType, hk]
  simp only [et, ne_eq, not_true_eq_false, false_and, ↓reduceIte, zero_add] at eS
  rw [eS]
  have hd : ∀ (t : ℕ) (u : Vec), (childN 0 k (t, u) : Multiset Node) =
      ((childTab t false true).map fun e => (e.1, M (0 : ℤ) k u + off 0 k e.2.1 e.2.2) : List Node) := by
    intro t u; simp [childN, hk]
  have o1 : off 0 k false false = (0, 0, 1) := by simp [off]
  have o2 : off 0 k false true = (0, (k : ℤ), 1) := by simp [off, hk]
  have o3 : off 0 k true false = (0, (k : ℤ), 1) := by simp [off]
  have oP : ∀ l : Bool, off 0 k l false = (0, if l then (k : ℤ) else 0, 1) := by
    intro l; cases l <;> simp [off]
  have base : ∀ f' : Option Node, (∀ x ∈ f', x.1 ∈ pos3 ∧ TripPairCones.Nonneg x.2) →
      (∀ y ∈ f', Cone (y.2 - 0)) →
      MInv (((some ((244 : ℕ), (0 : Vec))).toList : Multiset Node) + (f'.toList : Multiset Node)) :=
    fun f' h1 h2 => minv_head_free _ _ (by simp [heads, TripPairCones.Nonneg]) h1 (by simp)
      (by simp) (by simpa using h2)
  have M0 : ((0 : ℕ) : ℤ) = 0 := rfl
  rcases h with _ | ⟨th, u⟩
  · have := hhf rfl; subst this
    refine minv_congr ?_ (minv_add_inert (base none (by simp) (by simp)) (T := H) hHi)
    · ms_eq
  · obtain ⟨hth, hu⟩ := hh _ rfl
    have c27 : TripPairCones.Nonneg (M (0 : ℤ) k u + off 0 k false false) := nonneg_child 0 k hu _ _
    have bc : MInv (((some ((244 : ℕ), (0 : Vec))).toList : Multiset Node) +
        ((some ((27 : ℕ), M (0 : ℤ) k u + off 0 k false false)).toList : Multiset Node)) :=
      base _ (by simpa [pos3] using c27) (by
        simp only [Option.mem_def, Option.some.injEq, forall_eq', sub_zero]
        apply cone_of_nonneg 0 k hu <;> simp [o1])
    rcases head_mem hth with rfl | rfl | rfl
    · -- head 205: children 27, 20, 200
      rcases f with _ | y
      · refine minv_congr ?_ (minv_add_inert bc (T := (20, M (0 : ℤ) k u + off 0 k false true) ::ₘ
          (200, M (0 : ℤ) k u + off 0 k true false) ::ₘ H) ?_)
        · ms_eq
        · intro x hx; simp only [Multiset.mem_cons] at hx
          rcases hx with rfl | rfl | hx
          · exact inert_of_neg (by simp [negs])
          · exact inert_of_harmless (by simp [harmless])
          · exact hHi x hx
      · obtain ⟨hy1, hy2⟩ := hf y rfl
        obtain ⟨tP, l, Hf, eF, htP, hl, hHf⟩ := free_child 0 k hy1
        simp only [Nat.cast_zero] at eF
        have hcone := hc _ rfl y rfl
        refine minv_congr ?_ (minv_add_inert (minv_add_pair bc ((20, M (0 : ℤ) k u + off 0 k false true),
          (tP, M (0 : ℤ) k y.2 + off 0 k l false)) ?_)
          (T := (200, M (0 : ℤ) k u + off 0 k true false) ::ₘ (H + Hf)) ?_)
        · ms_eq
        · apply pairOK_cone (by simp [negs]) htP
          rw [diff_eq]; apply cone_shift 0 k hcone <;> cases l <;> simp [oP, o2]
        · intro x hx; simp only [Multiset.mem_cons, Multiset.mem_add] at hx
          rcases hx with rfl | hx | hx
          · exact inert_of_harmless (by simp [harmless])
          · exact hHi x hx
          · exact inert_of_harmless (hHf x hx)
    · -- head 244: harmless children only
      rcases f with _ | y
      · refine minv_congr ?_ (minv_add_inert (base none (by simp) (by simp))
          (T := H + (childN 0 k (244, u) : Multiset Node)) ?_)
        · ms_eq
        · intro x hx; rcases Multiset.mem_add.mp hx with hx | hx
          · exact hHi x hx
          · rw [hd] at hx; simp [childTab] at hx
            rcases hx with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> left <;> simp [harmless]
      · obtain ⟨hy1, hy2⟩ := hf y rfl
        obtain ⟨tP, l, Hf, eF, htP, hl, hHf⟩ := free_child 0 k hy1
        simp only [Nat.cast_zero] at eF
        refine minv_congr ?_ (minv_add_inert (base (some (tP, M (0 : ℤ) k y.2 + off 0 k l false))
          (by simpa using ⟨htP, nonneg_child 0 k hy2 l false⟩) ?_)
          (T := H + Hf + (childN 0 k (244, u) : Multiset Node)) ?_)
        · ms_eq
        · simp only [Option.mem_def, Option.some.injEq, forall_eq', sub_zero]
          apply cone_of_nonneg 0 k hy2 <;> cases l <;> simp [oP]
        · intro x hx; simp only [Multiset.mem_add] at hx
          rcases hx with (hx | hx) | hx
          · exact hHi x hx
          · exact inert_of_harmless (hHf x hx)
          · rw [hd] at hx; simp [childTab] at hx
            rcases hx with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> left <;> simp [harmless]
    · -- head 221: 27 free, pair (20, 216)
      have := h221 _ rfl rfl; subst this
      refine minv_congr ?_ (minv_add_inert (minv_add_pair bc ((20, M (0 : ℤ) k u + off 0 k false true),
        (216, M (0 : ℤ) k u + off 0 k true false)) ?_) (T := H) hHi)
      · ms_eq
      · apply pairOK_zero (by simp [negs]) (by simp [pos3]) (by simp [coneType])
        rw [o2, o3]

/-- Regime j = k = 0: heads and the free positive propagate. -/
lemma hf_00 (h f : Option Node)
    (hh : ∀ x ∈ h, x.1 ∈ heads ∧ TripPairCones.Nonneg x.2)
    (hf : ∀ x ∈ f, x.1 ∈ pos3 ∧ TripPairCones.Nonneg x.2) (hhf : h = none → f = none)
    (h221 : ∀ x ∈ h, x.1 = 221 → f = none) (hc : ∀ x ∈ h, ∀ y ∈ f, Cone (y.2 - x.2)) :
    MInv ((seedN 0 0 : Multiset Node) +
      (h.toList : Multiset Node).bind (fun x => (childN 0 0 x : Multiset Node)) +
      (f.toList : Multiset Node).bind (fun x => (childN 0 0 x : Multiset Node))) := by
  obtain ⟨H, eS, hH⟩ := seedN_decomp 0 0
  have hHi : ∀ x ∈ H, Inert x := fun x hx => Or.inl (hH x hx)
  have et : emptyType 0 0 = 484 := by simp [emptyType]
  simp only [et, ne_eq, not_true_eq_false, false_and, ↓reduceIte, zero_add] at eS
  rw [eS]
  have hd : ∀ (t : ℕ) (u : Vec), (childN 0 0 (t, u) : Multiset Node) =
      ((childTab t false false).map fun e => (e.1, M (0 : ℤ) 0 u + off 0 0 e.2.1 e.2.2) : List Node) := by
    intro t u; simp [childN]
  have oP : ∀ l : Bool, off 0 0 l false = (0, 0, 1) := by intro l; cases l <;> simp [off]
  have h484 : ∀ x ∈ (484, (0 : Vec)) ::ₘ H, Inert x := by
    intro x hx; rcases Multiset.mem_cons.mp hx with rfl | hx
    · exact inert_of_harmless (by simp [harmless])
    · exact hHi x hx
  rcases h with _ | ⟨th, u⟩
  · have := hhf rfl; subst this
    refine minv_congr ?_ (minv_add_inert (minv_head_free none none (by simp) (by simp) (by simp)
      (by simp) (by simp)) (T := (484, (0 : Vec)) ::ₘ H) h484)
    · ms_eq
  · obtain ⟨hth, hu⟩ := hh _ rfl
    have hch : (childN 0 0 (th, u) : Multiset Node) = {(th, M (0 : ℤ) 0 u + off 0 0 false false)} := by
      rw [hd]; rcases head_mem hth with rfl | rfl | rfl <;> simp [childTab]
    have hc' : TripPairCones.Nonneg (M (0 : ℤ) 0 u + off 0 0 false false) := nonneg_child 0 0 hu _ _
    rcases f with _ | y
    · refine minv_congr ?_ (minv_add_inert (minv_head_free (some (th, M (0 : ℤ) 0 u +
        off 0 0 false false)) none (by simpa using ⟨hth, hc'⟩) (by simp) (by simp) (by simp)
        (by simp)) (T := (484, (0 : Vec)) ::ₘ H) h484)
      · simp only [Option.toList_some, Option.toList_none, ← Multiset.cons_coe, Multiset.coe_nil,
          Multiset.zero_bind, Multiset.cons_bind, Multiset.singleton_bind, add_zero, zero_add]
        rw [hch]; simp only [← Multiset.singleton_add, add_zero, zero_add]; abel
    · obtain ⟨hy1, hy2⟩ := hf y rfl
      obtain ⟨tP, l, Hf, eF, htP, hl, hHf⟩ := free_child 0 0 hy1
      simp only [Nat.cast_zero] at eF
      have hcone := hc _ rfl y rfl
      have hnot : th ≠ 221 := fun h' => by have := h221 _ rfl h'; simp at this
      refine minv_congr ?_ (minv_add_inert (minv_head_free (some (th, M (0 : ℤ) 0 u +
        off 0 0 false false)) (some (tP, M (0 : ℤ) 0 y.2 + off 0 0 l false))
        (by simpa using ⟨hth, hc'⟩) (by simpa using ⟨htP, nonneg_child 0 0 hy2 l false⟩)
        (by simp) (by simpa using hnot) ?_) (T := (484, (0 : Vec)) ::ₘ (H + Hf)) ?_)
      · simp only [Option.toList_some, Option.toList_none, ← Multiset.cons_coe, Multiset.coe_nil,
          Multiset.zero_bind, Multiset.cons_bind, Multiset.singleton_bind, add_zero, zero_add]
        rw [hch, eF]; simp only [← Multiset.singleton_add, add_zero, zero_add]; abel
      · simp only [Option.mem_def, Option.some.injEq, forall_eq']
        rw [diff_eq]; apply cone_shift 0 0 hcone <;> simp [oP]
      · intro x hx; simp only [Multiset.mem_cons, Multiset.mem_add] at hx
        rcases hx with rfl | hx | hx
        · exact inert_of_harmless (by simp [harmless])
        · exact hHi x hx
        · exact inert_of_harmless (hHf x hx)

end Trip
```

### `TripMatchForest.lean`

```lean
import TripMatchStep

/-! The matching invariant holds on every abstract forest, hence
Σ_{nodes of length < n} m ≤ 1. -/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

namespace Trip
open TripPairCones

theorem hf_step (j k : ℕ) (h f : Option Node)
    (hh : ∀ x ∈ h, x.1 ∈ heads ∧ TripPairCones.Nonneg x.2)
    (hf : ∀ x ∈ f, x.1 ∈ pos3 ∧ TripPairCones.Nonneg x.2) (hhf : h = none → f = none)
    (h221 : ∀ x ∈ h, x.1 = 221 → f = none) (hc : ∀ x ∈ h, ∀ y ∈ f, Cone (y.2 - x.2)) :
    MInv ((seedN j k : Multiset Node) +
      (h.toList : Multiset Node).bind (fun x => (childN j k x : Multiset Node)) +
      (f.toList : Multiset Node).bind (fun x => (childN j k x : Multiset Node))) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj <;> rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact hf_00 h f hh hf hhf h221 hc
  · exact hf_0k k (by omega) h f hh hf hhf h221 hc
  · exact hf_j0 j (by omega) h f hh hf hhf h221 hc
  · exact hf_jk j k (by omega) (by omega) h f hh hf hhf h221 hc

theorem pairs_bind (j k : ℕ) : ∀ (P : Multiset (Node × Node)), (∀ x ∈ P, PairOK x) →
    ∃ (P' : Multiset (Node × Node)) (R' : Multiset Node),
      (P.map Prod.fst).bind (fun x => (childN j k x : Multiset Node)) +
        (P.map Prod.snd).bind (fun x => (childN j k x : Multiset Node)) =
        P'.map Prod.fst + P'.map Prod.snd + R' ∧ (∀ x ∈ P', PairOK x) ∧ ∀ y ∈ R', Inert y := by
  intro P
  induction P using Multiset.induction_on with
  | empty => intro _; exact ⟨0, 0, by simp, by simp, by simp⟩
  | cons x P ih =>
    intro hP
    obtain ⟨P', R', e, h1, h2⟩ := ih (fun y hy => hP y (Multiset.mem_cons_of_mem hy))
    obtain ⟨x', H, ex, hx', hH⟩ := pair_step j k x (hP x (Multiset.mem_cons_self x P))
    refine ⟨x' ::ₘ P', H + R', ?_, ?_, ?_⟩
    · simp only [Multiset.map_cons, Multiset.cons_bind]
      calc (childN j k x.1 : Multiset Node) + (P.map Prod.fst).bind (fun x => (childN j k x : Multiset Node)) +
            ((childN j k x.2 : Multiset Node) + (P.map Prod.snd).bind (fun x => (childN j k x : Multiset Node)))
          = ((childN j k x.1 : Multiset Node) + childN j k x.2) +
            ((P.map Prod.fst).bind (fun x => (childN j k x : Multiset Node)) +
              (P.map Prod.snd).bind (fun x => (childN j k x : Multiset Node))) := by abel
        _ = _ := by
          rw [ex, e]; simp only [← Multiset.singleton_add]; abel
    · intro y hy; rcases Multiset.mem_cons.mp hy with rfl | hy
      · exact hx'
      · exact h1 y hy
    · intro y hy; rcases Multiset.mem_add.mp hy with hy | hy
      · exact hH y hy
      · exact h2 y hy

theorem minv_step (j k : ℕ) (F : List Node) (hF : MInv (F : Multiset Node)) :
    MInv ((seedN j k ++ F.flatMap (childN j k) : List Node) : Multiset Node) := by
  obtain ⟨P, h, f, R, hEq, hP, hR, hh, hf, hhf, h221, hc⟩ := hF
  have hb : ((F.flatMap (childN j k) : List Node) : Multiset Node) =
      (F : Multiset Node).bind (fun x => (childN j k x : Multiset Node)) :=
    (Multiset.coe_bind F (childN j k)).symm
  rw [← Multiset.coe_add, hb, hEq]
  simp only [Multiset.add_bind]
  obtain ⟨P1, R1, e1, hP1, hR1⟩ := pairs_bind j k P hP
  obtain ⟨P2, h', f', R2, e2, hP2, hR2, hh', hf', hhf', h221', hc'⟩ :=
    hf_step j k h f hh hf hhf h221 hc
  refine ⟨P1 + P2, h', f', R1 + R2 + R.bind (fun x => (childN j k x : Multiset Node)), ?_, ?_, ?_,
    hh', hf', hhf', h221', hc'⟩
  · calc (seedN j k : Multiset Node) +
          ((P.map Prod.fst).bind (fun x => (childN j k x : Multiset Node)) +
            (P.map Prod.snd).bind (fun x => (childN j k x : Multiset Node)) +
            (h.toList : Multiset Node).bind (fun x => (childN j k x : Multiset Node)) +
            (f.toList : Multiset Node).bind (fun x => (childN j k x : Multiset Node)) +
            R.bind (fun x => (childN j k x : Multiset Node)))
        = ((seedN j k : Multiset Node) +
            (h.toList : Multiset Node).bind (fun x => (childN j k x : Multiset Node)) +
            (f.toList : Multiset Node).bind (fun x => (childN j k x : Multiset Node))) +
          ((P.map Prod.fst).bind (fun x => (childN j k x : Multiset Node)) +
            (P.map Prod.snd).bind (fun x => (childN j k x : Multiset Node))) +
          R.bind (fun x => (childN j k x : Multiset Node)) := by abel
      _ = _ := by rw [e1, e2]; simp only [Multiset.map_add]; abel
  · intro x hx; rcases Multiset.mem_add.mp hx with hx | hx
    · exact hP1 x hx
    · exact hP2 x hx
  · intro x hx; rcases Multiset.mem_add.mp hx with hx | hx
    · rcases Multiset.mem_add.mp hx with hx | hx
      · exact hR1 x hx
      · exact hR2 x hx
    · obtain ⟨y, hy, hx⟩ := Multiset.mem_bind.mp hx
      exact inert_childN (hR y hy) x hx

lemma minv_nil : MInv ((([] : List Node)) : Multiset Node) :=
  ⟨0, none, none, 0, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩

theorem minv_forest (g : ℕ → ℕ × ℕ) : ∀ D i, MInv ((forestN g i D : List Node) : Multiset Node)
  | 0, i => by
    have := minv_step (g i).1 (g i).2 [] minv_nil
    simpa [forestN] using this
  | D + 1, i => by
    have := minv_step (g i).1 (g i).2 _ (minv_forest g D (i + 1))
    simpa [forestN] using this

/-- The abstract bound: every finite production forest has Σ_{|x| < n} m(x) ≤ 1. -/
theorem forest_bound (g : ℕ → ℕ × ℕ) (D i : ℕ) (n : ℤ) :
    ((forestN g i D).map (wt n)).sum ≤ 1 := by
  have := minv_bound (minv_forest g D i) n
  simpa using this

#print axioms forest_bound
end Trip
```

### `TripStep.lean`

```lean
import TripSeeds

/-! One desubstitution level: the bispecial factors of an image language are
the seeds and the children of the bispecial factors of the antecedent
language, with the graph transform TG. -/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

namespace Trip

structure Good (L : Word → Prop) : Prop where
  fac : Factorial L
  left : LeftExtendable L
  right : ∀ w, L w → ∃ b : Letter, L (w ++ [b])
  letters : ∀ c : Letter, L [c]

lemma TG_apply (g : Gr) (jp kp l r : Bool) (y z : Letter) :
    TG g jp kp l r y z = true ↔
      ∃ c d, g c d = true ∧ alphaL kp l c = some y ∧ alphaR jp kp r d = some z := by
  simp only [TG, List.any_eq_true, List.mem_finRange, true_and, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨c, d, ⟨h1, h2⟩, h3⟩; exact ⟨c, d, h1, h2, h3⟩
  · rintro ⟨c, d, h1, h2, h3⟩; exact ⟨c, d, ⟨h1, h2⟩, h3⟩

theorem child_edges {L : Word → Prop} (hL : Good L) (j k : ℕ) (l r : Bool)
    (hl : l = true → 0 < k) (hr : r = true → 0 < j ∨ 0 < k) (v : Word) :
    edges (imageLanguage L j k) (child j k l r v) =
      TG (edges L v) (decide (j ≠ 0)) (decide (k ≠ 0)) l r := by
  funext y z
  apply Bool.eq_iff_iff.mpr
  rw [edges_apply, child_edge_iff L hL.fac hL.left j k l r hl hr v y z, TG_apply]
  simp only [edges_apply]

lemma leftSet_TG_le (g : Gr) (jp kp l r : Bool) :
    (leftSet (TG g jp kp l r)).card ≤ (leftSet g).card := by
  have hsub : (leftSet (TG g jp kp l r)).map ⟨some, Option.some_injective _⟩ ⊆
      (leftSet g).image (alphaL kp l) := by
    intro o ho
    simp only [Finset.mem_map, leftSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk] at ho
    obtain ⟨y, ⟨z, hz⟩, rfl⟩ := ho
    rw [TG_apply] at hz
    obtain ⟨c, d, h1, h2, -⟩ := hz
    simp only [Finset.mem_image, leftSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨c, ⟨d, h1⟩, h2⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_map] at this
  exact this.trans Finset.card_image_le

lemma rightSet_TG_le (g : Gr) (jp kp l r : Bool) :
    (rightSet (TG g jp kp l r)).card ≤ (rightSet g).card := by
  have hsub : (rightSet (TG g jp kp l r)).map ⟨some, Option.some_injective _⟩ ⊆
      (rightSet g).image (alphaR jp kp r) := by
    intro o ho
    simp only [Finset.mem_map, rightSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk] at ho
    obtain ⟨z, ⟨y, hy⟩, rfl⟩ := ho
    rw [TG_apply] at hy
    obtain ⟨c, d, h1, -, h3⟩ := hy
    simp only [Finset.mem_image, rightSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨d, ⟨c, h1⟩, h3⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_map] at this
  exact this.trans Finset.card_image_le

lemma bisp_of_TG {g : Gr} {jp kp l r : Bool} (h : bisp (TG g jp kp l r) = true) : bisp g = true := by
  simp only [bisp, decide_eq_true_eq] at h ⊢
  exact ⟨h.1.trans (leftSet_TG_le g jp kp l r), h.2.trans (rightSet_TG_le g jp kp l r)⟩

lemma two_left {g : Gr} (h : 2 ≤ (leftSet g).card) :
    ∃ y1 z1 y2 z2, g y1 z1 = true ∧ g y2 z2 = true ∧ y1 ≠ y2 := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (leftSet g).card)
  simp only [leftSet, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  obtain ⟨z1, h1⟩ := ha; obtain ⟨z2, h2⟩ := hb
  exact ⟨a, z1, b, z2, h1, h2, hab⟩

lemma two_right {g : Gr} (h : 2 ≤ (rightSet g).card) :
    ∃ y1 z1 y2 z2, g y1 z1 = true ∧ g y2 z2 = true ∧ z1 ≠ z2 := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (rightSet g).card)
  simp only [rightSet, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  obtain ⟨y1, h1⟩ := ha; obtain ⟨y2, h2⟩ := hb
  exact ⟨y1, a, y2, b, h1, h2, hab⟩

lemma length_le_sigma (j k : ℕ) (v : Word) : v.length ≤ (sigma j k v).length := by
  induction v with
  | nil => simp [sigma]
  | cons c v ih => rw [sigma_cons]; simp; omega

lemma child_length (j k : ℕ) (l r : Bool) (v : Word) : v.length < (child j k l r v).length := by
  rw [child_eq]; have := length_le_sigma j k v; simp; omega

lemma two_mem_child (j k : ℕ) (l r : Bool) (v : Word) : (2 : Letter) ∈ child j k l r v := by
  rw [child_eq]; simp

/-- Every bispecial factor containing 3 is a child of a bispecial antecedent. -/
theorem bisp_parse {L : Word → Prop} (hL : Good L) (j k : ℕ) (w : Word) (h2 : (2 : Letter) ∈ w)
    (hb : bisp (edges (imageLanguage L j k) w) = true) :
    ∃ v l r, (l = true → 0 < k) ∧ (r = true → 0 < j ∨ 0 < k) ∧ w = child j k l r v ∧
      bisp (edges L v) = true ∧ v.length < w.length ∧
      edges (imageLanguage L j k) w = TG (edges L v) (decide (j ≠ 0)) (decide (k ≠ 0)) l r := by
  have hb' := hb
  simp only [bisp, decide_eq_true_eq] at hb'
  obtain ⟨y1, z1, y2, z2, e1, e2, hy⟩ := two_left hb'.1
  obtain ⟨y1', z1', y2', z2', f1, f2, hz⟩ := two_right hb'.2
  rw [edges_apply] at e1 e2 f1 f2
  obtain ⟨v, l, r, hl, hr, rfl⟩ := special_parse L hL.fac hL.left j k w h2
    ⟨y1, z1, y2, z2, e1, e2, hy⟩ ⟨y1', z1', y2', z2', f1, f2, hz⟩
  have he := child_edges hL j k l r hl hr v
  refine ⟨v, l, r, hl, hr, rfl, ?_, child_length j k l r v, he⟩
  rw [he] at hb; exact bisp_of_TG hb

/-- Children with valid choices are distinct. -/
theorem child_inj {j k : ℕ} {l r l' r' : Bool} {v v' : Word} (hl : l = true → 0 < k)
    (hr : r = true → 0 < j ∨ 0 < k) (hl' : l' = true → 0 < k) (hr' : r' = true → 0 < j ∨ 0 < k)
    (h : child j k l r v = child j k l' r' v') : l = l' ∧ r = r' ∧ v = v' := by
  rw [child_eq, child_eq] at h
  obtain ⟨h1, h2, h3⟩ := parse_unique (two_not_mem_leftCore j k l) (two_not_mem_rightAffix j k r)
    (two_not_mem_leftCore j k l') (two_not_mem_rightAffix j k r') h
  refine ⟨?_, ?_, h2⟩
  · have := congrArg List.length h1
    cases l <;> cases l' <;> simp [leftCore, run] at this ⊢
    · have := hl' rfl; omega
    · have := hl rfl; omega
  · cases r <;> cases r'
    · rfl
    · exfalso; have := hr' rfl; by_cases hk : k = 0 <;> simp [rightAffix, hk, run] at h3 <;> omega
    · exfalso; have := hr rfl; by_cases hk : k = 0 <;> simp [rightAffix, hk, run] at h3 <;> omega
    · rfl

#print axioms bisp_parse
#print axioms child_inj
end Trip
```

### `TripDirective.lean`

```lean
import TripStep

/-! Languages of double-Gauss directives g : ℕ → ℕ × ℕ. Level i is the image of
level i+1; when g is eventually (1,1) (τ = σ_{1,1}) every level is factorial,
two-sided extendable and contains every letter. -/

set_option linter.unusedSimpArgs false

namespace Trip

def Phi (g : ℕ → ℕ × ℕ) : ℕ → ℕ → Word → Word
  | _, 0, u => u
  | i, N + 1, u => sigma (g i).1 (g i).2 (Phi g (i + 1) N u)

/-- The language of the shifted double-Gauss directive (g i, g (i+1), ...). -/
def Lang (g : ℕ → ℕ × ℕ) (i : ℕ) (w : Word) : Prop := ∃ (N : ℕ) (c : Letter), w <:+: Phi g i N [c]

lemma sigma_append' (j k : ℕ) (u v : Word) : sigma j k (u ++ v) = sigma j k u ++ sigma j k v := by
  simp [sigma]

lemma sigma_infix {j k : ℕ} {u v : Word} (h : u <:+: v) : sigma j k u <:+: sigma j k v := by
  obtain ⟨a, b, rfl⟩ := h
  exact ⟨sigma j k a, sigma j k b, by simp [sigma_append']⟩

lemma Phi_append (g : ℕ → ℕ × ℕ) : ∀ (N i : ℕ) (u v : Word),
    Phi g i N (u ++ v) = Phi g i N u ++ Phi g i N v
  | 0, _, _, _ => rfl
  | N + 1, i, u, v => by simp [Phi, Phi_append g N (i + 1), sigma_append']

lemma Phi_infix (g : ℕ → ℕ × ℕ) (N i : ℕ) {u v : Word} (h : u <:+: v) :
    Phi g i N u <:+: Phi g i N v := by
  obtain ⟨a, b, rfl⟩ := h
  exact ⟨Phi g i N a, Phi g i N b, by simp [Phi_append]⟩

lemma Phi_succ' (g : ℕ → ℕ × ℕ) : ∀ (N i : ℕ) (u : Word),
    Phi g i (N + 1) u = Phi g i N (sigma (g (i + N)).1 (g (i + N)).2 u)
  | 0, i, u => by simp [Phi]
  | N + 1, i, u => by
    rw [Phi, Phi_succ' g N (i + 1) u, Phi, show i + 1 + N = i + (N + 1) by omega]

lemma Phi_length (g : ℕ → ℕ × ℕ) : ∀ (N i : ℕ) (u : Word), u.length ≤ (Phi g i N u).length
  | 0, _, _ => le_rfl
  | N + 1, i, u => (Phi_length g N (i + 1) u).trans (length_le_sigma _ _ _)

lemma letter_in_block (j k : ℕ) (c : Letter) : ∃ c', [c] <:+: block j k c' := by
  fin_cases c
  · exact ⟨0, [], run j 0 ++ [2], by simp [block, run, List.replicate_succ]⟩
  · exact ⟨1, [], run k 1 ++ run j 0 ++ [2], by simp [block, run, List.replicate_succ]⟩
  · exact ⟨0, run (j + 1) 0, [], by simp [block]⟩

lemma Lang_step {g : ℕ → ℕ × ℕ} {i N : ℕ} {w : Word} {c : Letter} (h : w <:+: Phi g i N [c]) :
    ∃ c', w <:+: Phi g i (N + 1) [c'] := by
  obtain ⟨c', hc'⟩ := letter_in_block (g (i + N)).1 (g (i + N)).2 c
  refine ⟨c', h.trans ?_⟩
  rw [Phi_succ']
  exact Phi_infix g N i (by rw [sigma_singleton]; exact hc')

lemma Lang_mono {g : ℕ → ℕ × ℕ} {i N N' : ℕ} (hN : N ≤ N') {w : Word} {c : Letter}
    (h : w <:+: Phi g i N [c]) : ∃ c', w <:+: Phi g i N' [c'] := by
  induction hN with
  | refl => exact ⟨c, h⟩
  | step _ ih => obtain ⟨c', h'⟩ := ih; exact Lang_step h'

theorem Lang_image (g : ℕ → ℕ × ℕ) (i : ℕ) (w : Word) :
    Lang g i w ↔ imageLanguage (Lang g (i + 1)) (g i).1 (g i).2 w := by
  constructor
  · rintro ⟨N, c, h⟩
    cases N with
    | zero =>
      obtain ⟨c', hc'⟩ := letter_in_block (g i).1 (g i).2 c
      exact ⟨[c'], ⟨0, c', List.infix_refl _⟩, h.trans (by rw [sigma_singleton]; exact hc')⟩
    | succ N => exact ⟨Phi g (i + 1) N [c], ⟨N, c, List.infix_refl _⟩, h⟩
  · rintro ⟨u, ⟨N, c, hu⟩, hw⟩
    exact ⟨N + 1, c, hw.trans (sigma_infix hu)⟩

lemma tau2 (c : Letter) : ∃ P Q : Word, P ≠ [] ∧ Q ≠ [] ∧
    sigma 1 1 (sigma 1 1 [0]) = P ++ [c] ++ Q := by
  fin_cases c
  · exact ⟨[0], [2, 0, 0, 2, 1, 0, 2], by simp, by simp, by decide⟩
  · exact ⟨[0, 0, 2, 0, 0, 2], [0, 2], by simp, by simp, by decide⟩
  · exact ⟨[0, 0], [0, 0, 2, 1, 0, 2], by simp, by simp, by decide⟩

lemma interior_ext {X Y A B : Word} (hX : X <:+: Y) (hA : A ≠ []) (hB : B ≠ []) :
    (∃ a : Letter, a :: X <:+: A ++ Y ++ B) ∧ (∃ b : Letter, X ++ [b] <:+: A ++ Y ++ B) := by
  obtain ⟨s, t, rfl⟩ := hX
  obtain ⟨A', a, hAs⟩ := exists_concat (u := A ++ s) (by simp [hA])
  obtain ⟨b, B', hB'⟩ : ∃ b B', t ++ B = b :: B' := by
    cases ht : t ++ B with
    | nil => simp [hB] at ht
    | cons b B' => exact ⟨b, B', rfl⟩
  refine ⟨⟨a, A', t ++ B, ?_⟩, ⟨b, A ++ s, B', ?_⟩⟩
  · have : A ++ (s ++ X ++ t) ++ B = (A ++ s) ++ X ++ (t ++ B) := by simp
    rw [this, hAs]; simp
  · have : A ++ (s ++ X ++ t) ++ B = (A ++ s) ++ X ++ (t ++ B) := by simp
    rw [this, hB']; simp

theorem Lang_good (g : ℕ → ℕ × ℕ) (i0 : ℕ) (hg : ∀ i, i0 ≤ i → g i = (1, 1)) (i : ℕ) :
    Good (Lang g i) := by
  have ext : ∀ w, Lang g i w → (∃ a, Lang g i (a :: w)) ∧ (∃ b, Lang g i (w ++ [b])) := by
    rintro w ⟨N, c, h⟩
    obtain ⟨c', h'⟩ := Lang_mono (N' := N + i0) (by omega) h
    obtain ⟨P, Q, hP, hQ, hPQ⟩ := tau2 c'
    have e : Phi g i (N + i0 + 2) [0] =
        Phi g i (N + i0) P ++ Phi g i (N + i0) [c'] ++ Phi g i (N + i0) Q := by
      rw [show N + i0 + 2 = (N + i0 + 1) + 1 by omega, Phi_succ', Phi_succ',
        hg (i + (N + i0 + 1)) (by omega), hg (i + (N + i0)) (by omega)]
      rw [hPQ, Phi_append, Phi_append]
    have hP' : Phi g i (N + i0) P ≠ [] := by
      intro h0; have := Phi_length g (N + i0) i P; rw [h0] at this
      exact hP (List.eq_nil_of_length_eq_zero (by simpa using this))
    have hQ' : Phi g i (N + i0) Q ≠ [] := by
      intro h0; have := Phi_length g (N + i0) i Q; rw [h0] at this
      exact hQ (List.eq_nil_of_length_eq_zero (by simpa using this))
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := interior_ext h' hP' hQ'
    exact ⟨⟨a, _, 0, by rw [e]; exact ha⟩, ⟨b, _, 0, by rw [e]; exact hb⟩⟩
  exact { fac := fun u v hu hv => by obtain ⟨N, c, h⟩ := hu; exact ⟨N, c, hv.trans h⟩
          left := fun w hw => (ext w hw).1
          right := fun w hw => (ext w hw).2
          letters := fun c => ⟨0, c, List.infix_refl _⟩ }

#print axioms Lang_image
#print axioms Lang_good
end Trip
```

### `TripForest.lean`

```lean
import TripDirective
import TripMatchForest

/-! The word forest: actual bispecial factors produced by the same recursion as
the abstract forest. It is duplicate-free, consists of bispecial factors with
their true types and Parikh vectors, and contains every bispecial factor of
length at most its depth. -/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

namespace Trip
open TripPairCones

noncomputable def tyOf (L : Word → Prop) (w : Word) : ℕ := enc (edges L w)
noncomputable def nodeOf (L : Word → Prop) (w : Word) : Node := (tyOf L w, νw w)

noncomputable def childrenW (g : ℕ → ℕ × ℕ) (i : ℕ) (v : Word) : List Word :=
  (childTab (tyOf (Lang g (i + 1)) v) (decide ((g i).1 ≠ 0)) (decide ((g i).2 ≠ 0))).map
    fun e => child (g i).1 (g i).2 e.2.1 e.2.2 v

noncomputable def forestW (g : ℕ → ℕ × ℕ) : ℕ → ℕ → List Word
  | i, 0 => (seedList (g i).1 (g i).2).map Prod.fst
  | i, D + 1 => (seedList (g i).1 (g i).2).map Prod.fst ++
      (forestW g (i + 1) D).flatMap (childrenW g i)

/-! Finite facts. -/

set_option maxRecDepth 100000 in
lemma states_facts : ∀ t ∈ states,
    bisp (toG t) = true ∧ enc (toG t) = t ∧ multG (toG t) = mval t := by decide

lemma states_fact {t : ℕ} (ht : t ∈ states) :
    bisp (toG t) = true ∧ enc (toG t) = t ∧ multG (toG t) = mval t := states_facts t ht

set_option maxRecDepth 10000 in
lemma valid_tab : (states.all fun t => [false, true].all fun jp => [false, true].all fun kp =>
    (childTab t jp kp).all fun e => (!e.2.1 || kp) && (!e.2.2 || jp || kp) &&
      states.contains e.1) = true := by decide

set_option maxRecDepth 10000 in
lemma nodup_tab : (states.all fun t => [false, true].all fun jp => [false, true].all fun kp =>
    decide ((childTab t jp kp).map Prod.snd).Nodup) = true := by decide

lemma tab_entry {t : ℕ} (ht : t ∈ states) (jp kp : Bool) {e : ℕ × Bool × Bool}
    (he : e ∈ childTab t jp kp) :
    TG (toG t) jp kp e.2.1 e.2.2 = toG e.1 ∧ e.1 ∈ states ∧ (e.2.1 = true → kp = true) ∧
      (e.2.2 = true → jp = true ∨ kp = true) := by
  have hv := List.all_eq_true.mp valid_tab t ht
  have hv := List.all_eq_true.mp hv jp (bool_mem _)
  have hv := List.all_eq_true.mp hv kp (bool_mem _)
  have hv := List.all_eq_true.mp hv e he
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hv
  obtain ⟨⟨h1, h2⟩, h3⟩ := hv
  have hc := List.all_eq_true.mp childTab_check t ht
  have hc := List.all_eq_true.mp hc jp (bool_mem _)
  have hc := List.all_eq_true.mp hc kp (bool_mem _)
  simp only [beq_iff_eq] at hc
  rw [hc] at he
  simp only [computedChildren, List.mem_filterMap, Option.map_eq_some_iff] at he
  obtain ⟨p, -, t', hco, rfl⟩ := he
  have hk := List.all_eq_true.mp child_types_check t ht
  have hk := List.all_eq_true.mp hk jp (bool_mem _)
  have hk := List.all_eq_true.mp hk kp (bool_mem _)
  have hk := List.all_eq_true.mp hk p (by rcases p with ⟨_ | _, _ | _⟩ <;> simp [lrChoices])
  rw [hco] at hk
  simp only [Bool.and_eq_true] at hk
  refine ⟨eqG_spec hk.1, List.contains_iff_mem.mp h3, ?_, ?_⟩
  · intro hl; rcases h1 with h1 | h1
    · rw [h1] at hl; exact absurd hl (by simp)
    · exact h1
  · intro hr; rcases h2 with (h2 | h2) | h2
    · rw [h2] at hr; exact absurd hr (by simp)
    · exact Or.inl h2
    · exact Or.inr h2

lemma tab_complete {t : ℕ} (ht : t ∈ states) (jp kp l r : Bool)
    (hb : bisp (TG (toG t) jp kp l r) = true) : ∃ t', (t', l, r) ∈ childTab t jp kp := by
  have hc := List.all_eq_true.mp childTab_check t ht
  have hc := List.all_eq_true.mp hc jp (bool_mem _)
  have hc := List.all_eq_true.mp hc kp (bool_mem _)
  simp only [beq_iff_eq] at hc
  refine ⟨enc (TG (toG t) jp kp l r), ?_⟩
  rw [hc]
  simp only [computedChildren, List.mem_filterMap, Option.map_eq_some_iff]
  refine ⟨(l, r), by rcases l <;> rcases r <;> simp [lrChoices], _, ?_, rfl⟩
  simp [childOf, hb]

lemma seed_states (j k : ℕ) : ∀ p ∈ seedList j k, p.2 ∈ states := by
  intro p hp
  simp only [seedList, oneRuns, twoRuns, emptyType, List.mem_cons, List.mem_append,
    List.mem_map, List.mem_range] at hp
  rcases hp with rfl | (h | ⟨a, -, rfl⟩) | (h | ⟨b, -, rfl⟩)
  · dsimp only; split_ifs <;> simp [states]
  · split_ifs at h <;> simp at h <;> subst h <;> simp [states]
  · simp [states]
  · split_ifs at h <;> simp at h <;> subst h <;> simp [states]
  · dsimp only; split_ifs <;> simp [states]

/-! Parikh vectors. -/

lemma νw_append (u v : Word) : νw (u ++ v) = νw u + νw v := by
  simp [νw, List.count_append]

lemma νw_cons (c : Letter) (v : Word) : νw (c :: v) = νw [c] + νw v := by
  rw [← νw_append]; rfl

lemma νw_block (j k : ℕ) (c : Letter) : νw (block j k c) = M (j : ℤ) k (νw [c]) := by
  fin_cases c <;> simp [νw, block, M, run, List.count_replicate] <;> ring

lemma νw_sigma (j k : ℕ) (v : Word) : νw (sigma j k v) = M (j : ℤ) k (νw v) := by
  induction v with
  | nil => simp [sigma, νw, M]
  | cons c v ih =>
    rw [show sigma j k (c :: v) = block j k c ++ sigma j k v by simp [sigma], νw_append, ih,
      νw_block, νw_cons c v, M_add]

lemma νw_child (j k : ℕ) (l r : Bool) (v : Word) :
    νw (child j k l r v) = M (j : ℤ) k (νw v) + off j k l r := by
  rw [child, νw_append, νw_append, νw_sigma]
  have hl : νw (leftAffix j k l) = ((j : ℤ), if l = true then (k : ℤ) else 0, 1) := by
    cases l <;> simp [νw, leftAffix, affixA, affixC, run, List.count_replicate]
  have hr : νw (rightAffix j k r) =
      ((if r = true ∧ k = 0 then (j : ℤ) else 0), (if r = true ∧ k ≠ 0 then (k : ℤ) else 0), 0) := by
    cases r <;> by_cases hk : k = 0 <;> simp [νw, rightAffix, hk, run, List.count_replicate]
  rw [hl, hr]
  ext <;> simp [off] <;> ring

lemma lenV_νw (w : Word) : lenV (νw w) = (w.length : ℤ) := by
  induction w with
  | nil => simp [lenV, νw]
  | cons c w ih =>
    rw [νw_cons]; simp only [lenV, Prod.fst_add, Prod.snd_add] at ih ⊢
    fin_cases c <;> simp [νw] at ih ⊢ <;> omega

/-! The forest. -/

lemma Lang_eq (g : ℕ → ℕ × ℕ) (i : ℕ) :
    Lang g i = imageLanguage (Lang g (i + 1)) (g i).1 (g i).2 := by
  funext w; exact propext (Lang_image g i w)


section
variable (g : ℕ → ℕ × ℕ) (i0 : ℕ) (hg : ∀ i, i0 ≤ i → g i = (1, 1))
include hg

theorem forest_typed : ∀ D i, ∀ w ∈ forestW g i D,
    tyOf (Lang g i) w ∈ states ∧ edges (Lang g i) w = toG (tyOf (Lang g i) w) := by
  have seedcase : ∀ i, ∀ w ∈ (seedList (g i).1 (g i).2).map Prod.fst,
      tyOf (Lang g i) w ∈ states ∧ edges (Lang g i) w = toG (tyOf (Lang g i) w) := by
    intro i w hw
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw
    have hG := Lang_good g i0 hg (i + 1)
    have e := seeds_sound (Lang g (i + 1)) hG.left hG.letters _ _ p hp
    rw [← Lang_eq g i] at e
    have hs := seed_states _ _ p hp
    have hty : tyOf (Lang g i) p.1 = p.2 := by rw [tyOf, e, (states_fact hs).2.1]
    rw [hty]; exact ⟨hs, e⟩
  intro D
  induction D with
  | zero => exact seedcase
  | succ D ih =>
    intro i w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact seedcase i w hw
    · obtain ⟨v, hv, hw⟩ := List.mem_flatMap.mp hw
      obtain ⟨hvs, hve⟩ := ih (i + 1) v hv
      simp only [childrenW, List.mem_map] at hw
      obtain ⟨e, he, rfl⟩ := hw
      obtain ⟨hT, hs, hl, hr⟩ := tab_entry hvs _ _ he
      have hG := Lang_good g i0 hg (i + 1)
      have ce := child_edges hG (g i).1 (g i).2 e.2.1 e.2.2
        (fun h => by have := hl h; simpa [Nat.pos_iff_ne_zero] using this)
        (fun h => by have := hr h; simpa [Nat.pos_iff_ne_zero] using this) v
      rw [← Lang_eq g i, hve, hT] at ce
      have hty : tyOf (Lang g i) (child (g i).1 (g i).2 e.2.1 e.2.2 v) = e.1 := by
        rw [tyOf, ce, (states_fact hs).2.1]
      rw [hty]; exact ⟨hs, ce⟩

theorem forest_bridge : ∀ D i, (forestW g i D).map (nodeOf (Lang g i)) = forestN g i D := by
  have seedcase : ∀ i, ((seedList (g i).1 (g i).2).map Prod.fst).map (nodeOf (Lang g i)) =
      seedN (g i).1 (g i).2 := by
    intro i
    rw [List.map_map, seedN]
    apply List.map_congr_left
    intro p hp
    have hG := Lang_good g i0 hg (i + 1)
    have e := seeds_sound (Lang g (i + 1)) hG.left hG.letters _ _ p hp
    rw [← Lang_eq g i] at e
    have hty : tyOf (Lang g i) p.1 = p.2 := by
      rw [tyOf, e, (states_fact (seed_states _ _ p hp)).2.1]
    simp only [Function.comp, nodeOf, hty]
  intro D
  induction D with
  | zero => exact seedcase
  | succ D ih =>
    intro i
    rw [forestW, forestN, List.map_append, seedcase, ← ih (i + 1), List.map_flatMap,
      List.flatMap_map]
    congr 1
    apply List.flatMap_congr
    intro v hv
    obtain ⟨hvs, hve⟩ := forest_typed g i0 hg D (i + 1) v hv
    simp only [childrenW, childN, nodeOf, List.map_map]
    apply List.map_congr_left
    intro e he
    obtain ⟨hT, hs, hl, hr⟩ := tab_entry hvs _ _ he
    have hG := Lang_good g i0 hg (i + 1)
    have ce := child_edges hG (g i).1 (g i).2 e.2.1 e.2.2
      (fun h => by have := hl h; simpa [Nat.pos_iff_ne_zero] using this)
      (fun h => by have := hr h; simpa [Nat.pos_iff_ne_zero] using this) v
    rw [← Lang_eq g i, hve, hT] at ce
    have hty : tyOf (Lang g i) (child (g i).1 (g i).2 e.2.1 e.2.2 v) = e.1 := by
      rw [tyOf, ce, (states_fact hs).2.1]
    show (tyOf (Lang g i) (child (g i).1 (g i).2 e.2.1 e.2.2 v),
      νw (child (g i).1 (g i).2 e.2.1 e.2.2 v)) = _
    rw [hty, νw_child]

end

#print axioms forest_typed
#print axioms forest_bridge
end Trip
```

### `TripForest2.lean`

```lean
import TripForest

/-! The word forest is duplicate-free and complete; the weighted sum over it
is the abstract sum, hence at most 1. -/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

namespace Trip
open TripPairCones

lemma seed_free (j k : ℕ) : ∀ w ∈ (seedList j k).map Prod.fst, (2 : Letter) ∉ w := by
  intro w hw
  simp only [List.mem_map, seedList, oneRuns, twoRuns, List.mem_cons, List.mem_append,
    List.mem_range] at hw
  obtain ⟨p, hp, rfl⟩ := hw
  rcases hp with rfl | (h | ⟨a, -, rfl⟩) | (h | ⟨b, -, rfl⟩)
  · simp
  · by_cases hj : j = 0
    · simp [hj] at h
    · simp only [hj, ↓reduceIte, List.mem_singleton] at h; subst h; simp [run, List.mem_replicate]
  · simp [run, List.mem_replicate]
  · by_cases hk : k = 0
    · simp [hk] at h
    · simp only [hk, ↓reduceIte, List.mem_singleton] at h; subst h; simp [run, List.mem_replicate]
  · simp [run, List.mem_replicate]

def runIdx (j : ℕ) : List ℕ := (if j = 0 then [] else [j]) ++ (List.range (j - 1)).map (· + 1)

lemma runIdx_spec (j : ℕ) : (runIdx j).Nodup ∧ ∀ x ∈ runIdx j, 1 ≤ x := by
  unfold runIdx
  by_cases hj : j = 0
  · subst hj; simp
  · simp only [hj, ↓reduceIte, List.singleton_append, List.nodup_cons, List.mem_map,
      List.mem_range, List.mem_cons]
    refine ⟨⟨?_, List.Nodup.map (fun a b h => by simpa using h) List.nodup_range⟩, ?_⟩
    · rintro ⟨a, ha, h⟩; omega
    · rintro x (rfl | ⟨a, -, rfl⟩) <;> omega

lemma seed_nodup (j k : ℕ) : ((seedList j k).map Prod.fst).Nodup := by
  apply List.Nodup.of_map (fun w : Word => (w.count 0, w.count 1))
  have he : ((seedList j k).map Prod.fst).map (fun w : Word => (w.count 0, w.count 1)) =
      (0, 0) :: ((runIdx j).map (fun a => (a, 0)) ++ (runIdx k).map (fun b => (0, b))) := by
    by_cases hj : j = 0 <;> by_cases hk : k = 0 <;>
      simp [seedList, oneRuns, twoRuns, runIdx, hj, hk, run, List.count_replicate, Function.comp_def]
  rw [he]
  obtain ⟨n1, p1⟩ := runIdx_spec j
  obtain ⟨n2, p2⟩ := runIdx_spec k
  rw [List.nodup_cons, List.nodup_append]
  refine ⟨?_, n1.map (fun a b h => by simpa using h), n2.map (fun a b h => by simpa using h), ?_⟩
  · simp only [List.mem_append, List.mem_map, not_or, not_exists, not_and]
    refine ⟨fun a ha h => ?_, fun b hb h => ?_⟩
    · have := p1 a ha; simp at h; omega
    · have := p2 b hb; simp at h; omega
  · intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
    have := p1 a ha; simp at hxy; omega

section
variable (g : ℕ → ℕ × ℕ) (i0 : ℕ) (hg : ∀ i, i0 ≤ i → g i = (1, 1))
include hg

omit hg in
lemma valid_of_tab {i : ℕ} {v : Word} (hvs : tyOf (Lang g (i + 1)) v ∈ states) {e : ℕ × Bool × Bool}
    (he : e ∈ childTab (tyOf (Lang g (i + 1)) v) (decide ((g i).1 ≠ 0)) (decide ((g i).2 ≠ 0))) :
    (e.2.1 = true → 0 < (g i).2) ∧ (e.2.2 = true → 0 < (g i).1 ∨ 0 < (g i).2) := by
  obtain ⟨-, -, hl, hr⟩ := tab_entry hvs _ _ he
  exact ⟨fun h => by have := hl h; simpa [Nat.pos_iff_ne_zero] using this,
    fun h => by have := hr h; simpa [Nat.pos_iff_ne_zero] using this⟩

theorem forest_nodup : ∀ D i, (forestW g i D).Nodup := by
  intro D
  induction D with
  | zero => intro i; exact seed_nodup _ _
  | succ D ih =>
    intro i
    rw [forestW, List.nodup_append]
    refine ⟨seed_nodup _ _, ?_, ?_⟩
    · rw [List.nodup_flatMap]
      refine ⟨?_, ?_⟩
      · intro v hv
        have hvs := (forest_typed g i0 hg D (i + 1) v hv).1
        have hnd := List.all_eq_true.mp nodup_tab _ hvs
        have hnd := List.all_eq_true.mp hnd (decide ((g i).1 ≠ 0)) (bool_mem _)
        have hnd := List.all_eq_true.mp hnd (decide ((g i).2 ≠ 0)) (bool_mem _)
        simp only [decide_eq_true_eq] at hnd
        unfold childrenW
        have : ((childTab (tyOf (Lang g (i + 1)) v) (decide ((g i).1 ≠ 0))
            (decide ((g i).2 ≠ 0))).map fun e => child (g i).1 (g i).2 e.2.1 e.2.2 v) =
            ((childTab (tyOf (Lang g (i + 1)) v) (decide ((g i).1 ≠ 0))
              (decide ((g i).2 ≠ 0))).map Prod.snd).map fun p => child (g i).1 (g i).2 p.1 p.2 v := by
          simp [List.map_map, Function.comp]
        rw [this]
        apply List.Nodup.map_on _ hnd
        intro p hp q hq hpq
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp
        obtain ⟨e', he', rfl⟩ := List.mem_map.mp hq
        obtain ⟨h1, h2⟩ := valid_of_tab g hvs he
        obtain ⟨h1', h2'⟩ := valid_of_tab g hvs he'
        obtain ⟨a, b, -⟩ := child_inj h1 h2 h1' h2' hpq
        exact Prod.ext a b
      · apply (ih (i + 1)).pairwise_of_forall_ne
        intro v hv v' hv' hne w hw hw'
        simp only [childrenW, List.mem_map] at hw hw'
        obtain ⟨e, he, rfl⟩ := hw
        obtain ⟨e', he', hee⟩ := hw'
        obtain ⟨h1, h2⟩ := valid_of_tab g (forest_typed g i0 hg D (i + 1) v hv).1 he
        obtain ⟨h1', h2'⟩ := valid_of_tab g (forest_typed g i0 hg D (i + 1) v' hv').1 he'
        exact hne (child_inj h1 h2 h1' h2' hee.symm).2.2
    · intro a ha b hb hab
      subst hab
      obtain ⟨v, -, hb⟩ := List.mem_flatMap.mp hb
      simp only [childrenW, List.mem_map] at hb
      obtain ⟨e, -, rfl⟩ := hb
      exact seed_free _ _ _ ha (two_mem_child _ _ _ _ _)

theorem forest_complete : ∀ D i (w : Word), bisp (edges (Lang g i) w) = true →
    w.length ≤ D → w ∈ forestW g i D := by
  intro D
  induction D with
  | zero =>
    intro i w _ hl
    have : w = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp [forestW, seedList]
  | succ D ih =>
    intro i w hb hl
    have hG := Lang_good g i0 hg (i + 1)
    rw [Lang_eq g i] at hb
    by_cases h2 : (2 : Letter) ∈ w
    · obtain ⟨v, l, r, hl', hr', rfl, hbv, hlen, he⟩ := bisp_parse hG _ _ w h2 hb
      have hv := ih (i + 1) v hbv (by omega)
      obtain ⟨hvs, hve⟩ := forest_typed g i0 hg D (i + 1) v hv
      rw [hve] at he
      rw [he] at hb
      obtain ⟨t', ht'⟩ := tab_complete hvs _ _ l r hb
      rw [forestW]
      apply List.mem_append_right
      exact List.mem_flatMap.mpr ⟨v, hv, List.mem_map.mpr ⟨(t', l, r), ht', rfl⟩⟩
    · obtain ⟨t, ht⟩ := seeds_complete (Lang g (i + 1)) hG.left hG.letters _ _ w h2 hb
      rw [forestW]
      exact List.mem_append_left _ (List.mem_map.mpr ⟨(w, t), ht, rfl⟩)

/-- Σ over the word forest of m(w) for |w| < n is at most 1. -/
theorem forest_sum (D : ℕ) (n : ℕ) :
    ((forestW g 0 D).map fun w => if w.length < n then multG (edges (Lang g 0) w) else 0).sum ≤ 1 := by
  have hb := forest_bound g D 0 (n : ℤ)
  rw [← forest_bridge g i0 hg D 0, List.map_map] at hb
  convert hb using 2
  apply List.map_congr_left
  intro w hw
  obtain ⟨hs, he⟩ := forest_typed g i0 hg D 0 w hw
  simp only [Function.comp, wt, nodeOf, lenV_νw, Nat.cast_lt, he, (states_fact hs).2.2]

end

#print axioms forest_nodup
#print axioms forest_complete
#print axioms forest_sum
end Trip
```

### `TripCount.lean`

```lean
import TripStep
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Extension counting: for a factorial, two-sided extendable language,
p(n+2) − 2p(n+1) + p(n) = Σ_{|w| = n} m(w), and its telescoped form. -/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace Trip

open Classical

def allWords : ℕ → Finset Word
  | 0 => {[]}
  | n + 1 => (Finset.univ ×ˢ allWords n).image fun p => p.1 :: p.2

lemma mem_allWords : ∀ {n : ℕ} {w : Word}, w ∈ allWords n ↔ w.length = n
  | 0, w => by cases w <;> simp [allWords]
  | n + 1, w => by
    cases w with
    | nil => simp [allWords]
    | cons a w => simp [allWords, mem_allWords]

noncomputable def S (L : Word → Prop) (n : ℕ) : Finset Word := (allWords n).filter L

lemma mem_S {L : Word → Prop} {n : ℕ} {w : Word} : w ∈ S L n ↔ w.length = n ∧ L w := by
  simp [S, mem_allWords]

lemma complexity_eq (L : Word → Prop) (n : ℕ) : complexity L n = (S L n).card := by
  unfold complexity
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun w => mem_S.symm)

section
variable {L : Word → Prop} (hL : Good L)
include hL

lemma mem_of_edge {w : Word} {a b : Letter} (h : extensionEdge L w a b) : L w :=
  hL.fac _ _ h ⟨[a], [b], by simp⟩

lemma card_left (n : ℕ) : (S L (n + 1)).card = ∑ w ∈ S L n, (leftSet (edges L w)).card := by
  have e : S L (n + 1) = (S L n).biUnion fun w => (leftSet (edges L w)).image fun a => a :: w := by
    ext u
    simp only [mem_S, Finset.mem_biUnion, Finset.mem_image, leftSet, Finset.mem_filter,
      Finset.mem_univ, true_and, edges_apply]
    constructor
    · rintro ⟨hl, hu⟩
      cases u with
      | nil => simp at hl
      | cons a w =>
        obtain ⟨b, hb⟩ := hL.right _ hu
        refine ⟨w, ⟨by simpa using hl, hL.fac _ _ hu ⟨[a], [], by simp⟩⟩, a, ⟨b, by simpa [extensionEdge] using hb⟩, rfl⟩
    · rintro ⟨w, ⟨hl, -⟩, a, ⟨b, hb⟩, rfl⟩
      exact ⟨by simp [hl], hL.fac _ _ hb ⟨[], [b], by simp [extensionEdge]⟩⟩
  rw [e, Finset.card_biUnion]
  · apply Finset.sum_congr rfl; intro w _
    exact Finset.card_image_of_injective _ (fun a b h => by simpa using h)
  · intro w _ w' _ hne
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_image]
    rintro u ⟨a, -, rfl⟩ ⟨b, -, h⟩
    exact hne (List.cons.inj h).2.symm

lemma card_right (n : ℕ) : (S L (n + 1)).card = ∑ w ∈ S L n, (rightSet (edges L w)).card := by
  have e : S L (n + 1) = (S L n).biUnion fun w => (rightSet (edges L w)).image fun b => w ++ [b] := by
    ext u
    simp only [mem_S, Finset.mem_biUnion, Finset.mem_image, rightSet, Finset.mem_filter,
      Finset.mem_univ, true_and, edges_apply]
    constructor
    · rintro ⟨hl, hu⟩
      obtain ⟨w, b, rfl⟩ := exists_concat (u := u) (by rintro rfl; simp at hl)
      obtain ⟨a, ha⟩ := hL.left _ hu
      refine ⟨w, ⟨by simpa using hl, hL.fac _ _ hu ⟨[], [b], by simp⟩⟩, b, ⟨a, by simpa [extensionEdge] using ha⟩, rfl⟩
    · rintro ⟨w, ⟨hl, -⟩, b, ⟨a, ha⟩, rfl⟩
      exact ⟨by simp [hl], hL.fac _ _ ha ⟨[a], [], by simp [extensionEdge]⟩⟩
  rw [e, Finset.card_biUnion]
  · apply Finset.sum_congr rfl; intro w _
    exact Finset.card_image_of_injective _ (fun a b h => by
      beta_reduce at h; have := List.append_cancel_left h; simpa using this)
  · intro w _ w' _ hne
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_image]
    rintro u ⟨a, -, rfl⟩ ⟨b, -, h⟩
    exact hne (List.append_inj' h rfl).1.symm

lemma card_two (n : ℕ) : (S L (n + 2)).card = ∑ w ∈ S L n, (edgeSet (edges L w)).card := by
  have e : S L (n + 2) = (S L n).biUnion fun w =>
      (edgeSet (edges L w)).image fun p => p.1 :: (w ++ [p.2]) := by
    ext u
    simp only [mem_S, Finset.mem_biUnion, Finset.mem_image, edgeSet, Finset.mem_filter,
      Finset.mem_univ, true_and, edges_apply]
    constructor
    · rintro ⟨hl, hu⟩
      cases u with
      | nil => simp at hl
      | cons a v =>
        obtain ⟨w, b, rfl⟩ := exists_concat (u := v) (by rintro rfl; simp at hl)
        refine ⟨w, ⟨by simp at hl; omega, hL.fac _ _ hu ⟨[a], [b], by simp⟩⟩, (a, b),
          by simpa [extensionEdge] using hu, rfl⟩
    · rintro ⟨w, ⟨hl, -⟩, p, hp, rfl⟩
      exact ⟨by simp [hl], by simpa [extensionEdge] using hp⟩
  rw [e, Finset.card_biUnion]
  · apply Finset.sum_congr rfl; intro w _
    exact Finset.card_image_of_injective _ (fun p q h => by
      beta_reduce at h
      obtain ⟨h1, h2⟩ := List.cons.inj h
      have := List.append_cancel_left h2
      simp at this
      exact Prod.ext h1 this)
  · intro w _ w' _ hne
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_image]
    rintro u ⟨a, -, rfl⟩ ⟨b, -, h⟩
    simp only [List.cons.injEq] at h
    exact hne (List.append_inj' h.2 rfl).1.symm

/-- The second-difference identity. -/
theorem second_difference (n : ℕ) :
    ((S L (n + 2)).card : ℤ) - 2 * (S L (n + 1)).card + (S L n).card =
      ∑ w ∈ S L n, multG (edges L w) := by
  have h1 := card_left hL n
  have h2 := card_right hL n
  have h3 := card_two hL n
  have e1 : ((S L (n + 1)).card : ℤ) = ∑ w ∈ S L n, ((leftSet (edges L w)).card : ℤ) := by
    rw [h1]; push_cast; rfl
  have e2 : ((S L (n + 1)).card : ℤ) = ∑ w ∈ S L n, ((rightSet (edges L w)).card : ℤ) := by
    rw [h2]; push_cast; rfl
  have e3 : ((S L (n + 2)).card : ℤ) = ∑ w ∈ S L n, ((edgeSet (edges L w)).card : ℤ) := by
    rw [h3]; push_cast; rfl
  simp only [multG, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    nsmul_eq_mul, mul_one]
  linarith

lemma S_zero : (S L 0).card = 1 := by
  have : S L 0 = {[]} := by
    ext w; simp only [mem_S, Finset.mem_singleton]
    constructor
    · rintro ⟨h, -⟩; exact List.eq_nil_of_length_eq_zero h
    · rintro rfl; exact ⟨rfl, hL.fac _ _ (hL.letters 0) (List.nil_infix)⟩
  rw [this]; rfl

lemma S_one : (S L 1).card = 3 := by
  have : S L 1 = allWords 1 := by
    ext w; simp only [mem_S, mem_allWords]
    constructor
    · exact fun h => h.1
    · intro h; obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp h; exact ⟨rfl, hL.letters c⟩
  rw [this]; decide

/-- Telescoped form: p(n+1) − p(n) = 2 + Σ_{|w| < n} m(w). -/
theorem first_difference (n : ℕ) :
    ((S L (n + 1)).card : ℤ) - (S L n).card =
      2 + ∑ i ∈ Finset.range n, ∑ w ∈ S L i, multG (edges L w) := by
  induction n with
  | zero => simp [S_zero hL, S_one hL]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← second_difference hL n]
    linarith

/-- A word of the language that is not bispecial has multiplicity zero. -/
lemma mult_zero_of_not_bisp {w : Word} (hw : L w) (hb : bisp (edges L w) = false) :
    multG (edges L w) = 0 := by
  obtain ⟨b, hb'⟩ := hL.right _ hw
  obtain ⟨a, ha⟩ := hL.left _ hb'
  have he : edges L w a b = true := by
    rw [edges_apply]; simpa [extensionEdge] using ha
  have hl : 1 ≤ (leftSet (edges L w)).card :=
    Finset.card_pos.mpr ⟨a, by simp [leftSet]; exact ⟨b, he⟩⟩
  have hr : 1 ≤ (rightSet (edges L w)).card :=
    Finset.card_pos.mpr ⟨b, by simp [rightSet]; exact ⟨a, he⟩⟩
  simp only [bisp, decide_eq_false_iff_not, not_and, not_le] at hb
  set g := edges L w
  by_cases h1 : (leftSet g).card ≤ 1
  · obtain ⟨a0, ha0⟩ := Finset.card_eq_one.mp (by omega : (leftSet g).card = 1)
    have key : ∀ y z, g y z = true → y = a0 := by
      intro y z h
      have hy : y ∈ leftSet g := by
        simp only [leftSet, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨z, h⟩
      rw [ha0] at hy; simpa using hy
    have : edgeSet g = {a0} ×ˢ rightSet g := by
      ext ⟨y, z⟩
      simp only [edgeSet, rightSet, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_product, Finset.mem_singleton]
      constructor
      · intro h; exact ⟨key y z h, y, h⟩
      · rintro ⟨rfl, y', h⟩; have := key y' z h; subst this; exact h
    simp only [multG, this, Finset.card_product, ha0, Finset.card_singleton, one_mul]; ring
  · have h2 : (rightSet g).card ≤ 1 := by have := hb (by omega); omega
    obtain ⟨z0, hz0⟩ := Finset.card_eq_one.mp (by omega : (rightSet g).card = 1)
    have key : ∀ y z, g y z = true → z = z0 := by
      intro y z h
      have hz : z ∈ rightSet g := by
        simp only [rightSet, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨y, h⟩
      rw [hz0] at hz; simpa using hz
    have : edgeSet g = leftSet g ×ˢ {z0} := by
      ext ⟨y, z⟩
      simp only [edgeSet, leftSet, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_product, Finset.mem_singleton]
      constructor
      · intro h; exact ⟨⟨z, h⟩, key y z h⟩
      · rintro ⟨⟨z', h⟩, rfl⟩; have := key y z' h; subst this; exact h
    simp only [multG, this, Finset.card_product, hz0, Finset.card_singleton, mul_one]; ring

end

end Trip

#print axioms Trip.first_difference
#print axioms Trip.mult_zero_of_not_bisp
```

### `TripMain.lean`

```lean
import TripForest2
import TripCount
import TripReduction

/-! The complexity bound for eventually-τ double-Gauss directives, the
regrouping of an arbitrary finite Farey prefix into double-Gauss blocks, and
the endpoint: Conjecture 53 of Garrity–Osterman (MathDB 365088). -/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace Trip

open Classical

section
variable (g : ℕ → ℕ × ℕ) (i0 : ℕ) (hg : ∀ i, i0 ≤ i → g i = (1, 1))
include hg

/-- Σ_{|w| < n} m(w) ≤ 1 in the language of an eventually-τ directive. -/
theorem bispecial_sum_le (n : ℕ) :
    ∑ i ∈ Finset.range n, ∑ w ∈ S (Lang g 0) i, multG (edges (Lang g 0) w) ≤ 1 := by
  have hL := Lang_good g i0 hg 0
  set L := Lang g 0
  set f : Word → ℤ := fun w => multG (edges L w)
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range n)) (S L) := by
    intro a _ b _ hab
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro w h1 h2
    exact hab ((mem_S.mp h1).1.symm.trans (mem_S.mp h2).1)
  rw [← Finset.sum_biUnion hdisj]
  rw [← Finset.sum_filter_of_ne (p := fun w => bisp (edges L w) = true)]
  · have hset : ((Finset.range n).biUnion (S L)).filter (fun w => bisp (edges L w) = true) =
        (forestW g 0 n).toFinset.filter (fun w => w.length < n) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range, List.mem_toFinset, mem_S]
      constructor
      · rintro ⟨⟨i, hi, rfl, -⟩, hb⟩
        exact ⟨forest_complete g i0 hg w.length 0 w hb le_rfl |> fun h => by
          exact forest_complete g i0 hg n 0 w hb (by omega), hi⟩
      · rintro ⟨hw, hl⟩
        obtain ⟨hs, he⟩ := forest_typed g i0 hg n 0 w hw
        have hb : bisp (edges L w) = true := by rw [he]; exact (states_fact hs).1
        obtain ⟨y, z, e⟩ := exists_edge_of_bisp hb
        rw [edges_apply] at e
        exact ⟨⟨w.length, hl, rfl, mem_of_edge hL e⟩, hb⟩
    rw [hset, Finset.sum_filter, List.sum_toFinset _ (forest_nodup g i0 hg n 0)]
    exact forest_sum g i0 hg n n
  · intro w hw hne
    by_contra hb
    have hwL : L w := by
      obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hw
      exact (mem_S.mp hi).2
    exact hne (mult_zero_of_not_bisp hL hwL (by simpa using hb))

theorem eventually_tau_bound (n : ℕ) (hn : 1 ≤ n) : complexity (Lang g 0) n ≤ 3 * n := by
  have hL := Lang_good g i0 hg 0
  rw [complexity_eq]
  apply linear_bound_of_first_difference (fun n => (S (Lang g 0) n).card)
  · simp [S_one hL]
  · intro m _
    have h1 := first_difference hL m
    have h2 := bispecial_sum_le g i0 hg m
    omega
  · exact hn

end

/-! Regrouping a finite Farey prefix into double-Gauss blocks. -/

def applyB : List Bool → Word → Word
  | [], w => w
  | b :: bs, w => subst b (applyB bs w)

lemma applyB_append : ∀ (bs cs : List Bool) (w : Word),
    applyB (bs ++ cs) w = applyB bs (applyB cs w)
  | [], _, _ => rfl
  | b :: bs, cs, w => by simp [applyB, applyB_append bs cs w]

lemma applyB_morph : ∀ (bs : List Bool) (u v : Word),
    applyB bs (u ++ v) = applyB bs u ++ applyB bs v
  | [], _, _ => rfl
  | b :: bs, u, v => by simp [applyB, applyB_morph bs u v]

lemma applyB_infix (bs : List Bool) {u v : Word} (h : u <:+: v) : applyB bs u <:+: applyB bs v := by
  obtain ⟨a, b, rfl⟩ := h
  exact ⟨applyB bs a, applyB bs b, by simp [applyB_morph]⟩

lemma prefImage_eq (d : ℕ → Bool) : ∀ (r : ℕ) (w : Word),
    prefImage d r w = applyB ((List.range r).map d) w
  | 0, w => rfl
  | r + 1, w => by
    rw [prefImage, prefImage_eq d r, List.range_succ, List.map_append, applyB_append]
    rfl

lemma subst_infix (b : Bool) {u v : Word} (h : u <:+: v) : subst b u <:+: subst b v := by
  obtain ⟨a, c, rfl⟩ := h
  exact ⟨subst b a, subst b c, by simp⟩

def gaussSplit : List Bool → List ℕ
  | [] => [0]
  | false :: t => 0 :: gaussSplit t
  | true :: t => match gaussSplit t with
    | [] => [1]
    | k :: ks => (k + 1) :: ks

def gaussApply : List ℕ → Word → Word
  | [], w => w
  | k :: ks, w => gauss k (gaussApply ks w)

lemma gaussApply_append : ∀ (a b : List ℕ) (w : Word),
    gaussApply (a ++ b) w = gaussApply a (gaussApply b w)
  | [], _, _ => rfl
  | k :: ks, b, w => by simp [gaussApply, gaussApply_append ks b w]

lemma gaussSplit_ne : ∀ bs : List Bool, gaussSplit bs ≠ []
  | [] => by simp [gaussSplit]
  | false :: t => by simp [gaussSplit]
  | true :: t => by
    simp only [gaussSplit]
    split <;> simp

lemma gaussSplit_spec : ∀ (bs : List Bool) (w : Word),
    applyB (bs ++ [false]) w = gaussApply (gaussSplit bs) w
  | [], w => by simp [applyB, gaussSplit, gaussApply, gauss, s1Power]
  | false :: t, w => by
    simp [applyB, gaussSplit, gaussApply, gauss, s1Power, gaussSplit_spec t w]
  | true :: t, w => by
    have h := gaussSplit_spec t w
    obtain ⟨k, ks, hk⟩ : ∃ k ks, gaussSplit t = k :: ks := by
      cases hh : gaussSplit t with
      | nil => exact absurd hh (gaussSplit_ne t)
      | cons k ks => exact ⟨k, ks, rfl⟩
    have e : gaussSplit (true :: t) = (k + 1) :: ks := by simp [gaussSplit, hk]
    simp only [List.cons_append, applyB, h, e, hk, gaussApply, gauss, s1Power]

lemma gauss_gauss (j k : ℕ) : ∀ w : Word, gauss j (gauss k w) = sigma j k w
  | [] => by simp [gauss, subst, sigma]
  | c :: w => by
    rw [show c :: w = [c] ++ w from rfl, gauss_append, gauss_append, double_gauss_letter,
      gauss_gauss j k w]
    simp [sigma]

def pairUp : List ℕ → List (ℕ × ℕ)
  | [] => []
  | [a] => [(a, 0)]
  | a :: b :: t => (a, b) :: pairUp t

def sigmaApply : List (ℕ × ℕ) → Word → Word
  | [], w => w
  | p :: ps, w => sigma p.1 p.2 (sigmaApply ps w)

lemma pairUp_spec : ∀ (ks : List ℕ) (w : Word),
    sigmaApply (pairUp ks) w = gaussApply ks (if ks.length % 2 = 1 then gauss 0 w else w)
  | [], w => by simp [pairUp, sigmaApply, gaussApply]
  | [a], w => by simp [pairUp, sigmaApply, gaussApply, gauss_gauss]
  | a :: b :: t, w => by
    simp only [pairUp, sigmaApply, gaussApply, pairUp_spec t w, gauss_gauss, List.length_cons]
    congr 2
    simp only [show (t.length + 1 + 1) % 2 = t.length % 2 by omega]

lemma Phi_sigmaApply (g : ℕ → ℕ × ℕ) : ∀ (ps : List (ℕ × ℕ)) (i : ℕ),
    (∀ m (h : m < ps.length), g (i + m) = ps[m]) → ∀ w, Phi g i ps.length w = sigmaApply ps w
  | [], _, _, _ => rfl
  | p :: ps, i, h, w => by
    have h0 := h 0 (by simp)
    simp only [List.getElem_cons_zero, add_zero] at h0
    have ih := Phi_sigmaApply g ps (i + 1) (fun m hm => by
      have := h (m + 1) (by simp; omega)
      simpa [show i + (m + 1) = i + 1 + m by omega] using this) w
    simp only [List.length_cons, Phi, sigmaApply, ih, h0]

/-- Every finite literal prefix language embeds into the language of an
eventually-τ double-Gauss directive. -/
theorem prefix_embeds (d : ℕ → Bool) (r : ℕ) : ∃ (g : ℕ → ℕ × ℕ) (i0 : ℕ),
    (∀ i, i0 ≤ i → g i = (1, 1)) ∧ ∀ w, prefixLanguage d r w → Lang g 0 w := by
  set bs := (List.range r).map d
  set ks := gaussSplit bs
  set ps := pairUp ks
  refine ⟨fun i => ps.getD i (1, 1), ps.length, ?_, ?_⟩
  · intro i hi; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  · rintro w ⟨c, hc⟩
    rw [prefImage_eq] at hc
    -- the letter c occurs in an S0 image (once or twice)
    have hocc : ∃ c'', [c] <:+: subst false (if ks.length % 2 = 1 then gauss 0 [c''] else [c'']) := by
      by_cases hodd : ks.length % 2 = 1
      · obtain ⟨c1, h1⟩ := letter_occurs false c
        obtain ⟨c2, h2⟩ := letter_occurs false c1
        refine ⟨c2, ?_⟩
        simp only [hodd, ↓reduceIte]
        have : gauss 0 [c2] = subst false [c2] := by simp [gauss, s1Power]
        rw [this]
        exact h1.trans (subst_infix false h2)
      · obtain ⟨c1, h1⟩ := letter_occurs false c
        exact ⟨c1, by simp only [hodd, ↓reduceIte]; exact h1⟩
    obtain ⟨c'', hc''⟩ := hocc
    refine ⟨ps.length, c'', hc.trans ?_⟩
    rw [Phi_sigmaApply _ ps 0 (fun m hm => by simp [List.getD_eq_getElem?_getD, hm]),
      pairUp_spec, ← gaussSplit_spec, applyB_append]
    exact applyB_infix bs (by simpa [applyB] using hc'')

end Trip

/-- **Conjecture 53 (Garrity–Osterman), MathDB 365088.** For every directive
d : ℕ → {S0, S1} and every n ≥ 1, the number of distinct factors of length n of
the S(e,23,e)-adic language L(σ) of Definition 14 is at most 3n. -/
theorem garrity_osterman_conj53 (d : ℕ → Bool) (n : ℕ) (hn : 1 ≤ n) :
    Trip.complexity (Trip.lang d) n ≤ 3 * n := by
  classical
  obtain ⟨r, hr⟩ := Trip.finite_factors_one_level d (Trip.S (Trip.lang d) n)
    (fun w hw => (Trip.mem_S.mp hw).2)
  obtain ⟨g, i0, hg, hemb⟩ := Trip.prefix_embeds d r
  calc Trip.complexity (Trip.lang d) n = (Trip.S (Trip.lang d) n).card := Trip.complexity_eq _ _
    _ ≤ (Trip.S (Trip.Lang g 0) n).card := by
        apply Finset.card_le_card
        intro w hw
        exact Trip.mem_S.mpr ⟨(Trip.mem_S.mp hw).1, hemb w (hr w hw)⟩
    _ = Trip.complexity (Trip.Lang g 0) n := (Trip.complexity_eq _ _).symm
    _ ≤ 3 * n := Trip.eventually_tau_bound g i0 hg n hn

theorem garrity_osterman_conj53_prop : Trip.Conjecture53 :=
  fun d n hn => garrity_osterman_conj53 d n hn

#print axioms garrity_osterman_conj53
#print axioms garrity_osterman_conj53_prop
```

### `TripAudit.lean`

```lean
import TripMain
import TripSanity
import Mathlib.Data.Fin.VecNotation

/-! Audit: the literal definitions, the endpoint, a robustness check on the
indexing of Definition 14, and the axioms. -/

namespace Trip

/-- Definition 14 with n ∈ ℕ including 0 or n ≥ 1 gives the same language. -/
theorem lang_iff_pos_level (d : ℕ → Bool) (w : Word) :
    lang d w ↔ ∃ r, 1 ≤ r ∧ ∃ c : Letter, w <:+: prefImage d r [c] := by
  constructor
  · rintro ⟨r, c, h⟩
    obtain ⟨c', h'⟩ := prefixLanguage_succ d r ⟨c, h⟩
    exact ⟨r + 1, by omega, c', h'⟩
  · rintro ⟨r, -, c, h⟩; exact ⟨r, c, h⟩

/-- The review's literal forms of S0 = (1→2, 2→13, 3→3) and S1 = (1→1, 2→2, 3→13). -/
theorem S0_eq_review : S0 = ![[1], [0, 2], [2]] := by funext c; fin_cases c <;> rfl
theorem S1_eq_review : S1 = ![[0], [1], [0, 2]] := by funext c; fin_cases c <;> rfl

end Trip

#check @Trip.S0_eq_review
#check @Trip.S1_eq_review
#print axioms Trip.S0_eq_review
#print axioms Trip.S1_eq_review
#eval Lean.versionString
#print Trip.S0
#print Trip.S1
#print Trip.subst
#print Trip.prefImage
#print Trip.lang
#print Trip.complexity
#print Trip.Conjecture53
#check @garrity_osterman_conj53
#check @garrity_osterman_conj53_prop
#check @Trip.lang_iff_pos_level
#check @Trip.allS1_small_complexities
#check @Trip.child_edge_iff
#check @Trip.special_parse
#check @Trip.seeds_complete
#check @Trip.forest_bound
#check @Trip.first_difference
#check @Trip.eventually_tau_bound
#check @Trip.prefix_embeds
#print axioms garrity_osterman_conj53
#print axioms garrity_osterman_conj53_prop
#print axioms Trip.lang_iff_pos_level
#print axioms Trip.allS1_small_complexities
#print axioms Trip.child_edge_iff
#print axioms Trip.seeds_complete
#print axioms Trip.forest_bound
#print axioms Trip.first_difference
#print axioms Trip.eventually_tau_bound
#print axioms Trip.prefix_embeds
```

