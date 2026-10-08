import Research.WordCodec

/-! W016 public numerical layout and exact data encoding only. Numerical
admission is NOT admission of either pending instruction graph. Host parsers
below are representation/proof tools, not executed guest packing or validation.
No query program, fuel sufficiency, execution count or speed claim is supplied. -/
namespace Research.WordQueryData

open WordCore WordCodec

structure Sizes where
  W : Nat
  m : Nat
  k : Nat
  deriving Repr, DecidableEq

def Sizes.U (s : Sizes) : Nat := 2 ^ s.W
def Sizes.R (_s : Sizes) : Nat := 32
def Sizes.L (s : Sizes) : Nat := 2 * s.W + s.m * (s.k + s.W) + s.k
def Sizes.O (_s : Sizes) : Nat := 2
def Sizes.B (s : Sizes) : Nat := s.L + 2
def Sizes.A (s : Sizes) : Nat := s.B + 2 * s.m
def Sizes.M (s : Sizes) : Nat := s.A + 4
def Sizes.I (s : Sizes) : Nat := s.R + s.M + s.L
/-- The unchanged public challenge budget; no sufficiency theorem is asserted. -/
def Sizes.F (s : Sizes) : Nat := s.I + 256 * (s.L + 4 * s.m + 32)

/-- Numerical prerequisites only. Frozen program lengths and operands are not
yet available, so this predicate supplies NO common-code-admission witness. -/
def NumericallyAdmissible (s : Sizes) : Prop :=
  0 < s.W ∧ s.k ≤ s.W ∧ s.M ≤ s.U

instance (s : Sizes) : Decidable (NumericallyAdmissible s) :=
  inferInstanceAs (Decidable (0 < s.W ∧ s.k ≤ s.W ∧ s.M ≤ s.U))

theorem header_bounds (s : Sizes) (h : NumericallyAdmissible s) :
    s.m < s.U ∧ s.k < s.U ∧ s.W < s.U := by
  have hw : s.W < s.U := Nat.lt_two_pow_self
  have hm := h.2.2
  unfold Sizes.M Sizes.A Sizes.B at hm
  exact ⟨by omega, by have := h.2.1; omega, hw⟩

theorem layout_bounds (s : Sizes) (h : NumericallyAdmissible s) :
    s.L + 2 ≤ s.M ∧ s.L < s.U ∧ s.B < s.U ∧ s.A < s.U ∧
      s.A + 1 < s.U ∧ s.A + 2 < s.U ∧ s.A + 3 < s.U := by
  have hm := h.2.2
  unfold Sizes.M Sizes.A Sizes.B at hm ⊢
  omega

theorem table_address_bounds (s : Sizes) (h : NumericallyAdmissible s) (j : Fin s.m) :
    s.B ≤ s.B + 2 * j.val ∧ s.B + 2 * j.val + 1 < s.A ∧
      s.B + 2 * j.val + 1 < s.M ∧ 2 * j.val < s.U := by
  have hj := j.isLt
  have hm := h.2.2
  unfold Sizes.M Sizes.A at hm ⊢
  omega

theorem output_address_bounds (s : Sizes) (h : NumericallyAdmissible s) :
    s.L + 1 < s.B ∧ s.L + 1 < s.M ∧ s.L + 1 < s.U := by
  have hm := h.2.2
  unfold Sizes.M Sizes.A Sizes.B at hm ⊢
  omega

theorem key_word_bound (s : Sizes) (h : NumericallyAdmissible s) (key : Fin (2 ^ s.k)) :
    key.val < s.U :=
  Nat.lt_of_lt_of_le key.isLt (Nat.pow_le_pow_right (by decide) h.2.1)

theorem literal_two_bound (s : Sizes) (h : NumericallyAdmissible s) : 2 < s.U := by
  have hm := h.2.2
  unfold Sizes.M at hm
  omega

def Sizes.recordStart (s : Sizes) (j : Nat) : Nat := 2 * s.W + j * (s.k + s.W)
def Sizes.queryStart (s : Sizes) : Nat := 2 * s.W + s.m * (s.k + s.W)

theorem source_end_bounds (s : Sizes) (h : NumericallyAdmissible s) :
    2 * s.W ≤ s.queryStart ∧ s.queryStart + s.k = s.L ∧ s.L < s.U := by
  have hl := (layout_bounds s h).2.1
  unfold Sizes.queryStart Sizes.L at *
  omega

theorem record_field_bounds (s : Sizes) (h : NumericallyAdmissible s) (j : Fin s.m) :
    2 * s.W ≤ s.recordStart j.val ∧
    s.recordStart j.val + s.k + s.W ≤ s.queryStart ∧
    s.recordStart j.val + s.k + s.W < s.U := by
  have hj : j.val + 1 ≤ s.m := by have := j.isLt; omega
  have hp := Nat.mul_le_mul_right (s.k + s.W) hj
  simp only [Nat.add_mul, Nat.one_mul] at hp
  have hl := (layout_bounds s h).2.1
  unfold Sizes.recordStart Sizes.queryStart Sizes.L at *
  omega

theorem index_increment_bound (s : Sizes) (h : NumericallyAdmissible s) (j : Fin s.m) :
    j.val + 1 ≤ s.m ∧ j.val + 1 < s.U := by
  have hj := j.isLt
  have hm := (header_bounds s h).1
  omega

/-- Constructed exclusively from public sizes and numerical evidence. -/
def profile (s : Sizes) (h : NumericallyAdmissible s) : Profile where
  W := s.W
  R := s.R
  M := s.M
  L := s.L
  O := s.O
  W_pos := h.1
  R_pos := by change 0 < 32; decide
  heap_bound := h.2.2
  layout_bound := (layout_bounds s h).1

theorem profile_fields (s : Sizes) (h : NumericallyAdmissible s) :
    (profile s h).W = s.W ∧ (profile s h).R = 32 ∧
    (profile s h).M = s.M ∧ (profile s h).L = s.L ∧ (profile s h).O = 2 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

structure Entry (s : Sizes) where
  key : Fin (2 ^ s.k)
  payload : Fin s.U
  deriving Repr, DecidableEq

/-- Vector is an array with exactly m entries. Sortedness is a separate
precondition; the encoder neither sorts nor assumes it. -/
structure Data (s : Sizes) where
  entries : Vector (Entry s) s.m
  query : Fin (2 ^ s.k)
  deriving Repr, DecidableEq

def Sorted {s : Sizes} (d : Data s) : Prop :=
  ∀ i j : Fin s.m, i.val ≤ j.val →
    (d.entries.get i).key.val ≤ (d.entries.get j).key.val

/-- A sorted data witness exists at every public shape, independent of code
admission. It is NOT evidence that either pending query program is admitted. -/
def zeroData (s : Sizes) : Data s :=
  ⟨Vector.replicate s.m ⟨⟨0, Nat.two_pow_pos _⟩, ⟨0, Nat.two_pow_pos _⟩⟩,
    ⟨0, Nat.two_pow_pos _⟩⟩

theorem zeroData_sorted (s : Sizes) : Sorted (zeroData s) := by
  intro i j _
  simp [zeroData, Vector.get]

theorem sorted_data_nonempty (s : Sizes) : ∃ d : Data s, Sorted d :=
  ⟨zeroData s, zeroData_sorted s⟩

theorem zero_width_values (s : Sizes) (hk : s.k = 0) (d : Data s) :
    d.query.val = 0 ∧ ∀ j : Fin s.m, (d.entries.get j).key.val = 0 := by
  have hq := d.query.isLt
  simp only [hk, Nat.pow_zero] at hq
  constructor
  · omega
  · intro j
    have hj := (d.entries.get j).key.isLt
    simp only [hk, Nat.pow_zero] at hj
    omega

def encodeEntry {s : Sizes} (e : Entry s) : List Bool :=
  bits s.k e.key.val ++ bits s.W e.payload.val

def encodeEntries {s : Sizes} (es : List (Entry s)) : List Bool :=
  es.flatMap encodeEntry

def tableBits {s : Sizes} (es : Vector (Entry s) s.m) : List Bool :=
  bits s.W s.m ++ bits s.W s.k ++ encodeEntries es.toList

def encode {s : Sizes} (d : Data s) : List Bool :=
  tableBits d.entries ++ bits s.k d.query.val

theorem bits_length (width value : Nat) : (bits width value).length = width := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih => simp only [bits, List.length_cons, ih]

theorem encodeEntry_length {s : Sizes} (e : Entry s) :
    (encodeEntry e).length = s.k + s.W := by
  simp only [encodeEntry, List.length_append, bits_length]

theorem encodeEntries_length {s : Sizes} (es : List (Entry s)) :
    (encodeEntries es).length = es.length * (s.k + s.W) := by
  induction es with
  | nil => simp [encodeEntries]
  | cons e es ih =>
    simp only [encodeEntries, List.flatMap_cons, List.length_append, encodeEntry_length,
      List.length_cons] at *
    rw [ih]
    simp only [Nat.add_mul, Nat.one_mul]
    omega

theorem encode_length {s : Sizes} (d : Data s) : (encode d).length = s.L := by
  simp only [encode, tableBits, List.length_append, bits_length, encodeEntries_length, Vector.length_toList,
    Sizes.L]
  omega

theorem tableBits_length {s : Sizes} (es : Vector (Entry s) s.m) :
    (tableBits es).length = s.queryStart := by
  simp only [tableBits, List.length_append, bits_length, encodeEntries_length,
    Vector.length_toList, Sizes.queryStart]
  omega

/-- The entire header/table prefix is independent of the query. -/
theorem encode_table_prefix {s : Sizes} (d : Data s) :
    (encode d).take s.queryStart = tableBits d.entries :=
  List.take_left' (tableBits_length d.entries)

/-- Entrywise conversion preserving the complete exact encoded bit list. -/
def rawInput {s : Sizes} (d : Data s) : Fin s.L → Bool :=
  fun i => (encode d)[i.val]'(by rw [encode_length]; exact i.isLt)

theorem rawInput_entry {s : Sizes} (d : Data s) (i : Fin s.L) :
    rawInput d i = (encode d)[i.val]'(by rw [encode_length]; exact i.isLt) := rfl

theorem rawInput_list {s : Sizes} (d : Data s) : List.ofFn (rawInput d) = encode d := by
  apply List.ext_getElem
  · simp [encode_length]
  · intro i hi hj
    simp only [List.getElem_ofFn, rawInput]

/-- Host representation parser only. These range tests are not free guest
validation and do not implement the W016 charged decoding loop. -/
def parseEntry (s : Sizes) (input : List Bool) : Option (Entry s × List Bool) := do
  let (key, rest) ← parseBits s.k input
  let (payload, rest) ← parseBits s.W rest
  if hk : key < 2 ^ s.k then
    if hp : payload < s.U then
      pure (⟨⟨key, hk⟩, ⟨payload, hp⟩⟩, rest)
    else none
  else none

theorem parseEntry_roundtrip {s : Sizes} (e : Entry s) (suffix : List Bool) :
    parseEntry s (encodeEntry e ++ suffix) = some (e, suffix) := by
  simp [encodeEntry, List.append_assoc, parseEntry,
    parseBits_exact s.k e.key.val e.key.isLt,
    parseBits_exact s.W e.payload.val e.payload.isLt, e.key.isLt, e.payload.isLt]

def parseEntries (s : Sizes) : Nat → List Bool → Option (List (Entry s) × List Bool)
  | 0, rest => some ([], rest)
  | n + 1, input => do
      let (e, rest) ← parseEntry s input
      let (es, rest) ← parseEntries s n rest
      pure (e :: es, rest)

theorem parseEntries_roundtrip {s : Sizes} (es : List (Entry s)) (suffix : List Bool) :
    parseEntries s es.length (encodeEntries es ++ suffix) = some (es, suffix) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [encodeEntries, List.flatMap_cons, List.length_cons, List.append_assoc] at *
    simp [parseEntries, parseEntry_roundtrip, ih]

/-- Host typed-data parser. Header agreement is checked here for representation
roundtrips, not claimed as an executed check in either future query program. -/
def parseData (s : Sizes) (input : List Bool) : Option (Data s × List Bool) := do
  let (m, rest) ← parseBits s.W input
  let (k, rest) ← parseBits s.W rest
  if m = s.m ∧ k = s.k then
    let (es, rest) ← parseEntries s s.m rest
    if hn : es.length = s.m then
      let (query, rest) ← parseBits s.k rest
      if hq : query < 2 ^ s.k then
        pure (⟨⟨es.toArray, by simpa using hn⟩, ⟨query, hq⟩⟩, rest)
      else none
    else none
  else none

theorem parseData_roundtrip {s : Sizes} (h : NumericallyAdmissible s)
    (d : Data s) (suffix : List Bool) :
    parseData s (encode d ++ suffix) = some (d, suffix) := by
  have hb := header_bounds s h
  have he := parseEntries_roundtrip d.entries.toList (bits s.k d.query.val ++ suffix)
  simp only [Vector.length_toList] at he
  simp [encode, tableBits, List.append_assoc, parseData,
    parseBits_exact s.W s.m hb.1, parseBits_exact s.W s.k hb.2.1,
    he, parseBits_exact s.k d.query.val d.query.isLt, d.query.isLt, Vector.toArray_toList]

theorem encode_injective {s : Sizes} (h : NumericallyAdmissible s) (a b : Data s)
    (he : encode a = encode b) : a = b := by
  have hp := congrArg (fun xs => parseData s (xs ++ [])) he
  simpa only [parseData_roundtrip h, Option.some.injEq, Prod.mk.injEq, and_true] using hp

theorem rawInput_injective {s : Sizes} (h : NumericallyAdmissible s) (a b : Data s)
    (he : rawInput a = rawInput b) : a = b := by
  apply encode_injective h
  apply List.ext_getElem
  · rw [encode_length, encode_length]
  · intro i hi hj
    have hil : i < s.L := by simpa only [encode_length] using hi
    exact congrFun he ⟨i, hil⟩

private def emptySizes : Sizes := ⟨4, 0, 2⟩
private def zeroWidthSizes : Sizes := ⟨5, 2, 0⟩
private def fullWidthSizes : Sizes := ⟨6, 2, 6⟩

private def emptyData : Data emptySizes := ⟨#v[], ⟨3, by decide⟩⟩
private def zeroWidthData : Data zeroWidthSizes :=
  ⟨#v[⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩,
      ⟨⟨0, by decide⟩, ⟨31, by decide⟩⟩], ⟨0, by decide⟩⟩
private def fullWidthData : Data fullWidthSizes :=
  ⟨#v[⟨⟨63, by decide⟩, ⟨0, by decide⟩⟩,
      ⟨⟨63, by decide⟩, ⟨63, by decide⟩⟩], ⟨63, by decide⟩⟩

/-- These are numerical examples only; none witnesses pending code admission.
In particular the exclusive heap endpoint can equal the word bound. -/
theorem numerical_boundary_checks :
    NumericallyAdmissible emptySizes ∧ emptySizes.M = emptySizes.U ∧
    NumericallyAdmissible zeroWidthSizes ∧ NumericallyAdmissible fullWidthSizes ∧
    ¬NumericallyAdmissible ⟨4, 1, 0⟩ ∧ ¬NumericallyAdmissible ⟨6, 0, 7⟩ := by
  decide +kernel

/-- Kernel evaluation of representation tools, not execution of a guest query.
Covers empty/zero/full-width data, maximal values, duplicates with distinct
payloads, preserved suffixes, and malformed host headers. -/
theorem parser_boundary_checks :
    parseData emptySizes (encode emptyData ++ [true, false]) = some (emptyData, [true, false]) ∧
    parseData zeroWidthSizes (encode zeroWidthData ++ [false]) = some (zeroWidthData, [false]) ∧
    parseData fullWidthSizes (encode fullWidthData) = some (fullWidthData, []) ∧
    parseData fullWidthSizes (bits 6 1 ++ bits 6 6) = none ∧
    parseData fullWidthSizes [] = none ∧
    bits 3 1 = [true, false, false] ∧ bits 3 4 = [false, false, true] := by
  repeat' constructor
  all_goals decide +kernel

end Research.WordQueryData
