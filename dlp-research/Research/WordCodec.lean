import Research.Problem
import Research.WordCore

/-! Executable typed instruction/program/profile serialization for W011.
Suffix roundtrips prove injectivity, with actual unary-prefix bit lengths.
This deliberately noncompact encoding prices no guest computation or decoder
work and establishes no runtime, solver or description-budget feasibility claim.
-/
namespace Research.WordCodec

/-- Deliberately noncompact unary natural encoding, including a terminator. -/
def unary (n : Nat) : List Bool := List.replicate n true ++ [false]

def parseUnary : List Bool → Option (Nat × List Bool)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => do
      let (n, suffix) ← parseUnary rest
      pure (n + 1, suffix)

theorem unary_length (n : Nat) : (unary n).length = n + 1 := by
  simp [unary]

theorem parseUnary_roundtrip (n : Nat) (suffix : List Bool) :
    parseUnary (unary n ++ suffix) = some (n, suffix) := by
  induction n with
  | zero => simp [unary, parseUnary]
  | succ n ih =>
    change (parseUnary (unary n ++ suffix)).bind _ = _
    rw [ih]
    rfl

theorem parseUnary_unterminated (n : Nat) :
    parseUnary (List.replicate n true) = none := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, parseUnary, ih]

theorem unary_injective (a b : Nat) (h : unary a = unary b) : a = b := by
  have hlen := congrArg List.length h
  simpa only [unary_length, Nat.add_right_cancel_iff] using hlen

/-- Parse exactly width little-endian bits, preserving any unused suffix. -/
def parseBits : Nat → List Bool → Option (Nat × List Bool)
  | 0, rest => some (0, rest)
  | _ + 1, [] => none
  | width + 1, bit :: rest => do
      let (n, suffix) ← parseBits width rest
      pure ((if bit then 1 else 0) + 2 * n, suffix)

theorem parseBits_roundtrip (width value : Nat) (suffix : List Bool) :
    parseBits width (bits width value ++ suffix) = some (value % 2 ^ width, suffix) := by
  induction width generalizing value with
  | zero => simp [bits, parseBits, Nat.mod_one]
  | succ width ih =>
    simp only [bits, List.cons_append, parseBits, ih, pure]
    rw [Nat.pow_succ', Nat.mod_mul]
    split <;> simp_all <;> omega

theorem parseBits_exact (width value : Nat) (h : value < 2 ^ width) (suffix : List Bool) :
    parseBits width (bits width value ++ suffix) = some (value, suffix) := by
  simpa only [Nat.mod_eq_of_lt h] using parseBits_roundtrip width value suffix

def encodeFields (fields : List Nat) : List Bool := fields.flatMap unary

def parseFields : Nat → List Bool → Option (List Nat × List Bool)
  | 0, rest => some ([], rest)
  | count + 1, input => do
      let (n, rest) ← parseUnary input
      let (ns, suffix) ← parseFields count rest
      pure (n :: ns, suffix)

theorem parseFields_roundtrip (fields : List Nat) (suffix : List Bool) :
    parseFields fields.length (encodeFields fields ++ suffix) = some (fields, suffix) := by
  induction fields with
  | nil => rfl
  | cons n rest ih =>
    simp only [encodeFields, List.flatMap_cons, List.length_cons, List.append_assoc] at *
    simp [parseFields, parseUnary_roundtrip, ih]



open Research.WordCore

def tag {P : Profile} : Instr P → Nat
  | .const .. => 0
  | .mov .. => 1
  | .add .. => 2
  | .sub .. => 3
  | .mul .. => 4
  | .divmod .. => 5
  | .eq .. => 6
  | .lt .. => 7
  | .load .. => 8
  | .store .. => 9
  | .jump .. => 10
  | .branch .. => 11
  | .halt => 12

def fields {P : Profile} : Instr P → List Nat
  | .const d v t => [d.val, v.val, t.val]
  | .mov d a t => [d.val, a.val, t.val]
  | .add d a b t => [d.val, a.val, b.val, t.val]
  | .sub d a b t => [d.val, a.val, b.val, t.val]
  | .mul d a b t => [d.val, a.val, b.val, t.val]
  | .divmod dq dr a b t => [dq.val, dr.val, a.val, b.val, t.val]
  | .eq d a b t => [d.val, a.val, b.val, t.val]
  | .lt d a b t => [d.val, a.val, b.val, t.val]
  | .load d a t => [d.val, a.val, t.val]
  | .store a b t => [a.val, b.val, t.val]
  | .jump t => [t.val]
  | .branch a t0 t1 => [a.val, t0.val, t1.val]
  | .halt  => []

def fieldCount : Nat → Nat
  | 0 => 3
  | 1 => 3
  | 2 => 4
  | 3 => 4
  | 4 => 4
  | 5 => 5
  | 6 => 4
  | 7 => 4
  | 8 => 3
  | 9 => 3
  | 10 => 1
  | 11 => 3
  | 12 => 0
  | _ => 0

/-- Admission rejects malformed tags, arity, registers and word operands. -/
def admitInstr (P : Profile) : Nat → List Nat → Option (Instr P)
  | 0, [d, v, t] =>
    if h_d : d < P.R then
    if h_v : v < P.bound then
    if h_t : t < P.bound then
    some (.const ⟨d, h_d⟩ ⟨v, h_v⟩ ⟨t, h_t⟩)
    else none
    else none
    else none
  | 1, [d, a, t] =>
    if h_d : d < P.R then
    if h_a : a < P.R then
    if h_t : t < P.bound then
    some (.mov ⟨d, h_d⟩ ⟨a, h_a⟩ ⟨t, h_t⟩)
    else none
    else none
    else none
  | 2, [d, a, b, t] =>
    if h_d : d < P.R then
    if h_a : a < P.R then
    if h_b : b < P.R then
    if h_t : t < P.bound then
    some (.add ⟨d, h_d⟩ ⟨a, h_a⟩ ⟨b, h_b⟩ ⟨t, h_t⟩)
    else none
    else none
    else none
    else none
  | 3, [d, a, b, t] =>
    if h_d : d < P.R then
    if h_a : a < P.R then
    if h_b : b < P.R then
    if h_t : t < P.bound then
    some (.sub ⟨d, h_d⟩ ⟨a, h_a⟩ ⟨b, h_b⟩ ⟨t, h_t⟩)
    else none
    else none
    else none
    else none
  | 4, [d, a, b, t] =>
    if h_d : d < P.R then
    if h_a : a < P.R then
    if h_b : b < P.R then
    if h_t : t < P.bound then
    some (.mul ⟨d, h_d⟩ ⟨a, h_a⟩ ⟨b, h_b⟩ ⟨t, h_t⟩)
    else none
    else none
    else none
    else none
  | 5, [dq, dr, a, b, t] =>
    if h_dq : dq < P.R then
    if h_dr : dr < P.R then
    if h_a : a < P.R then
    if h_b : b < P.R then
    if h_t : t < P.bound then
    some (.divmod ⟨dq, h_dq⟩ ⟨dr, h_dr⟩ ⟨a, h_a⟩ ⟨b, h_b⟩ ⟨t, h_t⟩)
    else none
    else none
    else none
    else none
    else none
  | 6, [d, a, b, t] =>
    if h_d : d < P.R then
    if h_a : a < P.R then
    if h_b : b < P.R then
    if h_t : t < P.bound then
    some (.eq ⟨d, h_d⟩ ⟨a, h_a⟩ ⟨b, h_b⟩ ⟨t, h_t⟩)
    else none
    else none
    else none
    else none
  | 7, [d, a, b, t] =>
    if h_d : d < P.R then
    if h_a : a < P.R then
    if h_b : b < P.R then
    if h_t : t < P.bound then
    some (.lt ⟨d, h_d⟩ ⟨a, h_a⟩ ⟨b, h_b⟩ ⟨t, h_t⟩)
    else none
    else none
    else none
    else none
  | 8, [d, a, t] =>
    if h_d : d < P.R then
    if h_a : a < P.R then
    if h_t : t < P.bound then
    some (.load ⟨d, h_d⟩ ⟨a, h_a⟩ ⟨t, h_t⟩)
    else none
    else none
    else none
  | 9, [a, b, t] =>
    if h_a : a < P.R then
    if h_b : b < P.R then
    if h_t : t < P.bound then
    some (.store ⟨a, h_a⟩ ⟨b, h_b⟩ ⟨t, h_t⟩)
    else none
    else none
    else none
  | 10, [t] =>
    if h_t : t < P.bound then
    some (.jump ⟨t, h_t⟩)
    else none
  | 11, [a, t0, t1] =>
    if h_a : a < P.R then
    if h_t0 : t0 < P.bound then
    if h_t1 : t1 < P.bound then
    some (.branch ⟨a, h_a⟩ ⟨t0, h_t0⟩ ⟨t1, h_t1⟩)
    else none
    else none
    else none
  | 12, [] =>
    some (.halt)
  | _, _ => none

def encodeInstr {P : Profile} (i : Instr P) : List Bool :=
  bits 4 (tag i) ++ encodeFields (fields i)

def parseInstr (P : Profile) (input : List Bool) : Option (Instr P × List Bool) := do
  let (t, rest) ← parseBits 4 input
  let (fs, suffix) ← parseFields (fieldCount t) rest
  let i ← admitInstr P t fs
  pure (i, suffix)

theorem fields_count {P : Profile} (i : Instr P) :
    (fields i).length = fieldCount (tag i) := by cases i <;> rfl

theorem tag_bound {P : Profile} (i : Instr P) : tag i < 2 ^ 4 := by
  cases i <;> simp [tag]

theorem admitInstr_roundtrip {P : Profile} (i : Instr P) :
    admitInstr P (tag i) (fields i) = some i := by
  cases i <;> simp [tag, fields, admitInstr]

theorem parseInstr_roundtrip {P : Profile} (i : Instr P) (suffix : List Bool) :
    parseInstr P (encodeInstr i ++ suffix) = some (i, suffix) := by
  simp only [encodeInstr, List.append_assoc, parseInstr,
    parseBits_exact 4 (tag i) (tag_bound i)]
  change (do
    let (fs, rest) ← parseFields (fieldCount (tag i)) (encodeFields (fields i) ++ suffix)
    let j ← admitInstr P (tag i) fs
    pure (j, rest)) = _
  rw [← fields_count i, parseFields_roundtrip]
  simp [admitInstr_roundtrip]

theorem encodeInstr_injective {P : Profile} (a b : Instr P)
    (h : encodeInstr a = encodeInstr b) : a = b := by
  have e := congrArg (fun xs => parseInstr P (xs ++ [])) h
  simpa only [parseInstr_roundtrip, Option.some.injEq, Prod.mk.injEq, and_true] using e

theorem encodeFields_length (fs : List Nat) :
    (encodeFields fs).length = (fs.map (· + 1)).sum := by
  induction fs with
  | nil => rfl
  | cons n ns ih =>
    simp only [encodeFields, List.flatMap_cons, List.length_append] at *
    rw [ih, unary_length]
    rfl

theorem encodeInstr_length {P : Profile} (i : Instr P) :
    (encodeInstr i).length = 4 + ((fields i).map (· + 1)).sum := by
  simp [encodeInstr, bits, encodeFields_length]
  omega


def encodeInstrs {P : Profile} (is : List (Instr P)) : List Bool := is.flatMap encodeInstr

def parseInstrs (P : Profile) : Nat → List Bool → Option (List (Instr P) × List Bool)
  | 0, rest => some ([], rest)
  | count + 1, input => do
      let (i, rest) ← parseInstr P input
      let (is, suffix) ← parseInstrs P count rest
      pure (i :: is, suffix)

theorem parseInstrs_roundtrip {P : Profile} (is : List (Instr P)) (suffix : List Bool) :
    parseInstrs P is.length (encodeInstrs is ++ suffix) = some (is, suffix) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [encodeInstrs, List.flatMap_cons, List.length_cons, List.append_assoc] at *
    simp [parseInstrs, parseInstr_roundtrip, ih]

def encodeProgram {P : Profile} (c : Program P) : List Bool :=
  unary c.code.size ++ encodeInstrs c.code.toList

/-- Both the claimed instruction count and the constructed code are admitted.
The second guard is redundant on a successful parser, but keeps construction
independent of an unproved parser-length invariant. -/
def parseProgram (P : Profile) (input : List Bool) : Option (Program P × List Bool) := do
  let (count, rest) ← parseUnary input
  if count ≤ P.bound then
    let (is, suffix) ← parseInstrs P count rest
    if h : is.toArray.size ≤ P.bound then
      pure (⟨is.toArray, h⟩, suffix)
    else none
  else none

theorem parseProgram_roundtrip {P : Profile} (c : Program P) (suffix : List Bool) :
    parseProgram P (encodeProgram c ++ suffix) = some (c, suffix) := by
  simp only [encodeProgram, List.append_assoc, parseProgram, parseUnary_roundtrip]
  change (if c.code.size ≤ P.bound then (do
    let (is, rest) ← parseInstrs P c.code.size (encodeInstrs c.code.toList ++ suffix)
    if h : is.toArray.size ≤ P.bound then pure ((⟨is.toArray, h⟩ : Program P), rest) else none)
    else none) = _
  rw [ite_eq_left c.bounded]
  have e := parseInstrs_roundtrip c.code.toList suffix
  simp only [Array.length_toList] at e
  rw [e]
  simp [c.bounded]

theorem encodeProgram_injective {P : Profile} (a b : Program P)
    (h : encodeProgram a = encodeProgram b) : a = b := by
  have e := congrArg (fun xs => parseProgram P (xs ++ [])) h
  simpa only [parseProgram_roundtrip, Option.some.injEq, Prod.mk.injEq, and_true] using e

def programBits {P : Profile} (c : Program P) : Nat := (encodeProgram c).length

theorem encodeInstrs_length {P : Profile} (is : List (Instr P)) :
    (encodeInstrs is).length = (is.map (fun i => 4 + ((fields i).map (· + 1)).sum)).sum := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [encodeInstrs, List.flatMap_cons, List.length_append] at *
    rw [ih, encodeInstr_length]
    rfl

theorem programBits_exact {P : Profile} (c : Program P) :
    programBits c = c.code.size + 1 +
      (c.code.toList.map (fun i => 4 + ((fields i).map (· + 1)).sum)).sum := by
  simp [programBits, encodeProgram, unary_length, encodeInstrs_length]

def profileFields (P : Profile) : List Nat := [P.W, P.R, P.M, P.L, P.O]
def encodeProfile (P : Profile) : List Bool := encodeFields (profileFields P)

def admitProfile : List Nat → Option Profile
  | [w, r, m, l, o] =>
    if hw : 0 < w then
    if hr : 0 < r then
    if hm : m ≤ 2 ^ w then
    if hl : l + o ≤ m then some ⟨w, r, m, l, o, hw, hr, hm, hl⟩
    else none else none else none else none
  | _ => none

def parseProfile (input : List Bool) : Option (Profile × List Bool) := do
  let (fs, rest) ← parseFields 5 input
  let p ← admitProfile fs
  pure (p, rest)

theorem admitProfile_roundtrip (P : Profile) : admitProfile (profileFields P) = some P := by
  simp [admitProfile, profileFields, P.W_pos, P.R_pos, P.heap_bound, P.layout_bound]

theorem parseProfile_roundtrip (P : Profile) (suffix : List Bool) :
    parseProfile (encodeProfile P ++ suffix) = some (P, suffix) := by
  have count : (profileFields P).length = 5 := rfl
  simp only [parseProfile, encodeProfile, ← count, parseFields_roundtrip]
  simp [admitProfile_roundtrip]

theorem encodeProfile_injective (P Q : Profile) (h : encodeProfile P = encodeProfile Q) :
    P = Q := by
  have e := congrArg (fun xs => parseProfile (xs ++ [])) h
  simpa only [parseProfile_roundtrip, Option.some.injEq, Prod.mk.injEq, and_true] using e

abbrev Manifest := (P : Profile) × Program P

def encodeManifest (m : Manifest) : List Bool := encodeProfile m.1 ++ encodeProgram m.2

def parseManifest (input : List Bool) : Option (Manifest × List Bool) := do
  let (p, rest) ← parseProfile input
  let (c, suffix) ← parseProgram p rest
  pure (⟨p, c⟩, suffix)

theorem parseManifest_roundtrip (m : Manifest) (suffix : List Bool) :
    parseManifest (encodeManifest m ++ suffix) = some (m, suffix) := by
  simp [encodeManifest, List.append_assoc, parseManifest,
    parseProfile_roundtrip, parseProgram_roundtrip]

theorem encodeManifest_injective (a b : Manifest) (h : encodeManifest a = encodeManifest b) :
    a = b := by
  have e := congrArg (fun xs => parseManifest (xs ++ [])) h
  simpa only [parseManifest_roundtrip, Option.some.injEq, Prod.mk.injEq, and_true] using e

theorem encodeProfile_length (P : Profile) :
    (encodeProfile P).length = P.W + P.R + P.M + P.L + P.O + 5 := by
  simp [encodeProfile, encodeFields_length, profileFields]
  omega

theorem encodeManifest_length (m : Manifest) :
    (encodeManifest m).length = m.1.W + m.1.R + m.1.M + m.1.L + m.1.O + 5 + programBits m.2 := by
  simp [encodeManifest, encodeProfile_length, programBits]

/-- Reserved four-bit tags fail regardless of the following suffix. -/
theorem reserved_tags_rejected (P : Profile) (suffix : List Bool) :
    parseInstr P (bits 4 13 ++ suffix) = none ∧
    parseInstr P (bits 4 14 ++ suffix) = none ∧
    parseInstr P (bits 4 15 ++ suffix) = none := by
  simp [parseInstr, bits, parseBits, parseFields, fieldCount, admitInstr]

private def testProfile : Profile :=
  ⟨1, 2, 2, 0, 0, by decide, by decide, by decide, by decide⟩

/-- Malformed arity and out-of-range operands are rejected, not truncated. -/
theorem admission_boundary_checks :
    admitInstr testProfile 0 [0, 1, 1] ≠ none ∧
    admitInstr testProfile 0 [2, 1, 1] = none ∧
    admitInstr testProfile 0 [0, 2, 1] = none ∧
    admitInstr testProfile 0 [0, 1, 2] = none ∧
    admitInstr testProfile 0 [0, 1] = none ∧
    admitInstr testProfile 12 [0] = none ∧
    admitProfile [0, 1, 0, 0, 0] = none ∧
    admitProfile [1, 0, 0, 0, 0] = none ∧
    admitProfile [1, 1, 3, 0, 0] = none ∧
    admitProfile [1, 1, 2, 2, 1] = none := by
  decide +kernel

/-- Empty code is representable; overlong and truncated declarations fail. -/
theorem program_boundary_checks :
    parseProgram testProfile [false] = some (⟨#[], by decide⟩, []) ∧
    parseProgram testProfile (unary 3) = none ∧
    parseProgram testProfile (unary 1) = none ∧
    parseInstr testProfile [] = none ∧
    parseInstr testProfile [true, true, true] = none := by
  decide +kernel

end Research.WordCodec
