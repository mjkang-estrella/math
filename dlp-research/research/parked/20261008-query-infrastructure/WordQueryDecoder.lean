import Research.WordQueryCode
import Research.WordPacking
import Research.WordRunFacts

/-! Actual guest decoder segments at the five fixed W018 sites. Conditional
internal continuation facts do not provide a fresh-run query contract, global
fuel sufficiency, a whole-program count or a speed comparison. The five entry
instructions and full field-loop induction (9+6w) remain outstanding. -/
namespace Research.WordQueryDecoder

open WordCore WordQueryData WordQueryCode WordPacking

inductive Site where
  | headerM | headerK | entryKey | entryPayload | query
  deriving Repr, DecidableEq

def Site.entry : Site → Nat
  | .headerM => 7
  | .headerK => 20
  | .entryKey => 36
  | .entryPayload => 49
  | .query => 68

def Site.widthRegister : Site → Fin 32
  | .headerM | .headerK | .entryPayload => ⟨3, by decide⟩
  | .entryKey | .query => ⟨5, by decide⟩

def Site.destination : Site → Fin 32
  | .headerM => ⟨4, by decide⟩
  | .headerK => ⟨5, by decide⟩
  | .entryKey => ⟨15, by decide⟩
  | .entryPayload => ⟨16, by decide⟩
  | .query => ⟨17, by decide⟩

/-- Exact common graph rows, including the five-instruction entry, loop,
and two-instruction exit. All targets are explicit. -/
def template (site : Site) : Vector TemplateInstr 13 :=
  ⟨#[.mov ⟨7, by decide⟩ site.widthRegister (.fixed (site.entry + 1)),
      .mov ⟨27, by decide⟩ ⟨6, by decide⟩ (.fixed (site.entry + 2)),
      .add ⟨11, by decide⟩ ⟨6, by decide⟩ ⟨7, by decide⟩ (.fixed (site.entry + 3)),
      .mov ⟨8, by decide⟩ ⟨11, by decide⟩ (.fixed (site.entry + 4)),
      .mov ⟨9, by decide⟩ ⟨0, by decide⟩ (.fixed (site.entry + 5)),
      .lt ⟨24, by decide⟩ ⟨27, by decide⟩ ⟨8, by decide⟩ (.fixed (site.entry + 6)),
      .branch ⟨24, by decide⟩ (.fixed (site.entry + 11)) (.fixed (site.entry + 7)),
      .sub ⟨8, by decide⟩ ⟨8, by decide⟩ ⟨1, by decide⟩ (.fixed (site.entry + 8)),
      .load ⟨10, by decide⟩ ⟨8, by decide⟩ (.fixed (site.entry + 9)),
      .mul ⟨9, by decide⟩ ⟨9, by decide⟩ ⟨2, by decide⟩ (.fixed (site.entry + 10)),
      .add ⟨9, by decide⟩ ⟨9, by decide⟩ ⟨10, by decide⟩ (.fixed (site.entry + 5)),
      .mov ⟨6, by decide⟩ ⟨11, by decide⟩ (.fixed (site.entry + 12)),
      .mov site.destination ⟨9, by decide⟩ (.fixed (site.entry + 13))], rfl⟩

theorem site_entry_bound (site : Site) : site.entry ≤ 68 := by cases site <;> decide

theorem template_bounds (site : Site) :
    ∀ j : Fin 13, ∀ l ∈ (template site).get j |>.words, l.StaticBound := by
  cases site <;> decide

theorem template_rows (site : Site) :
    ∀ j : Fin 13, commonSkeleton[site.entry + j.val]? = some ((template site).get j) := by
  cases site <;> decide

abbrev P (s : Sizes) (h : Admissible s) := profile s h.1

/-- The target following the decoder is representable but need not be fetched
by a local segment ending at that boundary. -/
def pc (s : Sizes) (h : Admissible s) (site : Site) (offset : Nat) (ho : offset ≤ 13) :
    Word (P s h) :=
  ⟨site.entry + offset, by
    have hs := site_entry_bound site
    have hw := (admissible_iff s).mp h |>.2
    have hu : 128 ≤ s.U := Nat.pow_le_pow_right (n := 2) (i := 7) (by decide) hw
    change site.entry + offset < s.U
    omega⟩

theorem template_fits (s : Sizes) (h : Admissible s) (site : Site) (j : Fin 13) :
    ((template site).get j).Fits s :=
  fun l hl => literal_bound s h.1 ((admissible_iff s).mp h).2 l (template_bounds site j l hl)

def block (s : Sizes) (h : Admissible s) (site : Site) : Vector (Instr (P s h)) 13 :=
  Vector.ofFn fun j => instantiateInstr s h.1 ((template site).get j) (template_fits s h site j)

theorem block_get (s : Sizes) (h : Admissible s) (site : Site) (j : Fin 13) :
    (block s h site).get j =
      instantiateInstr s h.1 ((template site).get j) (template_fits s h site j) := by
  change (Vector.ofFn _)[j.val] = _
  rw [Vector.getElem_ofFn]

/-- A premise about actual fetched code slots, never a assumed decoder macro. -/
def Slots (s : Sizes) (h : Admissible s) (site : Site) (code : Program (P s h)) : Prop :=
  ∀ j : Fin 13, code.code[site.entry + j.val]? = some ((block s h site).get j)

private theorem instantiate_lookup (s : Sizes) (hn : NumericallyAdmissible s)
    (xs : Array TemplateInstr) (hf : ∀ i ∈ xs, i.Fits s) (n : Nat) (i : TemplateInstr)
    (he : xs[n]? = some i) :
    (instantiate s hn xs hf)[n]? =
      some (instantiateInstr s hn i (hf i (Array.mem_of_getElem? he))) := by
  obtain ⟨hb, he⟩ := Array.getElem?_eq_some_iff.mp he
  subst i
  apply Array.getElem?_eq_some_iff.mpr
  refine ⟨by simpa only [instantiate_size] using hb, ?_⟩
  simp only [instantiate, Array.getElem_pmap]

theorem linear_slots (s : Sizes) (h : Admissible s) (site : Site) :
    Slots s h site (linear s h) := by
  intro j
  have hj : site.entry + j.val < commonSkeleton.size := by
    rw [commonSkeleton_size]
    have := site_entry_bound site
    have := j.isLt
    omega
  have he : linearSkeleton[site.entry + j.val]? = some ((template site).get j) := by
    rw [linearSkeleton, Array.getElem?_append_left hj]
    exact template_rows site j
  change (instantiate s h.1 linearSkeleton h.2.1.2)[site.entry + j.val]? = _
  rw [block_get]
  exact instantiate_lookup s h.1 linearSkeleton h.2.1.2 _ _ he

theorem binary_slots (s : Sizes) (h : Admissible s) (site : Site) :
    Slots s h site (binary s h) := by
  intro j
  have hj : site.entry + j.val < commonSkeleton.size := by
    rw [commonSkeleton_size]
    have := site_entry_bound site
    have := j.isLt
    omega
  have he : binarySkeleton[site.entry + j.val]? = some ((template site).get j) := by
    rw [binarySkeleton, Array.getElem?_append_left hj]
    exact template_rows site j
  change (instantiate s h.1 binarySkeleton h.2.2.2)[site.entry + j.val]? = _
  rw [block_get]
  exact instantiate_lookup s h.1 binarySkeleton h.2.2.2 _ _ he


/-- A checked sequence of real continued guest steps. This is a proposition,
not a second evaluator or a cost oracle. -/
inductive Segment {Q : Profile} (code : Program Q) :
    State Q → List Opcode → State Q → Prop where
  | nil (a : State Q) : Segment code a [] a
  | cons {a b z : State Q} {op : Opcode} {ops : List Opcode}
      (head : step code a = ⟨.continued b, .instruction op .continued⟩)
      (tail : Segment code b ops z) : Segment code a (op :: ops) z

def guestEvents {Q : Profile} (ops : List Opcode) : List (WordRun.Event Q) :=
  ops.map (fun op => .guest (.instruction op .continued))

theorem segment_continuation {Q : Profile} (code : Program Q)
    (input : Fin Q.L → Bool) {a b : State Q} {ops : List Opcode}
    (hs : Segment code a ops b) :
    WordRun.continueRun code input ops.length (.guest a) =
      ⟨.exhausted (.guest b), guestEvents ops, 0⟩ := by
  induction hs with
  | nil a => rfl
  | @cons a b z op ops head tail ih =>
    simp only [List.length_cons, WordRun.continueRun, WordRun.normalize, head]
    rw [ih]
    rfl

theorem segment_attempts {Q : Profile} (code : Program Q)
    (input : Fin Q.L → Bool) {a b : State Q} {ops : List Opcode}
    (hs : Segment code a ops b) :
    (WordRun.continueRun code input ops.length (.guest a)).used = ops.length := by
  rw [segment_continuation code input hs]
  simp [WordRun.Result.used, guestEvents]

private theorem step_lookup {Q : Profile} (code : Program Q) (a : State Q) (i : Instr Q)
    (he : code.code[a.pc.val]? = some i) :
    step code a = ⟨execInstr i a, .instruction i.opcode (execInstr i a).disposition⟩ := by
  obtain ⟨hb, he⟩ := Array.getElem?_eq_some_iff.mp he
  rw [step_fetched code a hb, he]

private theorem fetched_slot (s : Sizes) (h : Admissible s) (site : Site)
    (code : Program (P s h)) (slots : Slots s h site code)
    (a : State (P s h)) (j : Fin 13)
    (hp : a.pc = pc s h site j.val (by have := j.isLt; omega)) :
    step code a = ⟨execInstr ((block s h site).get j) a,
      .instruction ((block s h site).get j).opcode
        (execInstr ((block s h site).get j) a).disposition⟩ := by
  apply step_lookup
  simpa only [hp, pc] using slots j

abbrev r0 : Fin 32 := ⟨0, by decide⟩
abbrev r1 : Fin 32 := ⟨1, by decide⟩
abbrev r2 : Fin 32 := ⟨2, by decide⟩
abbrev r6 : Fin 32 := ⟨6, by decide⟩
abbrev r8 : Fin 32 := ⟨8, by decide⟩
abbrev r9 : Fin 32 := ⟨9, by decide⟩
abbrev r10 : Fin 32 := ⟨10, by decide⟩
abbrev r11 : Fin 32 := ⟨11, by decide⟩
abbrev r24 : Fin 32 := ⟨24, by decide⟩
abbrev r27 : Fin 32 := ⟨27, by decide⟩

private theorem block_lt (s : Sizes) (h : Admissible s) (site : Site) :
    (block s h site).get ⟨5, by decide⟩ = .lt r24 r27 r8 (pc s h site 6 (by decide)) := by
  rw [block_get]; rfl

private theorem block_branch (s : Sizes) (h : Admissible s) (site : Site) :
    (block s h site).get ⟨6, by decide⟩ =
      .branch r24 (pc s h site 11 (by decide)) (pc s h site 7 (by decide)) := by
  rw [block_get]; rfl

private theorem block_sub (s : Sizes) (h : Admissible s) (site : Site) :
    (block s h site).get ⟨7, by decide⟩ = .sub r8 r8 r1 (pc s h site 8 (by decide)) := by
  rw [block_get]; rfl

private theorem block_load (s : Sizes) (h : Admissible s) (site : Site) :
    (block s h site).get ⟨8, by decide⟩ = .load r10 r8 (pc s h site 9 (by decide)) := by
  rw [block_get]; rfl

private theorem block_mul (s : Sizes) (h : Admissible s) (site : Site) :
    (block s h site).get ⟨9, by decide⟩ = .mul r9 r9 r2 (pc s h site 10 (by decide)) := by
  rw [block_get]; rfl

private theorem block_add (s : Sizes) (h : Admissible s) (site : Site) :
    (block s h site).get ⟨10, by decide⟩ = .add r9 r9 r10 (pc s h site 5 (by decide)) := by
  rw [block_get]; rfl

private theorem block_exit_cursor (s : Sizes) (h : Admissible s) (site : Site) :
    (block s h site).get ⟨11, by decide⟩ = .mov r6 r11 (pc s h site 12 (by decide)) := by
  rw [block_get]; rfl

private theorem block_exit_value (s : Sizes) (h : Admissible s) (site : Site) :
    (block s h site).get ⟨12, by decide⟩ =
      .mov site.destination r9 (pc s h site 13 (by decide)) := by
  rw [block_get]; rfl

def advance {Q : Profile} (a : State Q) (d : Register Q) (v target : Word Q) : State Q :=
  { a.writeReg d v with pc := target }

theorem read_write {Q : Profile} (a : State Q) (d r : Register Q) (v : Word Q) :
    (a.writeReg d v).readReg r = if d = r then v else a.readReg r := by
  change (a.regs.set d.val v)[r.val] = if d = r then v else a.regs[r.val]
  simp only [Vector.getElem_set, Fin.ext_iff]

theorem read_advance {Q : Profile} (a : State Q) (d r : Register Q) (v target : Word Q) :
    (advance a d v target).readReg r = if d = r then v else a.readReg r :=
  read_write a d r v

def setPC {Q : Profile} (a : State Q) (target : Word Q) : State Q :=
  { a with pc := target }

theorem read_setPC {Q : Profile} (a : State Q) (target : Word Q) (r : Register Q) :
    (setPC a target).readReg r = a.readReg r := rfl

/-- Specialization keeps the fixed register indices visible to rewriting;
profile construction is otherwise semireducible. -/
theorem read_advance_query (s : Sizes) (h : Admissible s) (a : State (P s h))
    (d r : Fin 32) (v target : Word (P s h)) :
    (advance a d v target).readReg r = if d = r then v else a.readReg r :=
  read_advance a d r v target

theorem read_setPC_query (s : Sizes) (h : Admissible s) (a : State (P s h))
    (target : Word (P s h)) (r : Fin 32) :
    (setPC a target).readReg r = a.readReg r := rfl

/-- Preconditions reflect each separate checked arithmetic/load operation.
They do not assume that the decoder already ran or that any macro is correct. -/
structure IterationPre (s : Sizes) (h : Admissible s) (a : State (P s h)) where
  above : (a.readReg r27).val < (a.readReg r8).val
  one : (a.readReg r1).val = 1
  two : (a.readReg r2).val = 2
  address : (a.readReg r8).val - 1 < (P s h).M
  multiply : (a.readReg r9).val * 2 < (P s h).bound
  addition : (a.readReg r9).val * 2 +
    (a.heap.get ⟨(a.readReg r8).val - 1, address⟩).val < (P s h).bound

def iterationResult (s : Sizes) (h : Admissible s) (site : Site)
    (a : State (P s h)) (pre : IterationPre s h a) : State (P s h) :=
  let addr : Word (P s h) := ⟨(a.readReg r8).val - 1,
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) (a.readReg r8).isLt⟩
  let bit := a.heap.get ⟨addr.val, pre.address⟩
  let product : Word (P s h) := ⟨(a.readReg r9).val * 2, pre.multiply⟩
  let total : Word (P s h) := ⟨product.val + bit.val, pre.addition⟩
  let b := advance a r24 (boolWord (P s h) true) (pc s h site 6 (by decide))
  let c := setPC b (pc s h site 7 (by decide))
  let d := advance c r8 addr (pc s h site 8 (by decide))
  let e := advance d r10 bit (pc s h site 9 (by decide))
  let f := advance e r9 product (pc s h site 10 (by decide))
  advance f r9 total (pc s h site 5 (by decide))


/-- One descending Horner iteration executes exactly lt, branch, sub, load,
mul, add and returns to the same actual loop PC. -/
theorem iteration_segment (s : Sizes) (h : Admissible s) (site : Site)
    (code : Program (P s h)) (slots : Slots s h site code)
    (a : State (P s h)) (pre : IterationPre s h a)
    (hp : a.pc = pc s h site 5 (by decide)) :
    Segment code a [.lt, .branch, .sub, .load, .mul, .add]
      (iterationResult s h site a pre) := by
  let addr : Word (P s h) := ⟨(a.readReg r8).val - 1,
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) (a.readReg r8).isLt⟩
  let bit := a.heap.get ⟨addr.val, pre.address⟩
  let product : Word (P s h) := ⟨(a.readReg r9).val * 2, pre.multiply⟩
  let total : Word (P s h) := ⟨product.val + bit.val, pre.addition⟩
  let b := advance a r24 (boolWord (P s h) true) (pc s h site 6 (by decide))
  let c := setPC b (pc s h site 7 (by decide))
  let d := advance c r8 addr (pc s h site 8 (by decide))
  let e := advance d r10 bit (pc s h site 9 (by decide))
  let f := advance e r9 product (pc s h site 10 (by decide))
  let z := advance f r9 total (pc s h site 5 (by decide))
  have b24 : b.readReg r24 = boolWord (P s h) true := by
    simp only [b, read_advance_query]
    rfl
  have c1 : c.readReg r1 = a.readReg r1 := by
    simp only [c, b, read_setPC_query, read_advance_query]
    rfl
  have c8 : c.readReg r8 = a.readReg r8 := by
    simp only [c, b, read_setPC_query, read_advance_query]
    rfl
  have d8 : d.readReg r8 = addr := by
    simp only [d, read_advance_query]
    rfl
  have e9 : e.readReg r9 = a.readReg r9 := by
    simp only [e, d, c, b, read_setPC_query, read_advance_query]
    rfl
  have e2 : e.readReg r2 = a.readReg r2 := by
    simp only [e, d, c, b, read_setPC_query, read_advance_query]
    rfl
  have f9 : f.readReg r9 = product := by
    simp only [f, read_advance_query]
    rfl
  have f10 : f.readReg r10 = bit := by
    simp only [f, e, read_advance_query]
    rfl
  have dheap : d.heap = a.heap := rfl
  have h1 : step code a = ⟨.continued b, .instruction .lt .continued⟩ := by
    rw [fetched_slot s h site code slots a ⟨5, by decide⟩ hp, block_lt]
    simp only [execInstr, pre.above, decide_true]
    rfl
  have h2 : step code b = ⟨.continued c, .instruction .branch .continued⟩ := by
    rw [fetched_slot s h site code slots b ⟨6, by decide⟩ rfl, block_branch]
    simp only [execInstr, b24, boolWord, ↓reduceIte]
    rfl
  have hc : 1 ≤ (a.readReg r8).val := by have := pre.above; omega
  have h3 : step code c = ⟨.continued d, .instruction .sub .continued⟩ := by
    rw [fetched_slot s h site code slots c ⟨7, by decide⟩ rfl, block_sub]
    simp only [execInstr, c1, c8, pre.one, hc, ↓reduceDIte]
    rfl
  have h4 : step code d = ⟨.continued e, .instruction .load .continued⟩ := by
    rw [fetched_slot s h site code slots d ⟨8, by decide⟩ rfl, block_load]
    simp only [execInstr, d8, addr, pre.address, ↓reduceDIte, dheap]
    rfl
  have h5 : step code e = ⟨.continued f, .instruction .mul .continued⟩ := by
    rw [fetched_slot s h site code slots e ⟨9, by decide⟩ rfl, block_mul]
    simp only [execInstr, e9, e2, pre.two, pre.multiply, ↓reduceDIte]
    rfl
  have h6 : step code f = ⟨.continued z, .instruction .add .continued⟩ := by
    rw [fetched_slot s h site code slots f ⟨10, by decide⟩ rfl, block_add]
    simp only [execInstr, f9, f10, product, bit, addr, pre.addition, ↓reduceDIte]
    rfl
  exact Segment.cons h1 (Segment.cons h2 (Segment.cons h3
    (Segment.cons h4 (Segment.cons h5 (Segment.cons h6 (Segment.nil z))))))

theorem iteration_continuation (s : Sizes) (h : Admissible s) (site : Site)
    (code : Program (P s h)) (slots : Slots s h site code)
    (input : Fin (P s h).L → Bool) (a : State (P s h)) (pre : IterationPre s h a)
    (hp : a.pc = pc s h site 5 (by decide)) :
    WordRun.continueRun code input 6 (.guest a) =
      ⟨.exhausted (.guest (iterationResult s h site a pre)),
        guestEvents [.lt, .branch, .sub, .load, .mul, .add], 0⟩ :=
  segment_continuation code input (iteration_segment s h site code slots a pre hp)

/-- Exact state consequences, including read-only heap and every register
outside the four loop scratch registers. -/
theorem iteration_preserves (s : Sizes) (h : Admissible s) (site : Site)
    (a : State (P s h)) (pre : IterationPre s h a) :
    (iterationResult s h site a pre).heap = a.heap ∧
    (iterationResult s h site a pre).pc = pc s h site 5 (by decide) ∧
    ((iterationResult s h site a pre).readReg r8).val = (a.readReg r8).val - 1 ∧
    ((iterationResult s h site a pre).readReg r9).val = (a.readReg r9).val * 2 +
      (a.heap.get ⟨(a.readReg r8).val - 1, pre.address⟩).val ∧
    ∀ r : Fin 32, r ≠ r8 → r ≠ r9 → r ≠ r10 → r ≠ r24 →
      (iterationResult s h site a pre).readReg r = a.readReg r := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · simp [iterationResult, read_advance_query]
  · simp [iterationResult, read_advance_query]
  · intro r h8 h9 h10 h24
    simp [iterationResult, read_advance_query, read_setPC_query, Ne.symm h8, Ne.symm h9,
      Ne.symm h10, Ne.symm h24]


def exitResult (s : Sizes) (h : Admissible s) (site : Site)
    (a : State (P s h)) : State (P s h) :=
  let b := advance a r24 (boolWord (P s h) false) (pc s h site 6 (by decide))
  let c := setPC b (pc s h site 11 (by decide))
  let d := advance c r6 (a.readReg r11) (pc s h site 12 (by decide))
  advance d site.destination (a.readReg r9) (pc s h site 13 (by decide))

/-- At an exhausted descending cursor, actual control takes the false branch
and executes both exit moves before reaching the following instruction. -/
theorem exit_segment (s : Sizes) (h : Admissible s) (site : Site)
    (code : Program (P s h)) (slots : Slots s h site code)
    (a : State (P s h)) (hp : a.pc = pc s h site 5 (by decide))
    (he : ¬ (a.readReg r27).val < (a.readReg r8).val) :
    Segment code a [.lt, .branch, .mov, .mov] (exitResult s h site a) := by
  let b := advance a r24 (boolWord (P s h) false) (pc s h site 6 (by decide))
  let c := setPC b (pc s h site 11 (by decide))
  let d := advance c r6 (a.readReg r11) (pc s h site 12 (by decide))
  let z := advance d site.destination (a.readReg r9) (pc s h site 13 (by decide))
  have b24 : b.readReg r24 = boolWord (P s h) false := by
    simp only [b, read_advance_query]
    rfl
  have c11 : c.readReg r11 = a.readReg r11 := by
    simp only [c, b, read_setPC_query, read_advance_query]
    rfl
  have d9 : d.readReg r9 = a.readReg r9 := by
    simp only [d, c, b, read_setPC_query, read_advance_query]
    rfl
  have h1 : step code a = ⟨.continued b, .instruction .lt .continued⟩ := by
    rw [fetched_slot s h site code slots a ⟨5, by decide⟩ hp, block_lt]
    simp only [execInstr, he, decide_false]
    rfl
  have h2 : step code b = ⟨.continued c, .instruction .branch .continued⟩ := by
    rw [fetched_slot s h site code slots b ⟨6, by decide⟩ rfl, block_branch]
    simp only [execInstr, b24, boolWord]
    rfl
  have h3 : step code c = ⟨.continued d, .instruction .mov .continued⟩ := by
    rw [fetched_slot s h site code slots c ⟨11, by decide⟩ rfl, block_exit_cursor]
    simp only [execInstr, c11]
    rfl
  have h4 : step code d = ⟨.continued z, .instruction .mov .continued⟩ := by
    rw [fetched_slot s h site code slots d ⟨12, by decide⟩ rfl, block_exit_value]
    simp only [execInstr, d9]
    rfl
  exact Segment.cons h1 (Segment.cons h2 (Segment.cons h3 (Segment.cons h4 (Segment.nil z))))

theorem exit_continuation (s : Sizes) (h : Admissible s) (site : Site)
    (code : Program (P s h)) (slots : Slots s h site code)
    (input : Fin (P s h).L → Bool) (a : State (P s h))
    (hp : a.pc = pc s h site 5 (by decide))
    (he : ¬ (a.readReg r27).val < (a.readReg r8).val) :
    WordRun.continueRun code input 4 (.guest a) =
      ⟨.exhausted (.guest (exitResult s h site a)), guestEvents [.lt, .branch, .mov, .mov], 0⟩ :=
  segment_continuation code input (exit_segment s h site code slots a hp he)

theorem exit_preserves (s : Sizes) (h : Admissible s) (site : Site) (a : State (P s h)) :
    (exitResult s h site a).heap = a.heap ∧
    (exitResult s h site a).pc = pc s h site 13 (by decide) ∧
    (exitResult s h site a).readReg r6 = a.readReg r11 ∧
    (exitResult s h site a).readReg site.destination = a.readReg r9 ∧
    ∀ r : Fin 32, r ≠ r6 → r ≠ site.destination → r ≠ r24 →
      (exitResult s h site a).readReg r = a.readReg r := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · cases site <;> simp only [exitResult, Site.destination, read_advance_query] <;> rfl
  · simp only [exitResult, read_advance_query]
    rfl
  · intro r h6 hd h24
    simp [exitResult, read_advance_query, read_setPC_query, Ne.symm h6, Ne.symm hd, Ne.symm h24]

/-- The Horner invariant discharges both separate word checks, for every
v<2^W, including fields whose width equals W. A caller must establish the
actual heap bit and cursor/register invariants; no host parser is substituted. -/
theorem hornerPre (s : Sizes) (h : Admissible s) (a : State (P s h))
    (lo remaining value : Nat) (hv : value < 2 ^ s.W)
    (hlo : (a.readReg r27).val = lo)
    (hc : (a.readReg r8).val = lo + remaining + 1)
    (ha : lo + remaining < (P s h).M)
    (hacc : (a.readReg r9).val = value / 2 ^ (remaining + 1))
    (hone : (a.readReg r1).val = 1) (htwo : (a.readReg r2).val = 2)
    (hbit : (a.heap.get ⟨lo + remaining, ha⟩).val = bitValue value remaining) :
    IterationPre s h a where
  above := by rw [hlo, hc]; omega
  one := hone
  two := htwo
  address := by simpa only [hc, Nat.add_sub_cancel] using ha
  multiply := by
    rw [hacc, Nat.mul_comm]
    exact (horner_intermediates s.W value remaining hv).1
  addition := by
    have hb : (a.heap.get ⟨(a.readReg r8).val - 1,
        by simpa only [hc, Nat.add_sub_cancel] using ha⟩).val = bitValue value remaining := by
      simpa only [hc, Nat.add_sub_cancel] using hbit
    rw [hacc, hb, Nat.mul_comm]
    exact (horner_intermediates s.W value remaining hv).2

theorem horner_iteration (s : Sizes) (h : Admissible s) (site : Site)
    (code : Program (P s h)) (slots : Slots s h site code)
    (a : State (P s h)) (hp : a.pc = pc s h site 5 (by decide))
    (lo remaining value : Nat) (hv : value < 2 ^ s.W)
    (hlo : (a.readReg r27).val = lo)
    (hc : (a.readReg r8).val = lo + remaining + 1)
    (ha : lo + remaining < (P s h).M)
    (hacc : (a.readReg r9).val = value / 2 ^ (remaining + 1))
    (hone : (a.readReg r1).val = 1) (htwo : (a.readReg r2).val = 2)
    (hbit : (a.heap.get ⟨lo + remaining, ha⟩).val = bitValue value remaining) :
    let pre := hornerPre s h a lo remaining value hv hlo hc ha hacc hone htwo hbit
    Segment code a [.lt, .branch, .sub, .load, .mul, .add] (iterationResult s h site a pre) ∧
    ((iterationResult s h site a pre).readReg r8).val = lo + remaining ∧
    ((iterationResult s h site a pre).readReg r9).val = value / 2 ^ remaining := by
  dsimp only
  refine ⟨iteration_segment s h site code slots a _ hp, ?_, ?_⟩
  · rw [(iteration_preserves s h site a _).2.2.1, hc, Nat.add_sub_cancel]
  · rw [(iteration_preserves s h site a _).2.2.2.1, hacc]
    have hb : (a.heap.get ⟨(a.readReg r8).val - 1,
        by simpa only [hc, Nat.add_sub_cancel] using ha⟩).val = bitValue value remaining := by
      simpa only [hc, Nat.add_sub_cancel] using hbit
    rw [hb, Nat.mul_comm]
    exact horner_step value remaining

/-- Remaining zero takes the actual exit, including width-zero fields once
entry initialization has established their empty-field invariant. -/
theorem horner_exit (s : Sizes) (h : Admissible s) (site : Site)
    (code : Program (P s h)) (slots : Slots s h site code)
    (a : State (P s h)) (hp : a.pc = pc s h site 5 (by decide))
    (he : (a.readReg r27).val = (a.readReg r8).val)
    (value : Nat) (hacc : (a.readReg r9).val = value / 2 ^ 0) :
    Segment code a [.lt, .branch, .mov, .mov] (exitResult s h site a) ∧
    ((exitResult s h site a).readReg site.destination).val = value := by
  refine ⟨exit_segment s h site code slots a hp (by rw [he]; omega), ?_⟩
  rw [(exit_preserves s h site a).2.2.2.1, hacc, horner_final]

end Research.WordQueryDecoder
