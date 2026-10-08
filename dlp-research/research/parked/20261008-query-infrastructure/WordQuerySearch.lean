import Research.WordQueryCode
import Research.WordRun
import Research.IndexedLookup

/-! Conditional operational facts for the frozen binary search body. The
preconditions describe an already packed internal state. They do not establish
that a fresh run reaches that state or pay for packing. No whole-query result,
fuel sufficiency, comparison, hardware or ECDLP bound is asserted here. -/
namespace Research.WordQuerySearch

open WordCore WordQueryData WordQueryCode

/-- Every edge is an actual successful fetch/execute event, not an assumed
instruction macro. The list records actual opcodes in execution order. -/
inductive Segment {P : Profile} (code : Program P) :
    State P → List Opcode → State P → Prop where
  | nil (state) : Segment code state [] state
  | cons {state next last ops op}
      (edge : step code state = ⟨.continued next, .instruction op .continued⟩)
      (tail : Segment code next ops last) : Segment code state (op :: ops) last

theorem segment_continuation {P : Profile} {code : Program P}
    {state last : State P} {ops : List Opcode} (h : Segment code state ops last)
    (input : Fin P.L → Bool) (fuel : Nat) :
    WordRun.continueRun code input (ops.length + fuel) (.guest state) =
      WordRun.prependTrace
        (ops.map fun op => WordRun.Event.guest (.instruction op .continued))
        (WordRun.continueRun code input fuel (.guest last)) := by
  induction h with
  | nil => simp [WordRun.prependTrace]
  | cons edge tail ih =>
    simp only [List.length_cons, Nat.succ_add, WordRun.continueRun,
      WordRun.normalize, edge, WordRun.prepend, List.map_cons, ih,
      WordRun.prependTrace, List.cons_append]

abbrev QState (s : Sizes) (h : Admissible s) := State (profile s h.1)

def reg {s : Sizes} {h : Admissible s} (st : QState s h) (r : Fin 32) : Nat :=
  (st.readReg r).val

def cell {s : Sizes} {h : Admissible s} (st : QState s h)
    (a : Nat) (ha : a < s.M) : Nat := (st.heap.get ⟨a, ha⟩).val

/-- Data and source are explicit. Sortedness is deliberately separate: fetching
a midpoint requires bounds, not a sortedness hypothesis. -/
structure Packed {s : Sizes} (h : Admissible s) (d : Data s) (st : QState s h) : Prop where
  zero : reg st 0 = 0
  one : reg st 1 = 1
  two : reg st 2 = 2
  tableBase : reg st 12 = s.B
  workspace : reg st 13 = s.A
  outputBase : reg st 26 = s.L
  count : ∀ ha, cell st s.A ha = s.m
  query : ∀ ha, cell st (s.A + 2) ha = d.query.val
  keys : ∀ j : Fin s.m, ∀ ha,
    cell st (s.B + 2 * j.val) ha = (d.entries.get j).key.val
  payloads : ∀ j : Fin s.m, ∀ ha,
    cell st (s.B + 2 * j.val + 1) ha = (d.entries.get j).payload.val
  source : ∀ i : Fin s.L, ∀ hi,
    cell st i.val hi = if rawInput d i then 1 else 0

private theorem get_binary (s : Sizes) (h : Admissible s) (n : Nat) (hn : n < 115) :
    (binary s h).code[n]'(by rw [binary_size]; exact hn) =
      instantiateInstr s h.1 (binarySkeleton[n]'(by rw [binarySkeleton_size]; exact hn))
        (h.2.2.2 _ (Array.getElem_mem _)) := by
  simp [binary, instantiate, Array.getElem_pmap]

private theorem read_write {P : Profile} (st : State P) (r j : Register P)
    (v : Word P) : (st.writeReg r v).readReg j = if r = j then v else st.readReg j := by
  change (st.regs.set r.val v)[j.val] = if r = j then v else st.regs[j.val]
  simp only [Vector.getElem_set, Fin.ext_iff]

private def put {P : Profile} (st : State P) (r : Register P)
    (v target : Word P) : State P := { st.writeReg r v with pc := target }

private theorem read_put {P : Profile} (st : State P) (r j : Register P)
    (v target : Word P) : (put st r v target).readReg j =
      if r = j then v else st.readReg j := read_write st r j v

private theorem fixed_bound (s : Sizes) (h : Admissible s) (n : Nat) (hn : n < 115) :
    n < (profile s h.1).bound := by
  have hh := h.2.2.1
  rw [binarySkeleton_size] at hh
  exact Nat.lt_of_lt_of_le hn hh

private def pc (s : Sizes) (h : Admissible s) (n : Nat) (hn : n < 115) :
    Word (profile s h.1) := ⟨n, fixed_bound s h n hn⟩

private theorem step86 (s : Sizes) (h : Admissible s) (st : QState s h)
    (hp : st.pc.val = 86) (ha : (st.readReg (13 : Fin 32)).val < s.M) :
    step (binary s h) st =
      ⟨.continued (put st (4 : Fin 32) (st.heap.get ⟨(st.readReg (13 : Fin 32)).val, ha⟩) (pc s h 87 (by decide))),
        .instruction .load .continued⟩ := by
  rw [step_fetched _ _ (by rw [hp, binary_size]; decide)]
  have hc : (binary s h).code[86]'(by rw [binary_size]; decide) =
      Instr.load (4 : Fin 32) (13 : Fin 32) (pc s h 87 (by decide)) := by
    rw [get_binary s h 86 (by decide)]
    rfl
  simp only [hp, hc, execInstr]
  have ha' : (st.readReg (13 : Fin 32)).val < (profile s h.1).M := ha
  simp only [ha', ↓reduceDIte, Instr.opcode, Outcome.disposition, put]

end Research.WordQuerySearch
