# W011: fixed-word, finite-PC core contract

Status: **ACCEPTED FOR CORE IMPLEMENTATION ONLY**, after the independent
reviews and binding amendments in section 10. The later query comparison is
NOT ACCEPTED. No implementation success is asserted by this contract.
This is a new, separately named semantics proposal. W010's original whole-cost
proposal remains rejected. Neither this draft nor a later implementation changes
`Research.Machine`, its goals, or the accepted scopes of W005/W008/W009.

The proposed first claim is that one small instruction interpreter implements
the contract below. A later claim can compare linear and binary *query* programs
under this same contract. No ECDLP solver, whole-program BSGS cost, hardware speed,
bit-complexity bound, tape simulation, or dynamic-memory bound is proposed here.

## 1. Public profile, values, code, and input

Write `U = 2^W`. A profile consists of natural numbers `W,R,M,L,O` with proofs
of `W > 0`, `R > 0`, `M ≤ U`, and `L + O ≤ M`.

- `Word = Fin U`; a register index is `Fin R`.
- There are exactly `R` registers and exactly `M` mutable heap cells.
- The public input is exactly `L` bits, supplied as `Fin L → Bool`, not a
  variable-length list whose length is scanned for free.
- Heap addresses `0 .. L-1` initially hold these bits as words 0 or 1.
- The observable output is the fixed word vector at addresses `L .. L+O-1`.
  This is disjoint from the initial input region. All remaining cells are scratch.
  All heap cells, including input and output, may be modified by guest code.
- `M=0`, `L=0`, and `O=0` are allowed when the inequalities permit them.

A program is an immutable finite array of the instructions in section 2, of
length `N ≤ U`. The guest PC is a `Word`, initially 0. Instruction operands are
typed register indices; immediate words and control targets are `Word`s. Code
has no closures, host callbacks, proof-dependent behavior, group operation,
sorting, square-root, allocation, free, mark, or randomness instruction.

Every non-halting instruction has an explicit next target or branch targets.
There is **no implicit PC increment**. A target need not be less than `N`:
transferring to it succeeds, and the next positive-fuel fetch faults if the PC
is out of code. Thus an empty program faults on its first positive-fuel attempt.
Every PC remains representable even when it is invalid for this particular code.

`M ≤ U` makes every actual cell address representable. It does not make the
exclusive endpoint `M` representable when `M=U`. Likewise `N=U`, `L`, `L+O`,
lengths, and other public natural metadata are not automatically guest words.
Code that stores any endpoint, length, scalar order, table index, product, sum,
or midpoint must prove its own strict `< U` bound. There is no endpoint sentinel
in the core that silently bypasses these checks.

The source bit vector is read only by initialization, and is not accessible
through a second input oracle during guest execution. It is supplied by the
reviewed problem encoding. For a `CyclicProblem` adapter, a proved fixed-length
encoding theorem must construct that vector from `P.input d`; it must preserve
the actual bits and may not introduce a scalar, logarithm, inverse table, or
secret-dependent metadata. No raw-list-to-vector runtime conversion is included
in the first core. Any later variable-length input reader needs its own charged
protocol; it cannot inherit a free scan from this vector interface.

The abstract machine starts with a preloaded immutable program and externally
supplied input bits. Source input production, code loading/decoding, and the
physical representation of those media are outside its execution-unit claim.
Their lengths and description sizes are nevertheless reported. Guest copying
of *every* input bit into the heap is charged below. A later end-to-end claim
must state whether producing public parameters or loading code is paid.

## 2. Complete instruction syntax and denotation

Here `d,a,b` denote register indices, `v,t,t0,t1` immediate words, and `s[x]`
means a register value in the **pre-state**. Each arithmetic expression below is
an ordinary natural expression used to define checked-word semantics. It is not
permission for guest code to evaluate an arbitrary Lean function.

| Tag | Instruction | Effect if its checks pass |
|---:|---|---|
| 0 | `const d v t` | Write `v` to `d`; PC := `t` |
| 1 | `mov d a t` | Write `s[a]` to `d`; PC := `t` |
| 2 | `add d a b t` | Require `s[a]+s[b] < U`; write their sum; PC := `t` |
| 3 | `sub d a b t` | Require `s[b] ≤ s[a]`; write their difference; PC := `t` |
| 4 | `mul d a b t` | Require `s[a]*s[b] < U`; write their product; PC := `t` |
| 5 | `divmod dq dr a b t` | Require `s[b] ≠ 0`; write quotient to `dq`, then remainder to `dr`; PC := `t` |
| 6 | `eq d a b t` | Write 1 iff `s[a]=s[b]`, otherwise 0; PC := `t` |
| 7 | `lt d a b t` | Write 1 iff `s[a]<s[b]`, otherwise 0; PC := `t` |
| 8 | `load d a t` | Require `s[a] < M`; read heap at `s[a]` into `d`; PC := `t` |
| 9 | `store a b t` | Require `s[a] < M`; write `s[b]` to heap at `s[a]`; PC := `t` |
| 10 | `jump t` | PC := `t` |
| 11 | `branch a t0 t1` | PC := `t0` if `s[a]=0`, otherwise `t1` |
| 12 | `halt` | Terminate with the unchanged guest state |

All source operands, including a load/store address and the dividend/divisor,
are cached from the pre-state. Instructions do not interleave operand reads
with destination writes. A division by a nonzero word always produces words:
both natural quotient and remainder are `< U`.

Aliasing is allowed. Ordinary destinations may equal sources. For `divmod`,
both results are computed from the original dividend and divisor; writes are
quotient first, remainder second. If `dq=dr`, **the remainder wins**. This rule
also applies when either destination aliases the dividend or divisor. `store`
reads its address and value before committing either effect. These rules are
deterministic and require no alias-based fault or source restriction.

Fault reasons are exactly `invalidPC`, `addOverflow`, `subUnderflow`,
`mulOverflow`, `divisionByZero`, and `heapAddress`. Typed code cannot contain an
invalid register index or an immediate outside the word range. Instruction
checks do not validate a successor target against `N`. No arithmetic wraps,
saturates, or truncates on failure. Every instruction fault is atomic: registers,
heap, and PC are **identical** to the pre-state. Only the attempt ledger and
remaining fuel change. The fault records the current PC and reason.

## 3. Initialization is a metered phase, not a free state constructor

Initialization has exactly the following action sequence, in this order:

1. For `r=0 .. R-1`, clear register `r` to word 0.
2. For `a=0 .. M-1`, clear heap cell `a` to word 0.
3. For `i=0 .. L-1`, read source bit `i` and copy its 0/1 word to heap cell `i`.

Each action consumes **one** shared fuel unit and emits **one** setup event.
Consequently complete initialization uses exactly `I=R+M+L` model units:
`R` register clears, `M` heap clears, and `L` source-bit reads/copies. Input
cells are first cleared and then copied; these are two charged writes, even for
a false bit. Output and scratch zero initialization are included in `M`.
Initial PC 0, phase/cursor, fuel, and zero ledger are interpreter metadata;
their construction creates no additional charged action. The PC's guest
control updates thereafter belong to instruction attempts. This convention is
explicit, rather than an unreported register or heap initialization.

A partial initialization state has optional register/heap cells, all initially
uninitialized, and an action cursor. The cursor identifies the next action in
the public sequence above. Its bounds and advancement are interpreter control,
included in that action's one unit. Only after all actions finish is a guest
state exposed: all registers are 0, all heap cells exist, the input region
contains precisely the supplied bit vector, all other cells are 0, and PC is 0.
Guest instructions cannot run against partial initialization or inspect its
cursor. No uninitialized contents may seed later guest computation.

The empty sequence boundary is transitioned to execution without another
event/unit. Thus if exactly `I` units were supplied, initialization completes and
execution returns `exhausted` at PC 0, including when the first opcode is `halt`.
If fewer than `I` units were supplied, it returns `exhausted` with phase `setup`
and a cursor/partial-state diagnostic; it cannot return a guest output. Fuel is
not reset when initialization finishes. A caller may request diagnostics, but
cannot resume a claim with a fresh uncharged initialized guest state.

Physical creation of the interpreter's representations of optional cells,
arrays, proofs, and counters is not claimed to take these many hardware
operations. The specification charges the entire logical initialization even
if the host eagerly constructs zero-filled arrays. This is a declared abstract
unit convention, with an exact ledger, not a physical allocation theorem.

## 4. One-step execution, fuel precedence, and terminal outcomes

A standalone guest `step` has no fuel parameter: it inspects the current PC,
returns one of `continue nextState`, `halted state`, or `faulted reason state`,
and produces exactly one attempt event. `run` owns the single shared natural
fuel counter across setup and all guest steps.

The precedence for each still-running configuration is fixed:

1. If remaining fuel is 0, return `exhausted` with the current phase/state and
   ledger. Do **not** inspect code, charge an attempt, or recognize a halt.
2. Otherwise consume one unit. During setup, perform its next initialization
   action. During execution, attempt a fetch at the current PC.
3. If the execution PC is not `< N`, emit `invalidPC` and return `faulted`.
4. If it is in range, fetch the instruction once and emit its opcode attempt.
   A fetched `halt` returns `halted`, consuming this unit. Another instruction
   either commits its complete checked effect and continues, or returns its
   atomic fault, also consuming this unit.

On completion of the final setup action, the no-charge phase boundary from
section 3 applies before the next zero-fuel check. Already terminal outcomes
take no further actions: `run` returns them, rather than starting another fetch.
In particular, an explicit halt attempted with the last available unit succeeds;
merely transferring to a halt with no remaining unit exhausts.

Outcomes are distinct constructors: `halted`, `faulted`, `exhausted`. Each
contains the ledger and fuel remaining; fault includes its diagnostic and
unchanged guest state; exhaustion includes its phase and current state. A halt
is never inferred from invalid code or a missing search result. An opcode
success that transfers to an invalid PC is visible as a committed instruction;
only the following positive-fuel attempt faults.

For an initial budget `F`, every returned outcome must satisfy
`F = used + remaining`. Exhaustion has `remaining=0`. For an execution that
halts/faults under `F`, adding fuel leaves the terminal guest state, diagnostic,
event trace, and `used` unchanged, increasing `remaining` by the added amount.
There is no analogous promise that an exhausted run remains exhausted.

## 5. Events, counts, capacities, and the limits of a model unit

An event is one of `clearRegister r`, `clearHeap a`, `copyInput i`,
`invalidPC pc`, or `instruction opcode disposition`. The last disposition is
`continued`, `halted`, or `faulted reason`. No user-supplied event label exists.
The trace is a semantic specification; an implementation may accumulate the
equivalent finite ledger instead of allocating the trace at runtime.

The ledger counts the three setup kinds, invalid-PC attempts, and each of the
13 opcode attempts. It also counts completed loads and stores (only successful
ones). Required identities are:

```
setupUnits = clearRegisters + clearHeap + inputCopies
guestAttempts = invalidPCAttempts + sum opcodeAttempts
used = setupUnits + guestAttempts
completedLoads = load attempts with disposition continued
completedStores = store attempts with disposition continued
comparisonAttempts = eq attempts + lt attempts
initializedHeapWrites = clearHeap + inputCopies
totalCompletedHeapWrites = initializedHeapWrites + completedStores
```

Failed loads/stores still count an instruction attempt but perform no heap
access/commit. Halt counts an opcode attempt. Fault checks and PC fetch consume
the enclosing attempt unit; an invalid-PC attempt has no opcode count. Every
successful or faulting fetched instruction appears once, with no separate
unpriced branch evaluation. Ordinary arithmetic followed by a separate branch
requires both instructions and therefore two attempts. Initialization source
reads and guest heap reads are separately reported.

One guest unit is an abstract **checked-word instruction attempt**. It includes
one code fetch when valid, the fixed number of specified register accesses,
its checks, its specified word operation/heap access, and its control transfer.
`mul` and `divmod` each cost one such unit; this deliberately hides their
width-dependent physical implementation inside a declared word-operation unit.
The full opcode vector exposes this granularity. This contract assigns no
schoolbook weights and proves no bit-time or hardware-time result. Internal
comparison work, host array access, proof erasure, reference counting, natural
arithmetic, code fetch latency, and ledger maintenance do not gain an empirical
speed claim from this abstraction. A later bit-level refinement must pay for
them or explicitly justify its own unit convention.

Report resource capacity as `R` register words and `M` heap words, not peak live
words. All `M` cells exist after setup; there is no allocator/liveness claim.
Also report the `L`-bit external source, encoded code length, public descriptor
length, `N` instruction cells, and the guest PC word. Log/ledger/proof and
interpreter metadata are outside guest storage, explicitly not a total host
memory bound. Unbounded natural event counters belong to observation, not guest
registers; code cannot read them. No `≤2m` temporary-space theorem follows.

## 6. Actual finite, prefix-decodable serialization

Use `unary(n) = true^n ++ [false]` for **every** natural operand. Its length is
`n+1`; this is intentionally noncompact. Opcode tags 0 through 12 are exactly
four bits in little-endian binary. Tags 13 through 15 are rejected. Instruction
fields are encoded in precisely the order shown in section 2, with register
indices, word literals, and targets represented by their natural values. Field
counts for tags 0..12 are respectively `3,3,4,4,4,5,4,4,3,3,1,3,0`.

Encode a program by `unary(N)` followed by the encodings of its `N` instructions.
Decode the unary count, then exactly that many opcode/operand records, returning
the program **and unused suffix**. Missing terminators, short tags/records, and
unused tags fail. For a supplied profile, reject register operands `≥ R`, word
operands/targets `≥ U`, or `N>U`. Targets `≥N` remain legal code operands, as
specified above. These checks are static code admission/decoding, not an
uncharged guest input validator. Only admitted finite programs may execute.

Required proof: for every admitted program `c` and suffix `s`,
`decode(profile, encode(c) ++ s) = some (c,s)`. This establishes injectivity
and absence of codeword prefix ambiguity. The decoder must consume its input
structurally; no arbitrary host callback or inverse table is needed. Standard
list recursion and arithmetic suffice for a planned Std-only proof; none is
claimed complete in this draft.

Define **programBits** as the actual length of this encoding, not an assigned
cost. With instruction fields `f`, the exact formula is

```
programBits = (N+1) + sum_instruction (4 + sum_field (f+1)).
```

Public profile serialization is separately `unary(W) ++ unary(R) ++ unary(M)
++ unary(L) ++ unary(O)`. The complete manifest is that descriptor followed
by the encoded program; the same suffix-roundtrip obligation applies. Report
descriptorBits and programBits separately and their sum. Proof witnesses are
not serialized. The first comparison has no compactness or description-budget
claim; unary literals/targets can make programs very large. Any future table
exclusion requires the actual encoded-size theorem and an explicit budget.

## 7. Output validity, public budgets, and uniformity

The observable guest output of a **halted** execution is exactly the `O` words
in its fixed output region. Fault and exhaustion cannot be successes and do
not expose a certified output. An external specification predicate determines
whether halted words are correct; `halted` itself and any boolean written by
the program are not correctness certificates. Reading/checking that fixed
vector is a mathematical observer, outside execution units, and must not be
presented as an executed validation program.

For scalar output, a later adapter must prove these words are 0/1 and exactly
the reviewed fixed-width little-endian output bits. For lookup, the next-stage
profile will reserve two output words: `flag,payload`; validity requires
`flag∈{0,1}`, and `flag=0` requires `payload=0`. A found result must correspond
to an actual matching table entry with that payload; absence requires there
be no matching entry. Thus duplicate keys may return different legitimate
payloads. These are future refinement specifications, not trusted runtime
lookup primitives. Correct untouched zero output may be valid for an input;
there is no artificial "must write" condition. An incorrect or missing output
cannot pass the all-input specification merely because code halts.

Profiles, budgets, and code are fixed independently of the secret. In a fixed
instance comparison, both query programs use the same `W,R,M,L,O`, input
layout, and table values for each public instance; spare registers/cells are
still initialized and charged. A run cannot receive a secret-specific fuel,
capacity, output offset, program, initialized scratch value, or table.

A later family claim needs one fixed finite raw opcode/operand program, whose
serialization does not vary with size or scalar, and explicit public functions
`W(n),R(n),M(n),L(n),O(n),F(n)`. Its register/literal/target bounds must hold at
every claimed size. Typed proof witnesses may vary; executable operand values
may not. Public functions are resource budgets, not free guest initialized
data. All guest registers start at zero; any public number needed by the code
must arrive through the reviewed bit input or fixed code constants. The origin,
description, computation/validation cost, and admissibility of family parameters
remain separate obligations. The first core establishes no family theorem.

## 8. First implementation gate and required falsification tests

Before any Lean code: an independent reviewer must approve or revise this exact
contract, including the instruction table, typed admission, explicit next-PC
rule, setup actions, zero-fuel precedence, counters, output, and serialization.
It is insufficient to approve "some RAM" or just the intended asymptotic bound.
Coordinator records the disposition and a frozen version/digest. W010 is not
silently rehabilitated by approving W011.

After approval, the **first** code milestone is only: executable types, setup,
single-step core, one shared-fuel runner, serialization, and bounded tiny
programs. Generic proof obligations are preservation of word/state bounds;
complete setup contents and exactly `R+M+L` setup units; deterministic step;
atomic instruction faults; exact event/ledger identities and fuel conservation;
terminal-run fuel monotonicity; serialization suffix roundtrip/injectivity;
and output observation as specified. All kernel proofs; Std only; initially
`timeout 60` per compile/check. No compile or theorem success is asserted here.

Required tests, with exact traces/ledger and unchanged-state checks where
applicable, include:

1. Zero fuel during setup; exactly `I-1`, `I`, and `I+1` fuel. After setup,
   zero fuel at a halt and at an invalid PC exhausts without an attempt;
   positive fuel at a halt halts, at an invalid PC faults. Empty code is tested.
2. Jump/branch to an invalid but word-representable target: the transfer commits;
   zero remaining fuel exhausts; one further unit faults. No free halt peek.
3. `W=1`: false/true comparison values fit; `1+1` faults. General boundaries
   `U-1+0`, `U-1+1`, `0-0`, `0-1`, `(U-1)*1`, `(U-1)*2` where applicable,
   division by 0 and 1, and division of `U-1` by itself.
4. Destination/source aliases for arithmetic, load, and store; for `divmod`,
   distinct destinations, shared destination, and destinations equal to both
   sources. Example dividend 7/divisor 3 at `W≥3` must leave shared destination
   1 (the remainder), not quotient 2 or a result computed from an overwritten
   divisor. A zero-divisor alias case faults without any destination write.
5. Heap size 0, last valid address `M-1`, invalid address `M` when `M<U`, and
   `M=U` with address `U-1`. Do not construct a word equal to `U` to fake that
   last boundary test. Failed store/load count attempts, not completed accesses.
6. Exact opcode/event counts for a conditional loop, halt, fault, and exhaustion;
   adding fuel to a terminal run preserves its used cost/trace and final state.
7. Setup with true and false bits, nonempty output/scratch, and full input
   boundary: registers/output/scratch start zero, only the exact input region
   receives bits. All zero writes and input copies remain counted.
8. Serialization roundtrip with arbitrary suffix, all 13 tags, operand 0,
   largest legal words/register indices, malformed tags/truncated unary fields,
   and rejected `N>U`/operand bounds. Raw word/target value `U` must be rejected.
9. Halt with incorrect output fails the external correctness predicate; valid
   untouched zeros may satisfy it. Fault/exhaustion never become output success.

The **next separate stage** can encode the same table/query as input bits,
execute conventional linear and indexed binary search programs, and refine
their outputs to actual table membership/absence (`IndexedLookup` as the search
specification). Binary search must charge all loads, comparisons, address/index
arithmetic and branches in this instruction set, prove no overflow/fault, and
use matching capacities/initialization with linear search. Table preparation,
sorting, key creation, and encoding are explicitly excluded from a query-only
comparison until separately priced. No whole BSGS or tape claim follows.

## 9. Retained negative findings and remaining scope

W010's durable arithmetic falsifiers remain relevant: `q=2^k` does not fit in
`k` bits; non-reused allocation address growth is not peak live size; composite
moduli do not justify Fermat inversion; `qG=0` alone proves divisibility rather
than exact order. These are proposal-level arithmetic checks, not faults in an
implemented VM or accepted solver. Fixed capacity avoids the allocator issue
by removing allocation, not by proving the rejected address bound.

The wrapper and query theorems remain legitimate counts of their stated
operations. This new core would support stronger operational coverage only
after refinement proofs. No universal tape-lookup lower bound, cost conversion,
whole-solver proof, prime-field generalization, public-family validation,
amortized preprocessing claim, dynamic ownership protocol, bit-level arithmetic
cost, realistic memory latency, or hardware calibration is supplied here.

Source basis: the final coordinator/independent-disposition appendix in
`research/findings/W010-cost-proposal-review.md`, plus the unchanged
`Research/Machine.lean` and `Research/Problem.lean`. This is a proposed semantics
contract, not a literature claim. No new broad literature search was needed.

## 10. Binding review amendments and acceptance boundary

This section incorporates the two conditions of the independent Opus review
and the nonblocking operational clarifications from Astra. It is part of the
accepted core contract. The original reviewed draft is preserved in
`archive/W011-fixed-word-contract-r1.md`, SHA-256
`7a730bca3238729da82b397fd40f9071f6a0e66374e51c19afd3fed08ff05864`.

**A1 — events determine the ledger.** The ledger is defined as, or proved equal
to, the per-kind count of the semantic trace generated by `run`. Each event is
determined by an initialization action actually performed or an actual guest
attempt: either an invalid-PC fetch attempt or a fetched instruction and its
disposition, never an independently chosen cost label. Section 5 identities alone are insufficient. Add this trace
projection/refinement obligation to section 8 and its event-count test6. A
counter-only implementation is not a lossless representation of event order;
trace claims require a trace semantics or an explicit refinement theorem.

**A2 — claims start from raw input.** Every externally reported program cost
or solution correctness predicate is defined through the fresh entry point
`run profile code (input : Fin L → Bool) F`, paying setup and execution from
the same budget. Lemmas about `step` or hand-built initialized states are
internal refinement facts; they must never be presented as end-to-end program
costs or substitute for raw-input execution. No fresh initialized-state resume
bypasses setup. Core preservation/atomicity lemmas remain proof obligations.

For any later CyclicProblem adapter, require explicitly
`∀ d, (P.input d).length = L` and entry-by-entry equality of the input vector
with that list. The public profile and layout are fixed independently of d.

Terminal fuel monotonicity compares fresh runs with identical profile, code
and input at F and F+delta. Continuation lemmas separately account for existing
state/ledger. Add combined-precedence tests: arithmetic overflow with an invalid
successor faults arithmetically and retains the original PC; a successful store
followed by an invalid successor commits that store, and a later fetch fault
preserves it. Boundary tests must use representable operands and sufficient
registers; M-1 is a last-address test only when M>0.

**Core acceptance does not authorize the next query comparison.** Sections 7
and 8 describe a future direction only. Before that stage, a separate reviewed
contract must fix all of the following:

- Code, profile and fuel may depend only on declared public size parameters,
  never particular table contents or queries. The exact code-generation rule,
  uniformity/description policy and programBits for both programs are required;
  a precomputed decision tree must not be hidden behind fixed-instance timing.
- Exact fixed-width, fixed-bit-order encoding of header, complete key/payload
  table and query, with no rank/location hint. The table is query-independent.
- The same domain for both programs: numerically nondecreasing tables with
  duplicates, all present/absent queries, bounded keys and word-sized payloads.
  Sortedness is an explicit precondition until an executed check is supplied.
  Profiles, capacities and budget functions agree and are table/query-independent.
- Report setupUnits, guestAttempts and used together, plus the opcode vector.
  Producing/sorting/encoding a table may be excluded only explicitly; copying
  its bits during this contract's setup is always charged. Use matching exact
  or worst-case conventions. Do not claim a sublinear total run while paying
  linear setup, or compare guest-only counts with another program's total.
- Rank under declared guest/total attempt units, not only eq/lt opcode counts:
  other arithmetic can implement equality. These opcodes are not W008's
  whole-key comparisons. No multiplication of external-bit query timings by
  B silently prices BSGS's internally generated giant keys.

Any future solver/family claim also needs a justified word-width growth bound
or separately reviewed bit-cost refinement. Arbitrarily wide unit-cost words
can enable packed arithmetic that changes the meaning of an exponent claim.
No claim that all fixed-instance cost theorems are mathematically vacuous is
adopted: they can be valid within a declared program-size/advice model, which
must be explicit and suitable for the intended research comparison.
