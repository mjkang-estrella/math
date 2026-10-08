# W010: proposed whole-solver cost interpreter — NOT ACCEPTED

Date: 2026-10-07. This is the retained verbatim reviewer proposal, not an adopted
specification or verified claim. Independent challenge is required, especially
for mark/fuel consistency, address/width bounds, exact-order validation, and
asserted tape lower bounds. Existing wrapper counts retain their expressly
limited meaning; this proposal cannot retroactively turn them into full costs.

Provider: Factory Fable 5.1, completed read-only design round.
Request `ecdloop-w4-cost-ledger-fable-20261007-r1`; task ID
`node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-w4-cost-ledger-fable-20261007-r1`.

## Original reviewer report (claims pending challenge)

Design review complete. Below is the actionable design. I made no file edits and ran only read-only inspection (repo sources at `9667d72` plus the untracked `PointKey.lean`/`IndexedLookup.lean`, and the pinned toolchain's `Init/Data/Array/Sort/Basic.lean` and `Init/Prelude.lean` externs).

# Whole-solver cost semantics for sorted BSGS: design proposal

## 0. Verdict in one paragraph

Adopt a **deep-embedded, fuel-driven word-RAM interpreter** (`Research/WordRAM.lean`) as the single cost semantics for the sorted-BSGS reference baseline and every later candidate. Do not extend the current wrapper counters. All existing counts (`countedAdd` returning `(x, 1)`, `equalityTest`/`orderingTest` returning `(b, 1)`, `Baseline.Result.comparisons`) are author-supplied literals that the author's own code can bypass by calling `A.add` or `==` directly; nothing in Lean detects that. That is exactly the "free oracle behind a label" the brief forbids, and `RESEARCH_LOOP.md`/W005 already require counts to "arise from explicit primitives or a small state interpreter". A shallow monadic ledger cannot close the loophole (continuations compute for free, Lean lists store for free), so the interpreter is justified now, not later. The frozen tape `Machine`, `CyclicProblem`, `SolvesWithin`, and both goals stay untouched; the RAM layer is a separately reviewed replacement cost model, and I flag below why its results do not transfer to the single-tape goal.

## 1. Inventory of what is currently counted versus free

| Artifact | Counted | Free / excluded | Loophole class |
|---|---|---|---|
| `Baseline.scan` | `point = target` tests (author `+1`) | `next`, equality internals | literal count |
| `OrbitArithmetic.buildFrom` | direct `countedAdd` calls = m | `orbit P 1` evaluates `P.next` (a coordinate add) per step, consing, scalars | literal count; generator oracle |
| `BSGS.search`/`solve` | nothing | lookup, `A.add`, `A.neg`, `%`, list traversal | uncounted |
| `IndexedLookup.search` | probes, eq calls, lt calls (author `1`s) | key creation, `entries[mid]` access, `Interval.mid` arithmetic, fuel | literal count; array access assumed O(1) |
| `PointKey.coordinateKey` | nothing | `1 + 5*x + y` | uncounted |
| W004/W006 Python | API adds, eq/lt (aggregated), sort compares | field ops, `pow(…,-1,p)`, slicing copies, allocation, memory | mixed units |

Two facts about Lean `Array` matter for the "formal vs physical" distinction the brief asks for:

- Definitionally, `Array α` is a wrapper around `List α`; `entries[mid]` in `decide +kernel` is a list traversal. O(1) indexing exists only in the compiled runtime via `@[extern "lean_array_fget"]`. Neither is a cost model; W008's probe count is fine as a probe count but can never be whole-solver evidence.
- The pinned `Array.mergeSort` (4.34.1) is top-down over `Subarray` slices and allocates a fresh `emptyWithCapacity` accumulator per merge, appending with `push`. Its peak live storage is not two buffers, and `push`'s in-place behavior depends on runtime reference-count uniqueness, which is unobservable in Lean semantics. So the W005 "≤ 2m slots" target cannot be inherited from `Array.mergeSort`; the sort must be written in the RAM language.

## 2. Why an interpreter now (and what it does not claim)

Why now:
1. Closes the literal-count loophole by construction: the only way a program touches data is through `Prim` constructors executed by `exec`, which records them.
2. Closes the generator-oracle gap: the program receives only the input bits (`P.parameters ++ encodePoint Q`), parses `p,a,b,Gx,Gy,q`, and computes every addition itself. `P.next`/`orbit P 1` do not exist inside the model.
3. Closes W005's open items by construction: fixed register file (`Fin R`) ⇒ no unbounded Lean-side storage; explicit `alloc/free` ⇒ peak words; explicit `load/store` ⇒ copies are visible; no recursion in the syntax ⇒ no stack; faults on overflow ⇒ the width analysis becomes a theorem obligation rather than a remark.
4. Same shape as the frozen `Machine.run` (global fuel, `Option` on fault/exhaustion, I/O as 0/1 cells at address 0), which is the right shape for a later RAM→tape simulation theorem.
5. Candidates become comparable: every candidate is a `Cmd` under the same `Params`, `Weights`, input layout and output convention.

What it does not do: it is not the tape model, not bit complexity (bit weights are a declared schoolbook assignment), not hardware, not a generic-group model, and it proves nothing about secp256k1 or any family. It yields no speed, novelty or "sqrt total work" claim; the honest shape of the baseline bound is $\tilde O(\sqrt q)$ word operations with explicit log and width factors, with table preprocessing paid per target.

Trade-off accepted: deep embedding makes generic proofs heavier than W007's functional proofs. Mitigation is staging (Section 9): instance-level theorems by `decide +kernel` evaluation of the interpreter first, generic invariants second, with a runtime sortedness self-check as an intermediate honest device.

## 3. Semantics specification (`Research/WordRAM.lean`)

### 3.1 Parameters and state

```lean
structure Params where
  W : Nat   -- word width in bits; every register/memory value is < 2^W
  R : Nat   -- register-file size, fixed per program family

abbrev Reg (P : Params) := Fin P.R

structure State (P : Params) where
  regs : Reg P → Nat
  mem  : Nat → Option Nat   -- none = unallocated; some v with v < 2^W
  brk  : Nat                -- bump pointer; addresses are never reused
  live : Nat                -- currently allocated words
```

No address reuse keeps proofs simple; `peak` is what the ledger reports, and `free` still lowers `live`, so release is accounted.

### 3.2 Primitives (the complete granularity)

```lean
inductive Prim (P : Params)
  | const  (dst : Reg P) (v : Nat)          -- fault if 2^W ≤ v
  | mov    (dst src : Reg P)
  | add | sub | mul (dst a b : Reg P)       -- fault on overflow (add/mul) or underflow (sub)
  | divmod (q r a b : Reg P)                -- fault if regs b = 0
  | cmpEq | cmpLt (dst a b : Reg P)         -- dst := 0 or 1
  | load   (dst addr : Reg P)               -- fault if mem addr = none
  | store  (addr src : Reg P)               -- fault if mem addr = none
  | alloc  (dst len : Reg P)                -- zero-fills len words, charges len; dst := base
  | free   (base len : Reg P)               -- live -= len; cells become none
  | mark   (label : Nat)                    -- weight fixed 0; no state effect; trace only

inductive Cmd (P : Params)
  | prim  (p : Prim P)
  | seq   (c₁ c₂ : Cmd P)
  | ite   (flag : Reg P) (t e : Cmd P)      -- charges one branch
  | while (flag : Reg P) (body : Cmd P)     -- charges one loopTest per test; flag refreshed by body
  | halt
```

Rules that keep it honest:
- No group, field, modular-multiply, sqrt or sort primitive. Field multiply is `mul` then `divmod`; inversion is a Fermat loop; sorting is a program. `divmod` is the only "fat" primitive and is priced $W^2$ under bit weights.
- `mark` carries no weight and cannot change state or control. It exists only so the ledger can report sub-counts (`ecAdd`, `probe`, `sortCompare`) for falsification against W004/W006/W008 numbers.
- Macros (Lean functions producing `Cmd`) may take only static data that is fixed per program, never per input. Loops are never unrolled over `m`, `q` or `p`; `Cmd.descriptionBits` (Section 3.5) is the budget that catches unrolling or hidden tables.

### 3.3 Interpreter and ledger

```lean
structure Ledger where
  const mov add sub mul divmod cmp load store allocWords freeWords : Nat
  branches loopTests : Nat
  steps : Nat                 -- fuel consumed = prims + branches + loopTests
  peakWords : Nat
  marks : List (Nat × Nat)    -- (label, count); or Nat → Nat

def exec (P) : Cmd P → Nat → State P → Ledger → Option (State P × Ledger)
```

- Every executed `prim`, `ite` test and `while` test consumes one fuel and increments `steps`. Fuel 0 before a needed step ⇒ `none` (exhausted). Any fault ⇒ `none`. `halt` ⇒ `some`.
- Required basic theorems before freeze: fuel monotonicity (mirror of `Machine.run_mono`); `mark` preserves state and all ledger fields except `marks`; `peakWords` is monotone and bounds `live` at every intermediate state; value invariant `∀ r, regs r < 2^W` and `∀ a v, mem a = some v → v < 2^W` is preserved; `exec` is deterministic (it is a function, but state the extensionality lemmas simp needs).

### 3.4 Input/output convention (mirrors the tape exactly)

```lean
def initial (P) (input : List Bool) : State P   -- mem i = some (if input[i] then 1 else 0) for i < length; brk = live = length
def readOut (P) (s : State P) (w : Nat) : List Bool   -- cell i reads true iff mem i = some 1, i < w
def RAMSolvesWithin (Q : CyclicProblem) (P : Params) (code : Cmd P) (fuel : Nat) : Prop :=
  ∀ d : Fin Q.order, ∃ s L, exec P code fuel (initial P (Q.input d)) Ledger.zero = some (s, L) ∧
    readOut P s Q.outputWidth = bits Q.outputWidth d.val
```

One bit per word in the I/O region; the program parses with charged `load`/`add`/`mul` (shift by two is `mul` by constant 2). Output is written as 0/1 words at addresses `0..outputWidth-1`, as `Tape.read` does. The input region counts toward `peakWords`.

### 3.5 Program size

`Cmd.descriptionBits`: 3 bits per node tag, `2*log2(v+1)+1` per `const` immediate, `2*log2(r+1)+1` per register operand, mirroring `Machine.Instruction.descriptionBits`. A `RAMConcreteGoal Q P maxBits fuel` analogue of `ConcreteGoal` must be stated, so a fixed-instance program cannot hide a table of `q` constants.

### 3.6 Weights (parameterized, never calibrated here)

```lean
structure Weights where
  const mov add sub mul divmod cmp load store allocWord freeWord branch loopTest : Nat
def cost (w : Weights) (L : Ledger) : Nat := ...   -- linear; marks contribute 0
def unit : Weights                                -- all 1
def bitSchool (W : Nat) : Weights                 -- add/sub/cmp/mov/const/load/store/allocWord/freeWord := W; mul/divmod := W*W; branch/loopTest := 1
```

Every report lists the quadruple `(steps, cost unit, cost (bitSchool W), peakWords)` plus register file size `R*W` bits. No hardware weights are defined in the repository; the W006 rule stands (an inequality between event vectors is not a calibrated result).

## 4. The baseline program (`Research/RAMBSGS.lean`) and its widths

### 4.1 Layout and setup, all charged

1. Parse fixed-width fields `p,a,b,Gx,Gy,q` (3 bits each on SmallCurve) and `tag,Qx,Qy` from the input region. Field width is a program constant per instance (the W003 framing assumption, unchanged).
2. Validate: `p ≠ 0`; `Gx,Gy,Qx,Qy < p`; `G` and `Q` on curve ($y^2 \equiv x^3+ax+b$); discriminant $4a^3+27b^2 \not\equiv 0$. Faults (`none`) on failure. Not validated: that `q` is the exact order (would cost $O(\log q)$ additions via double-and-add; propose leaving it out of the baseline and recording this as a trusted public parameter, as the frozen `CyclicProblem` already does). The generator is never an oracle input: `P.next` has no RAM counterpart.
3. Compute `m = isqrt(q-1)+1` by charged binary search on squares (≤ W iterations of `mul`+`cmpLt`). `m` must be computed from `q`; adding `m` to the public parameters would be parameter advice.
4. Allocate four `m`-word segments: `keys0, idx0, keys1, idx1` (two parallel-array buffers for ping-pong merge). Total table memory $4m$ words; no packing of key and index into one word.

### 4.2 Width obligations (these become the no-fault theorem)

| Quantity | Bound before reduction | Needed bits |
|---|---|---|
| field element | $< p$ | $\lceil\log_2 p\rceil$ |
| `mul` product before `divmod` | $< p^2$ | $2\lceil\log_2 p\rceil$ |
| sums before reduction (`fadd`, `fsub` as `a + p - b`) | $< 2p$ | $\lceil\log_2 p\rceil + 1$ |
| key `1 + p*x + y` (infinity = 0) | $< p^2 + 1$ | $2\lceil\log_2 p\rceil + 1$ |
| `q`, `d`, `j` | $< q$ | $\lceil\log_2 q\rceil$ |
| `m`, `B = (q-1)/m + 1`, `i` | $m \le \lceil\sqrt q\rceil$, $B \le q$ | $\lceil\log_2 q\rceil$ |
| `i*m + j` before `% q` | $\le (B-1)m + m - 1 < q + m$ | $\lceil\log_2 (q+m)\rceil$ |
| addresses | $< \text{input} + 4m + \text{scratch}$ | $\lceil\log_2(\text{peak})\rceil$ |
| fuel/steps (not a word) | — | Nat, outside the machine |

SmallCurve numbers: $p=5$ ⇒ products $<25$, keys $<26$ (matches `PointKey.coordinateKey_lt`), $q+m \le 15$, peak $< 25+32+c$; `W = 8` suffices with margin, `R = 32` is ample. State `Params := ⟨8, 32⟩` for the instance and prove `noFault` under hypotheses $2^W \ge 2p^2$ and $2^W > q+m$ and $2^W >$ peak address, so the theorem is reusable for the other four synthetic curves ($p=211$: $W \ge 17$).

### 4.3 Group kernel as programs

- `fmulmod`: `mul` + `divmod` (2 prims). `faddmod`/`fsubmod`: `add`(+`add p`)+`divmod`.
- `finv`: Fermat $a^{p-2}$ by square-and-multiply over the bits of `p-2`, loop bounded by W tests; ≤ `2W` `fmulmod`. Uniform in `p` (no $a^3$ shortcut), so the program text is unchanged across the five synthetic curves.
- `ecAdd` and `ecNeg`: affine formulas exactly as `SmallCurve.rawAdd/rawNeg`, with the infinity tag in a register; emits `mark ecAdd` once per call.
- `keyOf`: `1 + p*x + y`, 0 at infinity.

Bridge lemma (finite, kernel-checked over all 26 raw points × 26): `exec ecAdd s = some (s', L)` with `s'` registers equal to `rawAdd`, and `L` exact per branch (infinity/vertical/tangent/secant have different counts; report all four, never a single number).

### 4.4 Table construction, sort, search

- Babies: start at infinity (key 0, idx 0); loop `j = 1..m-1`: `ecAdd` with `G`, store `(key, j)` into buffer 0; one more `ecAdd` to obtain `mG`; `ecNeg` for the stride. Exactly `m` `ecAdd` marks, matching W005's wrapper count but now including the generator additions.
- Sort: bottom-up iterative merge, run length $1,2,4,\dots$, ping-pong between buffer 0 and buffer 1, comparator `cmpLt` on keys (ties keep either payload; the preorder is on keys only, as Astra noted). Track the live buffer parity in a register. Comparisons $\le m\lceil\log_2 m\rceil$, moves $= 2m\lceil\log_2 m\rceil$ words (`load`+`store` each), no extra allocation. Optional charged self-check (Section 5).
- Giant loop: `γ := Q`, `i := 0`; while `i < B`: `keyOf γ`; half-open binary search over the live key buffer with the W008 probe structure (one `load`, one `cmpEq`, on failure one `cmpLt`; `mark probe`); on hit, `load idx`, compute `(i*m + j)`, `divmod` by `q`, write `outputWidth` bits to addresses `0..`, `halt`; else `ecAdd γ stride`, `i += 1`. On loop exit without a hit: `halt` with no output written (correctness theorem shows this branch is unreachable for orbit inputs).
- Release: `free` all four segments before the final `halt` so the terminal `live` equals the I/O region; `peakWords` still records the maximum.

## 5. Proof obligations and invariants (staged)

Stage I (instance, kernel): for the seven SmallCurve scalars and `m ∈ {1,3,7,8}`, `exec bsgs F input = some (s, L)` with `readOut = bits 3 d` and the full ledger quadruple recorded as theorem statements (`decide +kernel`). This gives falsifiable numbers immediately. Risk: kernel evaluation time; if `decide +kernel` exceeds the 60 s envelope at `W=8`, record `#eval` output as experiment evidence and reduce to generic lemmas rather than raising timeouts silently.

Stage II (generic, by induction on the interpreter):
1. `noFault`: under the width hypotheses of 4.2, no primitive faults. This is the width theorem.
2. `fuel`: an explicit `F(q, m, W)` such that execution halts with `steps ≤ F`. Target shape: $F \le c_0 + c_1 W \cdot \text{inputLen} + m\,(c_2 + \text{ecAddSteps}) + m\lceil\log_2 m\rceil c_3 + B\,(\text{keySteps} + (\lceil\log_2 m\rceil+1)c_4 + \text{ecAddSteps} + c_5)$ with each $c_k$ a literal, and `ecAddSteps ≤ c_6 + 2W·(mulmodSteps)`.
3. `content`: every stored entry in the live buffer is `(keyOf (orbit j), j)` for some `j < m` (permutation invariant). Needed for soundness via `BSGSArithmetic.recover`.
4. `sorted`: after the final pass the live key buffer is nondecreasing. Needed for completeness via `complete_digits` and the half-open search invariant (W008's `lo ≤ hi ≤ size`).
5. `peak`: `peakWords ≤ inputLen + 4m` (registers reported separately).
6. `descriptionBits bsgs ≤` a literal independent of `q`.

Intermediate honest device for 4: add a charged $O(m)$ linear sortedness check after sorting that faults if violated. Then completeness needs only "check passed ⇒ sorted", which is a short lemma, while the instance-level theorem shows the check passes. This does not remove the eventual obligation to prove the sort correct for the generic bound; it just lets Stage II.4 lag without an unsound gap.

## 6. Falsification tests and retained assumptions

Tests (each a kernel theorem or a `research_demo` executable check, recorded with exact commands):
1. `marks ecAdd = m + ⌊d/m⌋` for all seven scalars (W004 formula), and executable agreement on the four other synthetic curves by feeding their input encodings (no Lean curve proofs needed, since the program reads `p,a,b,G,q` from input).
2. `marks probe ≤ (⌈\log_2 m⌉+1) · (⌊d/m⌋+1)` and per-lookup `cmp = 2·probes − 1` on success (W008 invariants).
3. `marks sortCompare ≤ m⌈\log_2 m⌉`; ping-pong allocates nothing after setup (`allocWords = inputLen + 4m` exactly).
4. `peakWords = inputLen + 4m` exactly; terminal `live = inputLen`.
5. No-fault at the stated `W`, and a *negative* test: at `W = 4` on SmallCurve the `mul` in `fmulmod` faults (`exec = none`), showing the width obligation is real.
6. Negative model tests (W002 style): a program that `load`s past the input region faults; a "table" program with `q` `const` immediates exceeds the `descriptionBits` budget; `mark` with any label leaves `steps`, `cost` and state unchanged.
7. Cross-check against `scripts/bsgs_lookup_experiment.py`: adds and eq/lt totals must agree exactly after aligning definitions (Python aggregates eq+lt; Python's lookup is on tuple keys, the RAM's on packed keys, so only counts, not key values, are compared).

Retained assumptions (must appear in the record):
- Single-word field elements ($W \ge 2\lceil\log_2 p\rceil+1$); multi-precision is a later program-level refinement.
- `bitSchool` weights are a schoolbook assignment, not measured; `unit` weights hide the $W^2$ inside `divmod`, so both are always reported.
- Control costs are one unit per branch/loop test; fixed field widths in the input header; `q` trusted as the order; fresh table per target; deterministic worst case only (no randomness primitive yet; a future `rand` must read an explicit random-bit region, charged, with separate expected-cost semantics).

## 7. Bounds you may responsibly state, and comparisons that remain invalid

May state (after Stage II): "Under `WordRAM` with parameters `(W,R)`, the reference sorted-BSGS program solves every orbit scalar within `F(q,m,W)` steps, cost `unit`/`bitSchool` as explicit polynomials in $m$, $\lceil\log_2 m\rceil$, $B$, $W$, and peak `inputLen + 4m` words, with table construction and sorting paid per target." That is $\tilde O(\sqrt q \cdot \text{poly}(W))$, not $O(\sqrt q)$, not an exponent statement, and not a tape bound.

Remain invalid:
- **RAM steps vs frozen tape steps.** The frozen `Machine` is single-tape with unit head moves. A table of $m$ entries of $W$ bits spans $\Theta(mW)$ cells; each of $B$ lookups costs $\Theta(mW)$ head movement, so sorted BSGS on the frozen tape costs $\Theta(qW)$, no better than exhaustive scanning. A $q^{1/2-\varepsilon}$ RAM result therefore does not imply `ExponentBreakthrough`; only a proven simulation with its overhead does, and for memory-heavy algorithms that overhead is fatal. This is a property of the frozen goal, recorded here, not a proposal to change it.
- **RAM counts vs Shoup/Nechaev generic bounds.** Those bound group-oracle queries for generic algorithms over random encodings, in expectation. The RAM model sees coordinates and counts word operations. So neither direction is valid: no lower bound in `WordRAM` follows from the generic bound, and a program with fewer than $\sqrt q$ `ecAdd` marks contradicts nothing and proves nothing until its full quadruple is reported (the W004 lesson, generalized).
- **`ecAdd` mark counts vs total cost**, **`unit` vs `bitSchool`**, **per-target vs amortized**, **wrapper counts from W005/W008 vs RAM counts**: different units, never summed or substituted.
- Any transfer to secp256k1 or a growing family; the baseline is proved on a fixed instance and tested on five synthetic curves.

## 8. Loopholes and trade-offs to watch

- Static macro arguments: a `Cmd`-producing Lean function could specialize on `q`. Only `descriptionBits` plus review catches instance-specific tables; the family goal needs one `Cmd` for all `n`, which the current fixed-width header cannot yet express (W003 open item).
- `divmod` granularity: one `unit` step for a $W^2$-bit operation. Mitigated by always reporting `bitSchool`.
- `alloc` zero-fill: charged per word, so no free initialized memory; but a program could `alloc` a huge region and never touch it, inflating nothing but `peak`. Fine, since `peak` is reported.
- No address reuse: a long-running candidate that repeatedly allocates would see `brk` grow while `live` and `peak` stay honest; addresses may need more bits than `peak` suggests. Record `brk` too if candidates allocate in loops.
- Fuel is a Nat outside the machine; the proof must supply `F` as a function of public `q` only, never of `d`.
- Kernel evaluation cost of the interpreter may force `#eval`-only evidence for larger synthetic curves; label those as experiments, not theorems.
- Deep embedding slows generic proofs; the sortedness self-check (Section 5) is the pressure valve, not a replacement for the sort proof.

## 9. Milestone plan (bounded waves, disjoint ownership)

| Wave | Deliverable | Done when |
|---|---|---|
| A | `Research/WordRAM.lean`: types, `exec`, `Ledger`, `Weights`, `descriptionBits`, `RAMSolvesWithin`; theorems: fuel monotone, mark-inert, value invariant, peak bounds live; demo program `isqrt` kernel-checked for $q \in \{7,19,31,109,199\}$ | standalone compile ≤ 60 s, Astra read-only semantic review, then **freeze** |
| B | `Research/RAMField.lean`: `fmulmod/faddmod/fsubmod/finv/ecAdd/ecNeg/keyOf`; bridge to `rawAdd/rawNeg/rawKey` over all raw points; per-branch exact ledgers; generic `noFault` under width hypotheses | kernel theorems pass; negative `W=4` fault test passes |
| C | `Research/RAMTable.lean`: baby build, ping-pong merge, binary search, sortedness self-check; instance ledgers at $m \in \{1,3,7,8\}$; generic `content` invariant | tests 1–4 of Section 6 pass at instance level |
| D | `Research/RAMBSGS.lean`: parse, validate, `isqrt`, table, giant loop, output, release; `RAMSolvesWithin SmallCurve.problem ⟨8,32⟩ bsgs F`; `research_demo` prints quadruples for the five synthetic curves and cross-checks Python counts | test 7 agrees exactly; W009 record with the quadruple table |
| E | Generic `fuel`, `sorted`, `peak`, `descriptionBits` theorems; the explicit $F(q,m,W)$ | the Section 7 "may state" sentence is a Lean theorem |
| Deferred | RAM→tape simulation with stated overhead; amortized multi-target ledger; `rand` region and expected-cost semantics; multi-precision field programs | separate milestones, each reviewed before any comparison |

Suggested ownership: Wave A to one writer with the semantic freeze reviewed by a different model before Waves B–D start; B/C/D are disjoint files; coordinator integrates `Audit.lean`/imports. The W008 `IndexedLookup.lean` work remains valuable as the probe-structure specification for Wave C's search and should not be duplicated; its probe/equality/ordering invariants become the Stage II.4 search lemmas re-stated over the RAM buffer.

## Coordinator challenge and durable arithmetic falsifiers

The original report is not accepted as written. Its insistence on explicit
whole-program semantics is a plausible design direction, not a proof that the
existing explicitly scoped wrapper counts are invalid. An author could bypass
a wrapper in a different program; that motivates coverage/refinement proofs or
an enforced instruction language for full-cost claims. It does not invalidate
reviewed theorems counting the calls present in the actual accepted source.

Independent Sol review is in progress. Coordinator identified these issues for
challenge: inconsistent mark/fuel rules; unspecified free ownership/double-free
behavior; bulk allocation versus primitive steps; non-reused bump addresses;
word widths including q itself; primality and exact-order assumptions; program
encoding and label size; and an unsupported universal tape-complexity assertion.
No replacement semantics has been implemented or frozen.

Durable arithmetic command:

```
timeout 60 python3 scripts/cost_proposal_counterexamples.py > research/findings/W010-counterexamples.json
```

It passed and archived:

- For q=2^k, k=0..8, ceil(log2 q)=k bits cannot represent q; q.bit_length()
  supplies k+1 bits. Scalars below q and the parameter q need distinct bounds.
- With one initial word, allocate/free three words three times without address
  reuse: peak live words=4, terminal break=10, final last address=9. A three-bit
  word fits peak=4 but cannot address 9. Track maximum break/address separately.
- p=4,a=0,b=1,G=(0,1) satisfies the listed nonzero-modulus, coordinate, equation
  and nonzero-discriminant-expression checks. For element 3, the Fermat proposal
  gives 3^(p-2)=1 mod4 and product3, not inverse product1. Prime-field assumptions
  must be trusted/proved or checked explicitly; this does not contradict the
  existing prime F5 instance or authorize arbitrary composite-modulus inputs.
- In the abstract group Z/7, 14G=0 but G has order7. A single qG=0 check proves
  only divisibility; exact order needs additional conditions. This is not a
  counterexample to CyclicProblem, whose distinctness premise rules it out.

These checks inspect integer consequences of proposed formulas, not an actual
WordRAM interpreter, EC runtime, accepted Lean solver or physical performance.
The original proposal remains visible above so corrections are not hidden.

## Independent disposition: DO NOT ADOPT original proposal

Native Sol independently reviewed the full proposal and coordinator objections.
It rejects adoption as written and gives a qualified design pass to a narrower
finite-PC, checked-word, fixed-capacity interpreter only after an exact small-step
contract is independently frozen. No WordRAM code is approved by this record.

Corrections and retained qualifications:

1. A mark cannot both be a one-fuel primitive and preserve steps. Omit marks
   initially; later static labels could classify already-executed instructions.
2. AST composition needs one shared remaining fuel and unambiguous global halt.
   A finite PC and single-step execution avoid these unspecified conventions.
3. Ledger.zero has peak0 while initialized input has live>0. Input allocation
   cannot enter allocWords unless charged. Initialize/report registers, heap,
   input copy and enough output capacity explicitly.
4. Free lacks range/support/ownership/double-free semantics. Bulk allocation
   taking one instruction plus len initialization units is a legitimate declared
   abstraction, not inherently dishonest; its unit definitions must agree.
   Huge allocation does increase cost under the proposed per-word weights.
5. Bump address high-water and live capacity differ, as the durable example
   shows. Initial fixed capacity removes this particular ambiguity, but stored
   lengths/endpoints still need bounds beyond representable cell addresses.
6. q itself needs more bits than a scalar below q at powers of two; baby j<m
   need not be below q when m>q. W must be positive for bit1/comparison true.
   The i*m+j bound needs q,m>0, i<B, j<m. Midpoint/square/run-length/validation
   intermediates and sentinel addresses need separate no-overflow proofs.
7. qG=O alone gives divisibility, not exact order. Prime q plus nonzero G is
   one sufficient additional condition; composite q requires appropriate
   factor-based evidence. Prime p and nonzero denominator justify Fermat
   inversion. They can be proved preconditions for the fixed F5 instance,
   but arbitrary parsed parameters do not inherit them.
8. Zero scalar needs the tag0 infinity branch. Its padded coordinates (0,0)
   need not satisfy the affine equation. The three-bit parser cannot process
   all five Python curves unchanged.
9. An all-input theorem still checks correct output: a missing-result halt is
   not automatically an unsound proof. Operational failure should nevertheless
   be distinguished. SmallCurve's untouched parameter prefix encodes5, which
   coincidentally equals one secret's expected output; halt alone is inadequate
   evidence. Requiring a write is unnecessary if correct output is already there.
   Allocated finite memory also does not exactly mirror the tape's zero padding.
10. Copying parallel key/index records uses two loads and two stores per record:
    at least4m accesses per full pass, before any extra comparison reads. Different
    bottom-up/top-down merge sorts need not have identical comparison totals.
11. Instruction syntax needs an actual encoding for opcode discriminators,
    registers, immediates and branches. A size budget excludes a table only
    when its proved encoded size exceeds the specified bound. Three Cmd-tag
    bits do not encode all Prim variants and operands by themselves.
12. The universal Theta(qW) tape claim and 'fatal' overhead claim are withdrawn.
    Particular translations may incur large movement costs, but require a
    specified layout, head position, query path and implementation. No general
    lower bound follows from the report.

Sol consulted primary SEC1 §3.1.1.2.1 and HAC Fact2.127 for the order/field
qualification: https://www.secg.org/sec1-v2.pdf and
https://cacr.uwaterloo.ca/hac/about/chap2.pdf . Those sources were consulted by
that reviewer, not newly retrieved by coordinator. The arithmetic counterexamples
stand independently of those literature attributions.

Schoolbook-looking weights are assigned proxies until supported by a bit-level
refinement. Public deterministic widths/capacities are not automatically secret
advice: their origin, description, computation/validation and costs must be fixed.
The current wrapper theorems remain valid for their documented scopes.

## Narrow next-stage gate

Proposed next core: W>0,R>0,fixed heapCells<=2^W, typed checked words, finite PC
and code, explicit initialization charges, and distinct halted/faulted/exhausted
outcomes. Addresses, stored lengths and endpoints have separate bounds. Reads
use pre-state, faults are atomic, each attempted instruction has an explicit
charge including halt/fault, and invalid-PC/zero-fuel precedence is fixed.
No allocation/free/marks/group/sort/sqrt primitive initially. Capacity is reported
as capacity, not a dynamic peak-live theorem. Serialization and output conventions
must be specified before accepting program-size or solver claims.

A rigorous first comparison could implement linear and binary lookup under
these same instructions, charging address arithmetic, loads and control. It
must remain a query-phase result with table construction separately priced or
explicitly excluded. Whole ECDLP execution must later construct the table from
original public input. The accepted algebra/lookup proofs should serve as
refinement specifications, rather than be discarded or relabeled as full costs.

Independent native Astra separately reproduced the arithmetic script and
exact archived JSON: PASS for all four narrow falsifiers, no failed tests.
It emphasizes G=1 for the Z/7 example, and that composite element3 actually has
inverse3 while the proposed expression returns1. Neither review ran a VM or
established a hardware/tape bound. Sol made no file edits; coordinator records
both reviews and preserves the rejected original report above.
