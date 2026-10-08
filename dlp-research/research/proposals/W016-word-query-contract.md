# W016: raw-bit sorted-table query challenge

Status: **ACCEPTED FOR DATA ENCODING AND NUMBERED-TEMPLATE DESIGN ONLY**,
after the binding independent-review amendments in section 9. No query
program, sufficiency theorem or comparison is accepted. W011 accepts the core only; its section 10 gates
remain binding. This challenge uses that separate word model and does not
change `Machine`, its goals, the public curve encoding, or W008/W009's counts.
`WordRun.lean` is inspected as the intended fresh entry point; its independent
implementation acceptance remains a prerequisite, not assumed by this draft.

The proposed result is a fair comparison of a conventional sequential search
and conventional indexed binary search on the **same** sorted table and query,
including their actual raw initialization and guest parsing/packing. Producing,
sorting, and encoding the source table are explicitly outside this challenge.
It is not a complete BSGS cost result, an ECDLP algorithm, or a speed claim.

## 1. Public sizes, identical capacities, and complete input domain

The only public size parameters are natural numbers `(W,m,k)`. Set

```
U = 2^W
R = 32
L = 2*W + m*(k+W) + k
O = 2
B = L+2                         -- packed table base
A = B+2*m                       -- four-cell workspace base
M = A+4 = L+2+2*m+4
I = R+M+L                       -- charged raw initialization
F = I + 256*(L+4*m+32)          -- common challenge fuel, not a proved bound
```

Admissible sizes satisfy `W>0`, `k≤W`, `M≤U`, `m<U`, and `k<U`, and admit
both programs under the exact template/operand conditions in section 5.
The last two numerical inequalities are explicit header representation checks;
they should also be proved consequences of the other numerical conditions.
Each profile is exactly `WordCore.Profile(W,32,M,L,2)`.

`F` is a fixed proposed **resource budget**, deliberately loose and the same
for both programs. It is not an assertion of measured cost, termination, or
sufficiency. Before acceptance of either implemented program, prove generic
sufficiency of this very `F` from its frozen instruction graph. Failure to fit
is a failed challenge obligation; increasing it requires a separately recorded
reviewed amendment. Never derive fuel from table contents, the query, observed
first-hit positions, or a previously measured run. Performance comparisons use
actual attempts, not this budget. No theorem about `F` is supplied here.

For each admitted size, input data are **all** arrays of length `m` of pairs
`(key,payload)`, with `key<2^k` and `payload<U`, numerically nondecreasing keys,
and **every** query `x<2^k`. Duplicates may have arbitrary different payloads.
There is no restriction to one table, present queries, a favored query interval,
or selected ranks. Keys need not be curve points. Sortedness is a mathematical
input precondition, not a free executed sort/check. No promise is made for an
arbitrary malformed `L`-bit buffer that fails this encoding/domain predicate.

The domain includes `m=0`, `k=0`, and `k=W` whenever size/code admission holds.
At `k=0`, all keys and the query are 0: an empty table has an absent result,
while a nonempty table has a present result. That is the entire width-zero key
domain, not a silently excluded absent-query case. At `k=W`, values through
`U-1` must work. Widths/table sizes failing public capacity/code admission are
outside this bounded-address model and must be reported as rejected sizes.

## 2. Exact bit encoding and heap layout

Use the existing `Research.bits width value`, fixed-width **little endian**.
The source bit list, in this exact order, is

```
bits W m ++ bits W k ++
  concat over j=0..m-1 (bits k entries[j].key ++ bits W entries[j].payload) ++
  bits k x
```

Its length is exactly `L`. The raw input vector is its entry-by-entry equivalent
`Fin L → Bool`. Require proved fixed length and index equality, not merely an
injective host data structure. The encoding carries the complete array in its
given order, both size fields, and the query. It carries no location/rank hint,
membership flag, matching payload, answer, search path, spare initialized data,
or table/query-dependent profile. Table encoding is independent of the query
except for the final query field. Prove roundtrip/injectivity on this fixed-size
data domain; no stronger claim about arbitrary variable-width encodings.

After charged `WordRun.run` setup, every source bit occupies **one word cell**
at `heap[0..L)`, containing only 0 or 1. Output is `heap[L]` (flag) and
`heap[L+1]` (payload). Both initially contain 0. Scratch cells are:

| Region | Contents after common guest packing |
|---|---|
| `B+2*j`, `j<m` | entry key as one word |
| `B+2*j+1`, `j<m` | corresponding payload as one word |
| `A` | parsed m |
| `A+1` | parsed k |
| `A+2` | parsed query |
| `A+3` | unused, remains initialized zero |

All `M` cells and all 32 registers are initialized/charged for **both**
programs, including unused cells/registers. Raw input remains unchanged by guest
code. No packed table is initially supplied and no host function populates
scratch. Packing must be executed by the common guest prefix below. This is
fixed capacity, not a peak-live or host-memory bound.

## 3. Common charged parsing/packing prefix

Both programs use the identical instruction-template prefix, with identical
public constants and control targets within that prefix. It parses m and k,
then **all** key/payload records, then x, in input order; stores every packed
key/payload and the three workspace metadata values; then enters search.
Even if the query would match the first record, neither may skip packing later
records. Table/query values are never inspected by the compiler.

Each fixed-width field decoder is a guest loop over its source bit cells.
With field start `c` and width `w`, set `end=c+w`, `p=end`, `acc=0`. While
`c<p`, decrement `p`, load its bit, execute checked `acc := 2*acc+bit` as a
`mul` and an `add`; after the loop, advance the next field start to `end`.
Thus a little-endian field is read from its most significant bit downward.
Width zero skips the loop and returns 0. No call to `WordCodec.parseBits`,
host `Nat` decoding, slice creation, table conversion, or bulk-copy primitive
is an executed guest operation.

For `w≤W`, the decoder invariant after h processed bits is
`0≤acc<2^h`. Before every doubling, `h<w≤W`, so the product is at most `U-2`
and the following bit addition is at most `U-1`. It must **not** maintain a
power-of-two weight and double that weight after the final bit: `2^W` is not a
word. Source bits stay 0/1 because they come from setup and are never overwritten.
Fields have distinct finite loop sites for header m, header k, repeated key,
repeated payload, and query; no indirect host call or unpriced subroutine return.

The header values are parsed and used for the loops/metadata. Their agreement
with public `(m,k)` is an encoding precondition to prove from the exact input;
there is no executed header/sortedness validator in this first challenge.
Outside-domain raw inputs may fault, exhaust, or halt incorrectly and obtain no
correctness claim. Public resource admission is not secret-dependent validation.

Before search, the prefix has executed exactly `L` raw-bit heap loads,
`2*m+3` packing/metadata stores, and no search/output operation. These are
**proof obligations about the eventual frozen source**, not assigned counters
or claims already established. The source contains no guest mark instruction.
Parsing versus search is observed using the fixed prefix-ending PC and the
first execution of it; static phase labels must be proved to partition actual
trace events. One may use internal state invariants to prove this partition,
but reported totals always start at fresh raw `run` and include that prefix.

## 4. Two search bodies and output validity

Search starts by guest loading m and x from `A` and `A+2`. Both bodies use
the same packed layout and compare a cached **key word**. A payload is read
only on equality, once, from the corresponding second cell. Address calculation,
loads, eq/lt, register updates and branches are separate charged instructions.

The **sequential sorted search** starts at `i=0`. While `i<m`, read its key;
test equality with x; if equal, read that record's payload and succeed. Otherwise
test `key<x`: if true increment i and continue, and if false return absence.
If i reaches m, return absence. This uses sortedness to stop on an above-query
key; it is not an artificially weakened full scan that ignores that information.
It returns the first matching record's payload when present.

The **binary search** starts at `lo=0, hi=m`. While `lo<hi`, compute
`mid=lo+(hi-lo)/2` using checked subtraction, `divmod` by 2, and addition.
Read/cache the key at mid once, test equality, and if equal read its payload
and succeed. On inequality test `key<x`: if true set `lo=mid+1`, otherwise
set `hi=mid`. Empty interval returns absence. Maintain `lo≤hi≤m`; no runtime
list traversal, slice/copy, linear scan, or external `IndexedLookup.lookup` call.
The quotient/remainder destinations in midpoint calculation are distinct.

Every exit writes **both** output words through guest stores, then executes
`halt`: success writes `(1,matchingPayload)`; absence writes `(0,0)`. These
fixed exit conventions remove accidental differences in write overhead, while
retaining W011's general rule that correct untouched output can be valid.
No search-result failure is encoded by invalid PC, exhaustion, or a free halt.

Correctness for each fresh run requires `WordRun.output` to return those two
words, with flag exactly 0 or 1. Flag 1 means there exists an actual array
**location** `j<m` with `entries[j].key=x` and the returned payload equal to
`entries[j].payload`. Flag 0 requires payload 0 and no matching key anywhere.
A payload is never assumed to be a location, rank, or scalar. With duplicates,
the two correct programs can return different payloads. They are compared on
the same input under this shared relational specification; their output bytes
need not coincide. A payload of 0 remains a successful result when flag is 1.

## 5. Code generation, admission, and no-advice rule

Only the 13 `WordCore.Instr` constructors are allowed. Programs are compiled
from fixed finite control graphs for the prefix and the two bodies just given.
Loops are branch/back-edge loops, **never** unrolled by m, k, table contents,
or a target value. The graph is fixed independently of `(W,m,k)` and data;
only the following literal substitutions may depend on sizes:
`W,L,B,A,A+1,A+2`, plus profile-dependent type witnesses. Constants 0,1,2 and
the fixed numbered register/PC labels are otherwise identical at every size.
The decoded header supplies m and k; these are not specialized lookup answers.

Register assignment is fixed: 0 zero, 1 one, 2 two, 3 W, 4 decoded m,
5 decoded k, 6 next input start, 7 field width, 8 field read cursor,
9 decoder accumulator, 10 loaded bit, 11 temporary/end, 12 B, 13 A,
14 record/sequential index, 15 cached key, 16 payload, 17 query, 18 lo,
19 hi, 20 mid, 21 interval length, 22 quotient, 23 remainder, 24 comparison,
25 heap address, 26 output base L, 27 saved field start, and 28..31 unused.
Any assembler aliases must be resolved to these indices, not arbitrary code.
Decode fields are separate template sites as specified, not runtime callbacks.

The common prefix first executes constants for registers 1,2,3,12,13,26,6
with values `1,2,W,B,A,L,0`, respectively. Register 0 stays the setup-proved
zero. Simple register assignment lowers to `mov`, literal assignment to
`const`, and each binary `+,-,*` to one checked `add,sub,mul`. A test lowers to
one `eq`/`lt` into register 24 and one `branch`. Division by 2 uses one
`divmod` into registers 22/23, followed by the specified use of the quotient.
Heap reads/writes use one `load`/`store` after explicit address calculations.
The decoder's accumulation is exactly `mul 9 9 2` then `add 9 9 10`.
`B+2*j` is explicitly a multiplication by register 2 and an addition of
register 12; the payload offset is another addition of register 1. Loop control
and exit targets are wired into the primitives' explicit next fields, with
`jump` where needed. No assignment expression or branch survives as a host
operation. Labels are numbered in fixed source-block order after this lowering;
the required numbered expansion resolves all edges before acceptance.

Before implementation acceptance, freeze a numbered expansion of both control
graphs into these instructions, including every next target, and the deterministic
assembler/literal-substitution rule. Each simple assignment/test/load/store in
sections 3–4 must expand to explicit primitive instructions; there is no new
semantic macro opcode. That expansion and its generic theorems must receive
independent source review. This draft freezes the admissibility policy and
algorithms; it does **not** pretend that unprovided instruction graphs or their
lengths have been verified. A materially different graph requires review.

Size admission additionally requires both expanded code lengths `Nlin,Nbin≤U`
and all substituted word/PC operands `<U`. Register indices are `<32`. These
are deterministic public-size predicates on the frozen templates. Both programs
must be admitted, or that size is rejected for the comparison. Code must not
read its own encoding or an external observer/counter. No table-specific
decision tree, target-specific constant, precomputed table summary, or program
chosen after examining input is admitted.

Report each program's actual `WordCodec.programBits`, its frozen instruction
count, descriptor length and total manifest length. Unary literals/targets are
intentionally noncompact; their entire encoded lengths count. There is no
unproved constant description bound or cryptographic family claim. Size-dependent
addresses may change programBits even though the control graph is fixed.
Also report the public fuel descriptor separately (for this draft, its unary
encoding has `F+1` bits); it is not packed into guest input or programBits and
is not an unreported answer/advice channel. Computing the public size/profile/
budget descriptors is excluded host preparation here, just as source encoding
is; no zero-cost family-parameter generation theorem is inferred.

## 6. Range proofs, common fuel, and comparison convention

Prove all endpoints and intermediates used as words strictly `<U`, including
`W,m,k,L,B,A+1,A+2`, source field ends, index increments, `2*j`, table address
plus payload offset, and `lo+(hi-lo)/2`. In this layout `M` itself need not fit:
it is never stored as a guest word. Actual addresses are at most `M-1`.
Since `L+2+2*m+4=M≤U`, the raw input endpoint L, packed endpoint A, output
addresses, and used workspace endpoints are strictly below U. Guard record
and interval reads so m=0 performs no table access. Prove field-width-zero
code never subtracts 1 from 0. Prove explicit program targets are valid on all
domain runs, and every checked operation/heap access succeeds.

The common budget F is used by both `WordRun.run` calls, with their same profile
and same raw bits. Prove both halt within F for **every** admitted table/query.
The proof must account for all prefix/field/record/search/control/exit actions;
counts detached from the final instruction expansion do not establish sufficiency.
Do not compare one program with a hand-built packed state or reset the runner
after preparation. Internal packed-state lemmas are allowed only as refinement
steps within the proved fresh-run execution.

For every run report actual `setupUnits`, `guestAttempts`, `used`, remaining
fuel, all 13 opcode counts, invalid-PC attempts, completed heap loads/stores,
programBits and capacities. A successful domain run has setupUnits exactly I,
invalid-PC attempts zero, and `used=I+guestAttempts`. Counts must be projected
from the actual `WordRun` trace. Report the common guest preparation segment
and search/exit segment separately if their trace partition has been proved.

Rank programs separately by actual **guestAttempts** and actual **used** on
the same inputs. Because I is identical, pairwise guest/total ordering should
coincide; prove this identity rather than omitting setup. Initially require
exact per-input ledgers. A worst-case comparison later requires separately
proved maxima or bounds with matching conventions: a loose upper bound for
one program is not another program's achieved worst case. Never sum maxima
of individual opcode classes taken at different inputs. Eq/lt counts are
diagnostics, not the sole ranking metric; equality can be implemented using
other arithmetic. No decoder/program unit is calibrated to CPU or bit time.

Raw setup is at least proportional to this complete bit input, and the common
packing prefix reads every bit again. A logarithmic search-body bound therefore
does **not** imply sublinear total fresh-run work. This challenge does not
silently amortize either setup or packing over multiple queries.

## 7. Proof milestones, falsifiers, and acceptance gate

The first implementation sequence, **only after new independent design approval**:

1. Freeze/independently inspect the numbered primitive templates and implement
   the exact data encoder, size admission, profile and two code constructors.
   Establish code/data independence, encoded length/index equality/injectivity,
   and actual programBits/descriptor/manifest formulas. No query-cost result yet.
2. Prove common-prefix raw-run refinement: actual setup contents, charged field
   decoding without overflow, full packed-table correspondence and invariant
   output/input/workspace separation. Prove prefix trace counts/phase boundary.
   If current WordRun lacks a generic setup-content theorem, prove it first;
   its existing setup-count/boundary theorems alone do not supply all contents.
3. Prove both search invariants, relational success/absence, no fault, termination
   and common-F sufficiency; connect binary results to the `IndexedLookup`
   specification, including actual matching location and duplicate payloads.
4. Prove exact fresh-run ledgers and the shared setup/packing partition; then
   reproduce bounded tests and review any comparison separately. A prototype
   at one size/table is evidence only, never generic completion of these steps.

Required falsification coverage includes empty table; k=0; k=W; all 0/all
maximum keys; payloads 0 and U-1; duplicates with distinct payloads; absent
below/above/between keys; all keys equal; query 0/U-1 when k=W; sizes around
powers of two; first/last matching locations; final source bit true and all
ones W-bit payloads; largest admitted m; rejected capacity/code sizes; input
endpoint versus actual last address; every decoder zero-width path; all legal
table/query values in selected bounded profiles. Independently enumerate
expected answers/actual matching locations rather than using the candidate's
search routine as the oracle. Include traces at F and larger fuel (terminal
monotonicity), insufficient setup/guest fuel, and count each halt explicitly.
Use the project's initial 60-second/one-million-event experiment envelope.

Falsifiers include any wrong/false absence, payload/location confusion, input
advice or data-dependent code/capacity/fuel, unmatched domains, a free packed
table, overflow at maximal encoded words, skipped setup/packing, an opcode
count detached from events, mismatched exact/worst-case comparison, or a claimed
generic theorem supported only by a favorite table/width. Failed obligations
are recorded; the accepted core/domain is not changed just to pass a program.

## 8. Connection to BSGS and explicit exclusions

W008 proves high-level indexed search correctness and logarithmic *wrapper*
counts. W009 accumulates those query counts in sorted BSGS while excluding
preparation, key/group arithmetic, memory and control. They can guide refinement
proofs; their counters are not these word-program attempts.

This standalone challenge receives a complete externally prepared table/query
bit buffer. Its paid setup/packing is deliberately visible. BSGS instead builds
a table from forward babies and generates successive keys internally. One
cannot multiply standalone fresh-query times by the number of giant blocks to
price BSGS; that would repeatedly charge external input/preparation and omit
other internal work. A later reviewed whole-program contract must construct,
key, sort, store and reuse the table; execute group arithmetic and giant-key
production; recover the scalar; and prove a separately justified cost bound.

No source generation/sorting/encoding cost, decoder code-loading cost, bit-level
arithmetic cost, array hardware latency, total host memory, amortized multi-target
claim, RAM-to-tape conversion, arbitrary-wide-word exponent improvement, or
transfer to cryptographic curves is provided here. Any future family claim
requires fixed public word-width growth/description/advice rules or a reviewed
bit-cost refinement. The code and declared size parameters remain public;
neither may encode the particular table or query.

Independent review must explicitly disposition all five W011/Opus query gates:
size-only code/profile/fuel; exact no-advice encoding; identical complete sorted
duplicate domain; identical raw setup with matching comparison conventions;
and ranking actual attempts/total units rather than eq/lt alone. This draft,
future templates, and final proofs each have their own acceptance boundary.
No query implementation or comparison is authorized merely by filing this draft.

Source basis: accepted W011 section 10 and its Opus/Astra findings; actual
WordCore/WordCodec/current WordRun; W008/W009 source and recorded exclusions.
No literature or novelty claim, and no new broad literature search.


## 9. Binding independent-review amendments and staged acceptance

The reviewed original is preserved at `archive/W016-word-query-contract-r1.md`,
SHA-256 `bd22c845c38d6d3c840affc217f6286fce74199865895c363176a3a413c97f4a`.
Native Astra and new-round Opus reviews both conditionally approve the policy
and next design stage. This section supersedes ambiguous wording above and
incorporates their conditions before any query implementation is accepted.

The target runner is committed in `4120ffc`, source SHA-256
`72ced59f481e8aef7f3340f918fa3d24ce8e9ff7ceb497d356f3cf31238b76e6`.
Its generic initialized register/input/rest/PC facts now exist. Changes to that
runner reopen any affected query-refinement obligations; no silent substitution.

**Authorized next stage:** implement data encoding/profile/admission support
and draft the two numbered primitive graphs. Before implementing query program
constructors, freeze and independently review those exact expansions, every
successor, and their common prefix range/entry point. No program correctness,
common-F sufficiency, comparison or speed claim is accepted at this stage.

1. Each code constructor must take only public sizes and admission proofs.
   Define one symbolic skeleton per algorithm and one non-branching-on-sizes
   instantiation using only the allowed literal slots. Prove the constructed
   code equals that instantiation. Keep the encoder/data argument separate.
   Prove encoding length L, entrywise equality with raw input and injectivity.
2. Define common admission as an executable decidable intersection of both
   frozen programs' length and operand conditions. After graph freeze, record
   its actual minimum W and prove admission witnesses covering empty/nonempty
   tables, k=0, nonempty k=W, duplicates and absence-capable domains. Numerical
   heap-capacity examples alone are not witnesses of code admission. Correctness
   universally conditional on admission cannot count as completion if this gate
   is missing. Admitted sizes have nonempty data domains (e.g. zero tables).
3. Numbered expansions settle register 27 usage, inline versus computed workspace
   addresses, absence-exit sharing and all decoder control. Register 0 stays zero;
   prove neither program writes it. Prove no guest store changes source [0,L),
   all input bits stay 0/1, all accesses/word operations and targets are valid,
   and both searches terminate within the unchanged proposed F for every input.
   A failed F obligation requires a recorded reviewed amendment, not silent
   adjustment. No actual instruction length, minimum W or sufficient F is yet known.
4. Use a new relational fresh-run output predicate, not a single fixed expected
   payload vector: duplicates may legitimately yield different payloads.
   Sequential search returns the first matching location; binary refinement
   must match IndexedLookup.lookup's deterministic midpoint/equality/order rule
   and payload exactly, with its query iterations linked to probes. The shared
   external found/absence specification still quantifies over actual locations.
5. Prove common-prefix instruction arrays identical and actual common-prefix
   traces identical from the same initialized state. Segment reporting is
   REQUIRED before any comparison prose. WordCore instruction events do not
   include PC, so the section 3 boundary is a property of the operational state,
   not something recoverable by reading an opcode trace. Prove a continuation
   split `continueRun (a+b) s = prependTrace t_prefix (continueRun b s')` at the
   actual intermediate guest state, and characterize a, t_prefix and s'. No
   invented PC event, guest marker or unpriced reset may replace that proof.
6. Prove the full fresh-run setup identity and `used=I+guestAttempts` for each
   accepted program. Generic accounting/split corollaries may support this,
   but must be connected to the actual run. Terminal can include faults in
   generic accounting; query correctness requires a proper halt as specified.
7. Label results **packed-table search under common full packing**. Mandatory
   full packing is the policy of these two prescribed programs, not a necessary
   preprocessing lower bound. Lazy binary decoding and early streaming linear
   search are excluded alternatives requiring separate reviewed challenges.
   Report per-input signs/crossovers from actual execution/proofs, not an assumed
   winner. Expected sequential wins on some inputs are reviewer hypotheses until
   measured/proved from the final graphs. Worst cases need matching extrema
   conventions; averages need an explicit distribution and exact computation.
8. Retain all declared exclusions and no word-width/bit/hardware/tape/exponent
   extrapolation. Program, manifest and fuel-descriptor lengths remain reported.
   No multiplication of fresh external-query costs prices internally generated
   giant keys in a whole BSGS program.

The initial finite test envelope does not justify saying all full-width tests
are impossible: an admitted m=0,k=W profile can permit exhaustive query tests.
Choose genuinely admitted bounded profiles and report exactly what was exhaustively
enumerated. Larger duplicate/full-payload domains may need selected boundary
experiments plus the generic proof; never relabel those samples as exhaustive.
No exact minimum W is guessed from an unprovided graph.
