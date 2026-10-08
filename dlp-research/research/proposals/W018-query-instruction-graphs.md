# W018: numbered packed-table query graphs

Status: **frozen design draft; NOT ACCEPTED for query constructors or results**.
Own artifact: this Markdown only. No Lean/query implementation, instruction
simulation, cost comparison, staging or commit was performed by the designer.

Target: amended W016 SHA-256
`3aa67dbd8e98de67878d978cb895f3d3763474546ff4ed5dc39c54ec517b92b5`,
especially section 9 and Opus C1–C14 in its finding. Target raw runner remains
the W016 recorded WordRun hash
`72ced59f481e8aef7f3340f918fa3d24ce8e9ff7ceb497d356f3cf31238b76e6`;
WordRunFacts supports future split/accounting proofs, not these unproved graphs.
Label any later results **packed-table search under common full packing**.

## Reading the tables and instantiation rule

Use exactly `WordCore.Instr` operand order. Every instruction row is complete:
ordinary final operand is its explicit next PC; `branch r f t` means PC f when
register r is **zero**, PC t otherwise; `jump t` has only its target; `halt`
has no operand. Registers are numbers 0..31; PC targets are numbers, not labels
resolved by a runtime function. These tables contain no implicit fallthrough.

Public `(W,m,k)` determines, exactly as in W016,

```
U=2^W; R=32; L=2*W+m*(k+W)+k; O=2;
B=L+2; A=B+2*m; M=A+4; I=32+M+L;
F=I+256*(L+4*m+32).
```

Only literals `W,L,B,A,A+1,A+2` below vary with sizes. Substitute these six
slots in one fixed skeleton; all register indices, instructions, code lengths,
control targets and other literals are unchanged. There is no branching on
sizes in instantiation, no data parameter, and no loop unrolling. The decoded
header supplies m/k. An admission proof permits lifting raw numeric operands
into the typed finite indices/words; it supplies no executable information.

Both arrays are the common rows 0..85 followed by exactly one search table.
Register 0 is never a destination. The seven first constants are in W016's
specified order. Workspace addresses A+1/A+2 are **inline const slots**, not
unstated arithmetic. Register allocation is W016's exact R32 assignment;
registers 28..31 are unused, and register 27 has the concrete role below.

## Common prefix: PCs 0..85 inclusive

| PC | Complete primitive instruction |
|---:|---|
| 0 | `const 1 1 1` |
| 1 | `const 2 2 2` |
| 2 | `const 3 W 3` |
| 3 | `const 12 B 4` |
| 4 | `const 13 A 5` |
| 5 | `const 26 L 6` |
| 6 | `const 6 0 7` |
| 7 | `mov 7 3 8` |
| 8 | `mov 27 6 9` |
| 9 | `add 11 6 7 10` |
| 10 | `mov 8 11 11` |
| 11 | `mov 9 0 12` |
| 12 | `lt 24 27 8 13` |
| 13 | `branch 24 18 14` |
| 14 | `sub 8 8 1 15` |
| 15 | `load 10 8 16` |
| 16 | `mul 9 9 2 17` |
| 17 | `add 9 9 10 12` |
| 18 | `mov 6 11 19` |
| 19 | `mov 4 9 20` |
| 20 | `mov 7 3 21` |
| 21 | `mov 27 6 22` |
| 22 | `add 11 6 7 23` |
| 23 | `mov 8 11 24` |
| 24 | `mov 9 0 25` |
| 25 | `lt 24 27 8 26` |
| 26 | `branch 24 31 27` |
| 27 | `sub 8 8 1 28` |
| 28 | `load 10 8 29` |
| 29 | `mul 9 9 2 30` |
| 30 | `add 9 9 10 25` |
| 31 | `mov 6 11 32` |
| 32 | `mov 5 9 33` |
| 33 | `mov 14 0 34` |
| 34 | `lt 24 14 4 35` |
| 35 | `branch 24 68 36` |
| 36 | `mov 7 5 37` |
| 37 | `mov 27 6 38` |
| 38 | `add 11 6 7 39` |
| 39 | `mov 8 11 40` |
| 40 | `mov 9 0 41` |
| 41 | `lt 24 27 8 42` |
| 42 | `branch 24 47 43` |
| 43 | `sub 8 8 1 44` |
| 44 | `load 10 8 45` |
| 45 | `mul 9 9 2 46` |
| 46 | `add 9 9 10 41` |
| 47 | `mov 6 11 48` |
| 48 | `mov 15 9 49` |
| 49 | `mov 7 3 50` |
| 50 | `mov 27 6 51` |
| 51 | `add 11 6 7 52` |
| 52 | `mov 8 11 53` |
| 53 | `mov 9 0 54` |
| 54 | `lt 24 27 8 55` |
| 55 | `branch 24 60 56` |
| 56 | `sub 8 8 1 57` |
| 57 | `load 10 8 58` |
| 58 | `mul 9 9 2 59` |
| 59 | `add 9 9 10 54` |
| 60 | `mov 6 11 61` |
| 61 | `mov 16 9 62` |
| 62 | `mul 25 14 2 63` |
| 63 | `add 25 12 25 64` |
| 64 | `store 25 15 65` |
| 65 | `add 25 25 1 66` |
| 66 | `store 25 16 67` |
| 67 | `add 14 14 1 34` |
| 68 | `mov 7 5 69` |
| 69 | `mov 27 6 70` |
| 70 | `add 11 6 7 71` |
| 71 | `mov 8 11 72` |
| 72 | `mov 9 0 73` |
| 73 | `lt 24 27 8 74` |
| 74 | `branch 24 79 75` |
| 75 | `sub 8 8 1 76` |
| 76 | `load 10 8 77` |
| 77 | `mul 9 9 2 78` |
| 78 | `add 9 9 10 73` |
| 79 | `mov 6 11 80` |
| 80 | `mov 17 9 81` |
| 81 | `store 13 4 82` |
| 82 | `const 25 A+1 83` |
| 83 | `store 25 5 84` |
| 84 | `const 25 A+2 85` |
| 85 | `store 25 17 86` |

The five 13-row decoder sites are 7..19 (m, width W), 20..32 (k, width W),
36..48 (key, width k), 49..61 (payload, width W), and 68..80 (query, width k).
Each site's first five actions set width r7, save original field start in r27,
compute **end** in r11, copy end into descending cursor r8, and clear r9.
Only r8, r10, r9 and r24 change during its bit loop. Thus r27 and r11 survive
all iterations. Its final two actions advance r6 to end and copy r9 to the
field's destination. There is no indirect call/return or shared dynamic return
register. A true loop test means start<cursor, so subtraction occurs only then.

For a width-zero key/query, the first loop guard branches straight to its
two-action exit. It loads no bit and subtracts nothing; r9 and the field value
are 0. For width W, descending order implements the actual little-endian
encoding and the final multiply/add produces at most U-1, not a weight U.

The record index r14 starts at 0. Guard 34/35 bypasses records at m=0.
For each record, r15 and r16 retain its decoded key/payload while 62/63 compute
`B+2*j` in r25. The two stores land there and at its successor. Row 67 increments
r14 once and transfers directly to 34, including after the last record.
There is no jump to a fictitious fallthrough row. The query site begins at 68.

PC 86 is the **state boundary**, not a PC-bearing trace event. Only row 85 in
the prefix targets 86; neither search body has an edge to 86 or any earlier
prefix row. Future proof must split actual continuations at this state. Do not
extract a boundary from opcode events or introduce a marker/reset.

## Sequential sorted search: PCs 86..109 inclusive

| PC | Complete primitive instruction |
|---:|---|
| 86 | `load 4 13 87` |
| 87 | `const 25 A+2 88` |
| 88 | `load 17 25 89` |
| 89 | `mov 14 0 90` |
| 90 | `lt 24 14 4 91` |
| 91 | `branch 24 106 92` |
| 92 | `mul 25 14 2 93` |
| 93 | `add 25 12 25 94` |
| 94 | `load 15 25 95` |
| 95 | `eq 24 15 17 96` |
| 96 | `branch 24 97 100` |
| 97 | `lt 24 15 17 98` |
| 98 | `branch 24 106 99` |
| 99 | `add 14 14 1 90` |
| 100 | `add 25 25 1 101` |
| 101 | `load 16 25 102` |
| 102 | `store 26 1 103` |
| 103 | `add 25 26 1 104` |
| 104 | `store 25 16 105` |
| 105 | `halt` |
| 106 | `store 26 0 107` |
| 107 | `add 25 26 1 108` |
| 108 | `store 25 0 109` |
| 109 | `halt` |

The empty-table and above-query-key branches share the **same** absence exit
106..109. Equality uses 100..105, with r25 still the matching key address until
100 adds its payload offset. Both paths store flag and payload before a charged
halt. The equality success returns the first matching location by sequential
order; the payload value need not be that location. Row 98 continues only when
key<query, preserving the prescribed sorted early exit.

## Binary indexed search: PCs 86..114 inclusive

| PC | Complete primitive instruction |
|---:|---|
| 86 | `load 4 13 87` |
| 87 | `const 25 A+2 88` |
| 88 | `load 17 25 89` |
| 89 | `mov 18 0 90` |
| 90 | `mov 19 4 91` |
| 91 | `lt 24 18 19 92` |
| 92 | `branch 24 111 93` |
| 93 | `sub 21 19 18 94` |
| 94 | `divmod 22 23 21 2 95` |
| 95 | `add 20 18 22 96` |
| 96 | `mul 25 20 2 97` |
| 97 | `add 25 12 25 98` |
| 98 | `load 15 25 99` |
| 99 | `eq 24 15 17 100` |
| 100 | `branch 24 101 105` |
| 101 | `lt 24 15 17 102` |
| 102 | `branch 24 104 103` |
| 103 | `add 18 20 1 91` |
| 104 | `mov 19 20 91` |
| 105 | `add 25 25 1 106` |
| 106 | `load 16 25 107` |
| 107 | `store 26 1 108` |
| 108 | `add 25 26 1 109` |
| 109 | `store 25 16 110` |
| 110 | `halt` |
| 111 | `store 26 0 112` |
| 112 | `add 25 26 1 113` |
| 113 | `store 25 0 114` |
| 114 | `halt` |

Register 21 is hi-lo; 22/23 are distinct quotient/remainder destinations and
neither aliases its dividend or divisor. Row 95 computes mid=lo+(hi-lo)/2.
After equality fails, true key<query at 102 chooses 103 (lo:=mid+1), and false
chooses 104 (hi:=mid). This is exactly the `IndexedLookup` midpoint and
equals-then-less rule. Future deterministic refinement must link payload and
probe count, not just existence. r25 remains the cached key address until a hit.
No payload load occurs on a miss. The interval guard precedes subtraction/read.

## Prefix end state and operational proof obligations

Let `c = 2*W+m*(k+W) = L-k`. From a fresh domain input, the prefix must reach
PC 86 with the following state; this characterization is a **proof target**,
not a supplied theorem. Every register/cell starts from W011's charged setup.

| Registers | Required values at PC 86 |
|---|---|
| 0,1,2,3 | 0,1,2,W respectively |
| 4,5,6,7 | m,k,L,k respectively |
| 8,9,11 | c,x,L respectively |
| 10 | x mod2 if k>0; otherwise last payload mod2 if m>0; otherwise 0 |
| 12,13,14 | B,A,m respectively |
| 15,16 | last key/payload if m>0; otherwise 0,0 |
| 17 | x |
| 18..23 | 0 |
| 24,25,26,27 | 0,A+2,L,c respectively |
| 28..31 | 0 |

Heap `[0,L)` is exactly the source 0/1 bit words, unmodified. Output cells L
and L+1 remain zero. Packed cells B+2*j/B+2*j+1 contain the given record, and
A/A+1/A+2 contain m/k/x. A+3 remains zero. Thus every cell has a specified value;
no uninitialized or hidden advice remains. For m=0,k=0 the last loaded bit is
the low bit of the k header (0), explaining r10 rather than assuming it zero.

Prove decoder contents by descending source indices. Preserve r0, source cells,
public constants, prefix bounds and register liveness. For record j<m,
`2*j < 2*m`, `B+2*j+1<A<M`, and j+1≤m<U. For decoder width w≤W,
its end≤L<M and the bit-loop accumulator doubling/addition is `<U`.
Workspace constants A+1/A+2<M, and output L+1<M. Binary lo≤hi≤m and lo<hi
imply mid<hi≤m and mid+1≤m<U. Exclusive endpoint M is not stored as a word.

Prove common instruction-prefix equality and common actual prefix traces.
The continuation split must characterize a,t_prefix,s_prefix, with PC86 in
s_prefix and
`continueRun code input (a+b) (.guest initialized) = prependTrace t_prefix
  (continueRun code input b (.guest s_prefix))`.
Then connect that split to fresh `run`, including the actual setup trace and I.
Search-entry loads are **not** part of the prefix. No event claims rely on PC
information absent from WordCore.Event.

## Code admission and minimum-width design evidence

Exact static counts from the numbered tables are **Nlin=110** and **Nbin=115**.
All targets lie within their respective arrays: largest linear target 109,
largest binary target 114. All register operands are <32; all fixed word
literals are 0,1,2. The common prefix occupies exactly 86 instructions.

Use the decidable intersection of W016's numerical conditions and **both**
tables' length/all-word-operand checks; do not admit one program separately.
The design predicts the simplified common admission

```
W≥7 ∧ k≤W ∧ M≤2^W ∧ m<2^W ∧ k<2^W,
```

because 115≤2^W forces W≥7, while W≥7 makes 2, all targets ≤114 and W
representable. All six public literal slots are `<M≤U` or bounded by W<U.
This equivalence, its decidability, and witnesses remain **unproved until Lean**.
It concerns these exact graphs, not a minimum width for every query algorithm.

The following arithmetically checked design witnesses satisfy numerical bounds,
lengths and every listed operand; generic typed-admission proofs are still owed:

| W,m,k | L | M | U | Domain examples |
|---|---:|---:|---:|---|
| 7,0,0 | 14 | 20 | 128 | Empty, width-zero key, query0 absent |
| 7,0,7 | 21 | 27 | 128 | Empty, every query0..127 absent |
| 7,1,0 | 21 | 29 | 128 | Key0; every payload0..127; query0 present |
| 7,1,7 | 35 | 43 | 128 | Nonempty k=W, key/payload/query maximum127 |
| 7,2,1 | 31 | 41 | 128 | Keys[0,0], payloads[0,127], query0 present/query1 absent |
| 7,3,2 | 43 | 55 | 128 | Keys[0,2,2], query1 absent between; query2 duplicates |
| 7,6,7 | 105 | 123 | 128 | Largest m at W7,k7; boundary payload127 |
| 7,12,0 | 98 | 128 | 128 | M=U, last physical cell127 valid |

At W7,k7, m=7 yields M=139>128 and is rejected. At W7,k0, m=13 yields
M=137>128 and is rejected. W6,m0,k0 has ample numerical heap room but fails
both code-length checks. The empty width7 example permits exhaustive full-width
query testing; no blanket impossibility claim about such tests is justified.

## Manual path accounting, not verified execution cost

The following is a derivation from listed paths, **unverified until generic Lean
refinement/count proofs**. It is not an assigned ledger and not a performance
comparison. Any discrepancy with actual traces falsifies the derivation.

Each decoder invocation of width w executes its five entry instructions,
two loop-test instructions w+1 times, four bit-body instructions w times,
and two exit instructions: `9+6*w` attempts. There are 2*m+3 invocations
whose widths sum to L. Add seven initial constants, one record-index reset,
2*(m+1) record guards, six packing/increment instructions per record, and
five metadata instructions. Proposed exact common-prefix attempts are

```
a = 7 + 9*(2*m+3) + 6*L + 1 + 2*(m+1) + 6*m + 5
  = 6*L + 26*m + 42.
```

Proposed prefix opcode counts are const9, mov(12*m+19), add(L+5*m+3),
sub L, mul(L+m), lt(L+3*m+4), branch(L+3*m+4), load L, store(2*m+3),
and zero eq/divmod/jump/halt/invalidPC. Their sum is a. Source loads L and
packing/metadata stores 2*m+3 match W016. Setup events are not included in a.

For sequential search, four entry instructions precede the loop. Each visited
record uses two interval guards and five address/load/equality instructions.
Every smaller-key miss additionally uses two order instructions and one index
increment. A hit uses the six-instruction success exit; an above-query key uses
two order instructions and the four-instruction absence exit. Exhausting m
records adds a final two-instruction guard and that absence exit. Hence proposed
search attempts are `10*p+7` for a hit/above-query absence after p≥1 probes,
or `10*m+10` for end-of-table absence. In particular, empty-table search is10.
These are exact-path proof targets, not attained worst cases for every domain.

Binary has five entry instructions. Each probe uses two guards and eight
93..100 midpoint/address/load/equality instructions. A miss uses 101/102 and
exactly one of 103/104, three more instructions. A hit uses the six-instruction
success exit. Completed absence uses the final two guards and four-instruction
absence exit. Proposed search attempts are `13*p+8` on a hit (p≥1), and
`13*p+11` on absence (p≥0). Empty binary search is11. A miss strictly shrinks
the natural interval, so a coarse bound p≤m yields search≤13*m+11.
The logarithmic probe theorem is a later refinement obligation, not assumed
for budget feasibility in this manual argument.

Both proposed guest totals are at most
`a+13*m+11 = 6*L+39*m+53 ≤ 256*(L+4*m+32)`.
Thus the unchanged F looks sufficient after adding I, if all path/invariant
claims are proved. No Lean theorem, guest run, comparison sign/crossover,
hardware result, or whole BSGS bound is established by this inequality.

ProgramBits must still be computed from the actual tables using WordCodec's
unary fields and code-count prefix, including every register/literal/target.
Descriptor and fuel lengths remain separate. No code-size cost is hidden in
the path derivation, and no cost ranking can use these bounds before proof.

## Review gate, recorded drafting issues, and next distinct steps

During manual numbering, the record body ends at67 and branches back to34:
the query begins at68, **not69**. That numbering adjustment was resolved before
freeze; no executing program or experiment failed. Success/absence targets
were assigned only after their shared-exit rows were fixed. No other design
failure, Lean compile or runtime test is reported by this artifact.

A read-only Python stdin check parsed the Markdown rows and verified 86 common
rows, contiguous complete ranges of 110/115 instructions, constructor arities,
all register bounds, all control edges, the single prefix exit85→86, no search
edge back to86/prefix, no r0 destination, allowed constant slots, and distinct
divmod destinations. It also checked all eight listed admission examples against
every listed literal/target and the code lengths. All checks passed. Formatting
checks passed. This is static design/arithmetic evidence, **not** a query
implementation, execution test, typed Lean admission proof or semantic proof.

Independent review must check all rows/edges, branch polarity, register27/r11
liveness, pre-state source aliases, no r0 write, exact table/query decoding,
zero/full-width paths, record/interval guard safety, true payload addresses,
source/output separation, N/minimum-W reasoning, and manual accounting. Review
must disposition the exact graph hash before any query constructor is written.

After graph approval, separately implement the fixed skeleton and size-only
instantiation; prove common admission/witnesses/programBits; then derive generic
prefix contents/split and search correctness/termination/counts from the actual
WordRun semantics. No favorite table/width substitutes for universal admitted
input proofs. The independent data-encoding author owns a different file.

Full packing is a policy of these two prescribed programs, not a lower bound
on preprocessing. Streaming sequential and lazy binary decoding remain distinct
unreviewed challenges. No timing, winner, arbitrary-wide-word exponent,
RAM-to-tape conversion, or multiplying standalone costs by BSGS block count.
