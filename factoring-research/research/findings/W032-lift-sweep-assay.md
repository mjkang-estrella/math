# W032 lift-sweep assay: two finite negatives; third group budget-stopped

**Disposition: incomplete three-group diagnostic, with two completely exhausted
finite families and no proper factor. Verified complete factoring improvement:
NONE.** The sole frozen execution used exactly **20,000/20,000 declared arithmetic
events** and **0.238444 seconds rounded up**, including input verification,
diagnostic prime generation, candidate setup, comparisons, controls and run
recording. The event cap stopped the b=17 group during prime generation. It did
not reach that group's candidate or controls. There was no source error, failed
completed control, hard timeout, repair, retuning or second execution.

The [parent protocol](W032-lift-sweep-assay-evidence/inputs/research/findings/W032-lift-sweep-protocol.md)
and both targets were frozen before execution. The mathematical quotient and
sweep audits remain separate work; this assay neither duplicates nor accepts
their general proofs. The old scalar assay was not read, imported or rerun.

## Fixed groups and complete outcomes

- **b=9:** exact trial division selected p=521, q=541, N=281861. The candidate
  used R=5, m=11, a0=1 and all 12 initial points. All unit checks passed.
  The complete sweep retained 78 thresholds, 79 intervals and 79 maximal
  constant segments, covering all 281861 parameters. Its 75 distinct c values
  had maximum absolute bit length 10; c0=133. Every interval had gcd(c,N)=1.
  Length-weighted unit/zero/nonzero-full/proper totals were
  281861/0/0/0. Exact proper probability for this finite lift family is **0**.
  The diagnostic ordinary uniform-residue proper-gcd probability was
  **1060/281861**. This group consumed **9,330 events** and completed all
  prescribed controls and verification.
- **b=13:** exact trial division selected p=8209, q=8287, N=68027983. The
  candidate used R=7, m=15, a0=1 and all 16 initial points. All unit checks
  passed. The complete sweep retained 136 thresholds, 137 intervals and 137
  maximal constant segments, covering all 68027983 parameters. Its 130
  distinct c values had maximum absolute bit length 14; c0=-2252. Every
  interval had gcd(c,N)=1. Length-weighted unit/zero/nonzero-full/proper totals
  were 68027983/0/0/0. Exact proper probability for this finite lift family
  is **0**. The diagnostic ordinary uniform-residue proper-gcd probability
  was **16494/68027983**. This group consumed **9,989 events** and completed
  its four prescribed controls and verification. No scalar control was
  scheduled for this group.
- **b=17:** **stopped after 681 charged setup events**, at cumulative event
  20,000. The final event incremented the trial divisor from 111 to 113 while
  checking the candidate integer 131093. That integer's primality was not
  certified. No p, q, N or R was completed; candidate, all four direct
  controls, and diagnostic probability/verification remain explicitly
  **unstarted**. Its family probability and factor yield are unknown. No
  scalar control was scheduled for this group.

There were no initial proper/full gcd exits in the completed groups and no
proper sweep outputs to verify against hidden factors. Every successful gcd
operation, including guards, is in the event ledger. No factor caused an early
exit, and no probability is assigned to the unfinished third group. The two
recorded baseline fractions are analytic diagnostic reference quantities;
there were no random-gcd trials or matched factoring benchmark.

## Controls and coverage

For N=281861, the direct lower-polynomial controls at w=0, 1, 140930, 281860
returned exact normalized quotients **133, 133, 116, 133**, respectively. All
four matched the interval lookup. Each reevaluated all 12 actual unwrapped
points `a_i + 12*N^(2R-3)*w` at full lower precision.

For N=68027983, the controls at w=0, 1, 34013991, 68027982 returned
**-2252, -2252, 1452, -2252**, respectively. All four matched; each reevaluated
all 16 actual unwrapped points. The lower-polynomial controls reuse the frozen
coefficient data, Horner routine and signed weights. They independently
reevaluate the materialized lifted inputs instead of using the sweep formula;
they do not supply an independent coefficient or evaluator proof.

The **one independent original scalar control passed** for the first N at w=0,
at all 12 points. It computed original quadratic coefficient-pair powers modulo
N^(2R+3), exactly divided A by N², applied the checked unit normalization modulo
N^(2R+1), and extracted the canonical top digits. Its separate ordinary
difference table gave the filtered integer **108798213**, with residue
**281728 = -c0 modulo 281861**. This control consumed 3,835 events, including
its setup, powers, inverses, full widths and difference table. It uses neither
the lower-polynomial coefficients nor the candidate's binomial-weight filter.
No extra or adapted scalar control was run.

All completed quotient divisions, threshold crossings, interval adjacency,
coverage totals and carry bounds passed their recorded checks. The 216
intervals and their 216 maximal segments are retained separately. Each tied
threshold group is collected fully before changing c or computing its next
gcd. **No equal thresholds occurred in these two completed families**, so the
multiple-event tie path and zero-net tie merging received source inspection
only, not a numerical exercise. Their correctness remains an audit obligation;
no extra tie-producing case was selected.

R=1 was not evaluated: symbolically the lower polynomial is P_1=1, so the
order-three difference of its constant lower remainders and its carry quotient
are zero. The new numerical sweep uses only its stipulated R>=2 branch.

## Accounting and preserved execution

The [meter declaration](W032-lift-sweep-assay-evidence/METER.md) predates the run.
It individually charges arithmetic products, sums/differences, reductions,
quotients, bit lengths and mathematical comparisons. Powers use actual repeated
operations. Stable threshold sorting charged 391 comparisons in the first
group and 779 in the second. Primality testing used charged exact trial division;
generation cost 270, 1,003 and 681 events in the three groups. Coefficient
recurrence, Horner evaluation, unit guards, bounds, threshold crossing checks,
controls and probability fractions are in the same global meter.

Native gcd and inverse are explicitly declared primitives with all actual
operand/result widths; their internal Euclidean work is not separately counted.
List/index administration, distinct-value set hashing, JSON, clocks, memory,
instrumentation and integrity hashes are separately declared. Thus **these
events are not bit operations or an asymptotic cost benchmark**. The maximum
recorded operand/result width was **729 bits**. No full polynomial evaluation
or positive power was priced as one event. The implementation uses Horner,
not a fast multipoint routine.

The global operation vector is: 3,864 multiplies; 3,796 additions; 1,716
subtractions; 1,968 remainders; 668 floor divisions; 441 quotient/remainder
operations; 284 gcds; 22 inverses; 2,426 equalities; 2,691 strict comparisons;
1,472 non-strict comparisons; 434 absolute values; and 218 bit-length operations.
Every operand, result and width is retained, including the last successful
primitive. The denied next primitive was not executed.

The run started at **2026-10-09 05:55:11 UTC** (October 8 locally). The process
supervisor recorded 0.2378464009379968 seconds through child termination/output;
the externally captured total through supervisor recording was
0.23844374401960522 seconds. The frozen 60-second global limit reserves its
last second for terminal recording; this allowance was not approached. The
child's exit code **2** denotes the recorded cooperative event-budget stop;
the supervisor returned normally. Empty stdout/stderr files are preserved.
Administrative post-run reading/reporting/sealing performed no assay arithmetic.

The [ledger audit](W032-lift-sweep-assay-evidence/ledger-audit.json) found all
**20,000 event IDs contiguous**, all **1,180 records** parseable, matching
operation/phase/width/record totals, and all **23 frozen payloads unchanged**.
This was a structural and hash inspection, not numerical replay. All three
initial plans and terminal statuses, all partial prime work, and every stopped
or unstarted control are retained. Source stayed frozen after execution.

## Interpretation and handoff

The measured computation exhausts these first two fixed families without a
proper gcd. That is a finite negative for their selected depths and start,
not a global impossibility result. The three-case protocol remains incomplete;
it cannot be described as three exhausted failures or a complete pass. The
completed controls support the recorded finite implementation behavior but
do not prove the general identities, tie handling, or useful output supply.
No fitted exponent, independent-success model, novelty claim or factoring-time
gain follows. The exact failed yield premise in these two families is simply
that some attained carry has a proper common divisor with N: none did.

The parent should consume the separate mathematical audits and assess useful
output supply. A different paid selector or family would require its own
justification and authorization; no replacement is selected or executed here.
This delivery does not request or authorize a rerun of the frozen diagnostic.

All changes are confined to this report and the named evidence directory.
There was no delegation, install, commit, shared solver/Lean/STATE/task edit,
or project-check invocation. **The required project check remains parent-owned
after delivery.** [Read scope](W032-lift-sweep-assay-evidence/read-scope.json)
states excerpts and unchecked scope explicitly.

The complete pre-run [freeze manifest](W032-lift-sweep-assay-evidence/freeze-manifest.json)
has externally announced SHA-256
`8b7387c453d5824d3948d11d9f161c49c6eb64ce67673c5e6e033a3d604a305c`.
It includes the exact protocol/configuration, all three Python sources,
governing documents and accepted-interface snapshots. The
[raw events](W032-lift-sweep-assay-evidence/events.jsonl),
[records](W032-lift-sweep-assay-evidence/records.jsonl),
[complete status](W032-lift-sweep-assay-evidence/status.json),
[runner status](W032-lift-sweep-assay-evidence/runner-status.json) and
[external execution transcript](W032-lift-sweep-assay-evidence/external-terminal-transcript.txt)
retain the sole execution.

The [delivery manifest](W032-lift-sweep-assay-evidence/delivery-manifest.json)
seals this report and every evidence payload, excluding only itself and its
[terminal hash sidecar](W032-lift-sweep-assay-evidence/terminal-manifest.sha256).
Its exact hash is returned in the external terminal handoff. No payload is
amended after that seal.
