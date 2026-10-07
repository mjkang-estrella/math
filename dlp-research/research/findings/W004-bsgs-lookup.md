# W004: naive BSGS lookup retains exhaustive equality work

Date: 2026-10-07. Status: independently reviewed finite experiment and limited
negative result. No new algorithm, asymptotic bound, or tape-cost result.

## Hypothesis and baseline

H: reducing generator-addition calls with baby-step giant-step (BSGS) suffices
to justify a square-root runtime claim even if table lookup is implemented by
linear search. Falsifier: linear comparison work remains proportional to q
when counted independently of additions. Compare exhaustive orbit scanning,
linear-table BSGS, and conventional ordered-table BSGS with construction and
sorting paid anew for every public key.

Primary algorithm source retrieved: [Handbook of Applied Cryptography, chapter
3](https://cacr.uwaterloo.ca/hac/about/chap3.pdf), algorithm 3.56 and its cost
discussion, p. 105. It specifies sorting (or hashing) the baby table and
distinguishes comparison, storage and group-operation costs. We implement
additive coordinate-group operations and explicit merge sort/binary search.
This is a conventional baseline, not a proposed novel attack.

## Parameters and reproducibility

`scripts/bsgs_lookup_experiment.py` uses exactly these (p,a,b,G,q) tuples:

- (5,2,1,(0,1),7), the existing Lean example;
- (17,2,2,(0,6),19);
- (43,0,7,(2,12),31);
- (101,1,46,(2,37),109);
- (211,0,2,(4,53),199).

The latter four were selected in a coordinator one-off Python enumeration:
for fixed p in [17,43,101,211], scan a then b ascending, skip zero discriminant,
enumerate all x,y in range(p), accept the first curve with prime point count
different from p, and choose its lexicographically first affine point. Primality
used trial division through isqrt. This selection is not a hard-family
construction and its cost is not a claimed solver cost. The committed script
revalidates p primality, discriminant, full point set and exact generator orbit
without relying on primality of q. It does not validate embedding-degree or
other cryptographic-admissibility conditions. No secp256k1 transfer is inferred
from the p=43 example's coefficients.

Exact command: `timeout 60 python3 scripts/bsgs_lookup_experiment.py` (exit 0).
For durable output: same command redirected to
`research/findings/W004-bsgs-results.json`. Both executions passed. No seeds or
random sampling: all 365 scalars, including zero and q-1, are tested in all
three solvers. No failed hypothesis test is hidden.

## Observations

Let m=ceil(sqrt(q)). On every tested scalar d, each BSGS variant used exactly
m+floor(d/m) group-add API calls, with the m additions building baby points and
mG at runtime. Linear lookup and exhaustive search both used exactly d+1
equality tests. Worst-case linear lookup counts were 7,19,31,109,199. Ordered
BSGS worst-case sort-plus-lookup counts were 13,25,41,97,155 respectively.
Both BSGS variants' maximum group-add counts were 5,8,11,20,28 versus exhaustive
counts 6,18,30,108,198. The ordered variant is worse in comparison count on the
three smallest instances, which are retained in the evidence. Addition savings
are worst-case comparisons, not per-secret dominance: for d=0 BSGS pays m
additions while exhaustive pays zero.

Informal explanation for linear lookup: write d=im+j, 0<=j<m. Each earlier
giant block scans all m baby entries; the successful block scans j+1. No earlier
candidate index equals d modulo q before the canonical d is reached, giving
im+j+1=d+1 comparisons. This is not yet a Lean theorem about this Python code.

Instrumentation counted 119327 solver events across all runs (group-add calls,
lookup comparisons, sort comparisons), below the one-million initial envelope;
each command finished within its 60-second bound. Setup enumeration and
validation are separate and unpriced. These events are NOT tape transitions.

## Explicit limits and accounting

Each target invocation builds its own m-entry baby table; no online-only or
amortized cost is reported. Merge-sort comparisons are included. A failed
binary-search equality is followed by a separately charged ordering comparison;
both event kinds are aggregated in `lookup_comparisons`, not separate totals.
All group arithmetic uses ordinary coordinate tuples; solvers receive a target
point, public curve constants and G, never its secret scalar or orbit list.
The test harness alone retains the orbit for expected answers.

Counters exclude field arithmetic inside additions, point-comparison internals,
negation, array indexing, allocation, sorting copies, serialization, and peak
memory. m baby entries plus sorting temporaries are present, but no byte-space
bound is proved. Runtime and hardware effects are not measured. This is a
mixed-operation ledger, not a reviewed replacement for Machine semantics.
No Python BSGS correctness/cost theorem, in-model square-root baseline, or
asymptotic extrapolation follows from the finite measurements.

## Review and next step

Native Astra `/root/encoding_review` completed independent script/cost review:
qualified PASS, no correctness blockers. It reproduced the exact command and
all 365 scalar results/119327 events. It checked isolation of secret labels in
the harness, construction charged per target, exact m and block count,
wraparound, tagged coordinate ordering, and counter call sites. The two wording
qualifications (worst-case rather than per-secret improvement; aggregated
equality/ordering totals) are resolved above. Coordinator is proposer/implementer;
reviewer had no write ownership.

Reviewer additionally reported bounded ephemeral cyclic-group tests for orders
1 through 150 (11325 scalar cases, 22650 BSGS runs), including squares and
composites, all passing with no failures. Those scripts/output are not archived
here; they support the review but are not substituted for the committed
reproducible coordinate experiment or claimed as EC verification.

Verdict: reject H for counted equality work; group-operation
savings alone do not justify a total runtime claim. Accept ordered BSGS only as
an experimental reference. Next formal milestone should prove
BSGS correctness together with construction, lookup and storage bounds in an
explicit cost model, then relate it to concrete EC operations and tape access.
