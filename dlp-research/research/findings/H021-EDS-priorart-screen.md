# H021 EDS-BSGS primary-source comparison

2026-10-08. Known prior art, not a new attack. Root independently inspected
the primary source located/read by native Sol /root/h010_early_dependencies.
Verified improvement NONE. No experiment or new general formal infrastructure.

Liao and Zhang, *Accelerating Baby-step Giant-step Algorithm for Solving ECDLP
Using Elliptic Divisibility Sequences*, TCHES2026(3),518–540,
[primary PDF](https://tches.iacr.org/index.php/TCHES/article/download/13106/12653),
DOI10.46586/tches.v2026.i3.518-540. The web tool could not open it; direct
publisher curl succeeded. Root read Section2.3/2.4, Algorithms2/4, Lemmas1/2,
Remark3 and Section5.2. Sol read the broader algorithm sections as well.

The public representation bridge applies to prime point order q>3 relatively
prime to p-1 (our notation: field F_p). Public shifted EDS terms are computable
from Q without knowing its scalar. Algorithm4 explicitly constructs complete
auxiliary lists before its interleaved loop. Its stated auxiliary-list cost is
(3.5M+S)*sqrt(q), apart from lower-order setup. The online kernel is not free
and matches require scalar verification. The reported inversion threshold
31.98 compares a fixed8,8 full-point baseline, not our x-only variable-batch
comparison. These are source statements, not reproduced measurements.

## Our single-target arithmetic screen

H019's explicitly scheduled x-only interleaved comparator has leading expected
cost (2sqrt(2)/3)*(2.5+s)*sqrt(q) multiplications, s=S/M, under its stated
uniform-input, memory and inversion-amortization assumptions. Because
2sqrt(2)/3<1, this is less than (2.5+s)*sqrt(q), which is itself less than
the EDS full-list setup (3.5+s)*sqrt(q). At s=.8 the comparison is approximately
3.111sqrt(q) versus4.3sqrt(q), BEFORE the EDS search loop. This rejects the
literal fresh-preprocessing schedule's gain rationale in that matched limiting
arithmetic model; it is not a finite wall-clock measurement.

Both finite algorithms still pay their actual initialization, inversion/field
operations, table traffic, labels, exceptions and verification. Batching
parameters and memory must be feasible; no universal hardware conclusion follows.
Shared preprocessing across many targets is a different comparison, charging
the setup once to both appropriate algorithms. A lazy EDS schedule would also
be a different algorithm requiring its own dependency/support and coverage
analysis. This screen does not reject either possibility in general.

Remark3's wider block kernel tends toward3M per emitted term as block width
grows, conditional on available supporting terms. Do not replace that family
by a blanket assertion that every EDS term costs3.5M+0.5S. Lower kernel cost
does not erase its required auxiliary terms, stored blocks or target matching.
No new support-generation mechanism that changes complete work was supplied.

## Coverage qualification

The source uses both signs of giant terms and both baby directions. Index caps
near sqrt(q)/2 are therefore not by themselves a half-range bug: the signed
rectangle is ±iD±j, with correct endpoint rounding required. However the
depth-first EDS emission order is not plainly the contiguous-prefix schedule
used in a standard interleaved stopping-time argument. We do not import its
average-loop constant without checking those actual index sets. The
preprocessing-only screen above does not need that contested constant.

EDS values are not established injective keys. A correct implementation must
retain the relevant colliding indices, or prove that discarded indices cannot
hide the actual witness. Verifying one false match does not justify discarding
the remaining matches. This is an additional correctness gate, not evidence
that the literal paper implementation necessarily fails.

## Evidence and next gate

Source retrieval, temporary files outside the repository:

    curl -L --fail --max-time 30 -o /tmp/ecdlp-eds-bsgs-2026.pdf https://tches.iacr.org/index.php/TCHES/article/download/13106/12653
    pdftotext -layout /tmp/ecdlp-eds-bsgs-2026.pdf /tmp/ecdlp-eds-bsgs-2026.txt

A reopening needs a concrete paid lazy/support schedule, a justified material
finite-cost regime, or matched multi-target amortization. The literal paper
schedule supplies no gain over the stated comparator. Sol's broader H021
representation report COMPLETED; its separate ray-class lead is retained for
independent review. No candidate experiment follows here.
