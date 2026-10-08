# H033 primary-literature audit: accepted scope and corrections

Status: bounded search completed by Claude Opus5.5; raw report preserved in
H033-primary-algorithms-opus-raw.md with exact task ID. Root source checks and
an independent native Astra arithmetic review correct several conclusions below.
No new solver experiment, no accepted improved algorithm. Absence of a discovery
in this search is neither a novelty proof nor an impossibility theorem.

## Hu's printed summation-polynomial counterexample

Primary: https://eprint.iacr.org/2024/1923 . Root read archived primary text in
/tmp/h033lit/a.txt, Example1 and §VI. The report's modulus1019 objection is WRONG:
§VI explicitly refers to Example1 over F23, printed order28, so2+3+23=28 is
consistent with that context. No independent order proof is claimed here.

There is a different exact defect. On the stated curve y²=x³+x+1, the printed
2P=(2,19) is off-curve:19²=16 mod23 but2³+2+1=11 mod23. Doubling P=(0,1)
gives slope12, x=6, y=19, hence2P=(6,19). Native Astra independently checked
the primary passage and this arithmetic without a numerical run. The supplied
abscissae therefore fail to represent the asserted triple of points. This
invalidates THAT printed counterexample, not the entire paper or every formula.
The proposed pseudo-index-calculus route supplies no accepted improved solver;
its broad complexity/impossibility assertions are not adopted.

## Windowed-batch BSGS: scope and whole-step cost

Primary: https://eprint.iacr.org/2026/2102 , received2026-09-18. Root read its
landing page and the archived text /tmp/h033lit/c.txt, cost displays on pp9,11.
Text SHA256:80499b3e6f3cffb8648eddd3fbfdbf7ba23390ebb10c5232b096c3f3b1c7aef8.
Direct PDF access failed; archived revision currency is not guaranteed.

The reported measurements concern bounded plaintext recovery. They do not
establish full-range ECDLP improvement, but bounded experiments alone do NOT
make a transferable implementation technique irrelevant. Such a transfer needs
matched full-range work, memory, setup, lookup and stopping analysis.

The raw review quotes15M+4S for a co-Z PAIR update. The paper also charges
normalization and lookup: its displayed leading total per pair is
20M+5S+I/W+2L, with the finite batch correction before simplification. The
unsigned display is12M+4S+I/W+L per output. Do not compare an update kernel
to another solver's completed output. These are paper operation counts, not
root benchmarks. No full-runtime dominance follows merely from them. The next
useful test would compare complete schedules and initialization, not repeat the
paper's narrower measured speedup as a new full-range result.

## Mage: no demonstrated full-range learned solver

Root read https://arxiv.org/html/2512.12483v3 . Reported training memorization
and near-chance held-out bytes do not establish successful held-out scalar
recovery. They also do not logically disprove every weak predictive signal.
The separate extrapolation confuses pairwise collisions with hitting a specified
target: for a fixed memorized set of m distinct scalars and independent uniform
target, membership probability is m/q, not a birthday square-root law. A50%
membership chance needs about q/2 entries. Generalization beyond memorized keys
would require its own measured mechanism and complete training/inference costs.
No AI-FLOPS-to-curve-throughput estimate is accepted.

## Other search results and access limits

The reviewer reports additional scope exclusions for2025/015 (finite-field
multiplicative DLP),2024/1321 (structured weak scalar classes), and abstract-only
2024/1330,2026/1976,2026/1299. Root inspected the2024/1321 landing page but has
not independently certified all raw numerical or theorem claims. Retain them as
reviewer leads with stated access depth, not blanket rejections. In particular,
the raw rational-kernel exclusion and title-only exclusions are not proofs.

No single-target success probability is multiplied/divided into a runtime without
declaring how repeated trials are randomized and which preprocessing is reused.
No special scalar class is the full-range challenge. Search coverage,403s,
archive snapshots and recollection-only comparisons remain visible in the raw
report. No rerun or synthetic campaign is admitted by these sources alone.

## Process and result

Root re-opened primary landing pages/Mage HTML, read archived source passages
and checked cost displays. Native `/root/h007_additive_relations` independently
verified the corrected Hu example. No unproved attack axiom, Lean declaration
or numeric timing was added. The generic square-root reference is unchanged;
verified improvement NONE. Next decisions remain tied to new executable gain
premises from the live H033 investigations, not to broad literature claims.
