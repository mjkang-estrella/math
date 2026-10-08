# H004 P1 frozen integer-coverage gate

Proposer: native Sol /root/h002_tradeoff_ideas. Mathematical preflight: independent
native Astra /root/encoding_review, approved with the clarifications included below.
Implementer: separate native Sol /root/small_curve owns only
research/experiments/H004/coverage_gate.py; root integrates and runs. No experiment
has run at this checkpoint. No full-work or novelty claim.

## Candidate, challenge, comparator

Use all scalar values k in Zq, q in the fixed ascending list31,61,127,251,509,1021.
There are no random seeds or restricted secret ranges. The diagnostic is integer
arithmetic only; it computes offline coverage, not an ECDLP oracle or solver table.
The tested solver receives only G,Q, not these scalar-indexed hit arrays.

P1 has M=floor(sqrt(q/2)), intercepts b=(0,1,2,3), strides
s=(1,M,−M−1,2M+1). Emit labels (a,b)=(j*s_i modq,b_i), j starting0,
in repeating order0,1,2,3. This represents aG+bQ. Grant all schedules the same
negation equivalence and equal unit output cost, including uninformative outputs.
Direct Q=O solves scalar0 at emission0 for all configurations; its actual check
must later be priced in a complete solver.

Compare signed two-list b=(0,1),s=(1,−M) and signed three-list
b=(0,1,2),s=(1,M,−M). Use M=floor(c*sqrt(q/2)), c in{1/2,1,3/2,2},
computed exactly as isqrt((num²*q)//(2*den²)), minimum1. Two-list order0,1;
three-list orders0,1,2 and0,0,1,2. Deduplicate identical configurations. A finite
best-of-grid value is a diagnostic envelope, not free online parameter selection
or a claim of global optimality. Retain each comparator separately.

New record (a,b), old (a',b'), sign delta in{1,−1}: if d=b−delta*b'!=0 modq,
the collision solves k=(delta*a'−a)/d modq. Zero denominator gives no scalar.
Include negative matches between distinct records in the same list. Identity
hit with b!=0 solves k=−a/b; a=b=0 is uninformative. All inverses are modulo q.

## Metrics and fallback

At emission n, U_n is the union of all solved scalar candidates from these
relations, initialized U_0={0}. Store first-hit times T(k). Cap each prefix at
N=2ceil(sqrt(q))+4 outputs; end simulation early only on complete coverage.
The censored mean L_N=E[min(T,N)] and tail S_N=1−|U_N|/q are exact rational
numbers. L_N+S_N is the stronger integer lower bound on uncapped mean. Neither
is the exact uncapped mean if S_N>0. Do not compare two lower bounds as though
they prove an ordering of the actual means.

The frozen bounded solver falls back after a failed prefix: discard its archive,
emit BOTH deterministic signed-BSGS lists with stride m=ceil(sqrt(q)), indices
0..m inclusive, and only then finish. Its constant fallback cost F=2(m+1) is
charged to every failed scalar. This covers all k by k=j+l*m, 0<=j,l<m.
Exact mean output count for this bounded strategy is L_N+F*S_N. This deliberately
conservative fallback is identical for all configurations; do not hide its cost.

A loss rejects only P1's output-count advantage for these tested configurations,
sizes and fallback. It does not reject all schedules, possible cheaper output
arithmetic, or behavior outside tested sizes. A win is merely a gate: charge
initial Q multiples, stride setup, paired blocks/overshoot, table joins, memory,
collision recovery and verification before any end-to-end claim. Known terminal
y omission and batching belong to every applicable comparator.

## Budget, records, validation

One global cap:60seconds or1,000,000 instrumented algorithmic events, whichever
comes first. No resets per configuration or curve. Count modular arithmetic,
Euclidean inverse steps, pair visits, emissions, coverage updates and metric
passes; implementation documents exact categories. This is not a physical/bit
cost model; Python allocation, serialization, process/I/O costs are excluded.
Record exact source hash, parameters, complete configurations and an explicit
incomplete current configuration on exhaustion (exit2). Never infer missing cases.

Mathematical preflight independently checked recovery signs, identity handling,
same-list negative matches, fallback coverage and the censoring formulas. It
required the explicit weighted order and free scalar0 handling now frozen here.
Root must review source and budget instrumentation before the single run; code
review/correctness validation must not quietly spend this experiment cap first.
