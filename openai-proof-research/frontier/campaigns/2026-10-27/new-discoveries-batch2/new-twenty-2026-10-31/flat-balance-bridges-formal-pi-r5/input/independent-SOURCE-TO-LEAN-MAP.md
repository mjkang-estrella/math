# Source to Lean map — MathDB 352972

Line numbers refer to the exact assigned FlatBalance.lean (502 lines). 'Proved' means a visible proof with supplied author pass evidence, not execution here.

| Source clause | Encoding and proof | Verdict / remaining obligation |
| --- | --- | --- |
| Original record: any flat graph balanced | FlatBalancedConjecture 484–486; not_flat_balanced_conjecture 497–500 | Actual universal implication negated; no graph-specific antecedent smuggled into statement. |
| Introduction: finite simple undirected | SimpleGraph 46–52, endpoint V/hV/G 485 | Arbitrary irreflexive symmetric relation plus Fintype. Type0 small presentations suffice; explicit witness is nonempty. No fixed witness in graph structure. |
| i-cliques are complete i-vertex subgraphs | IsClique 63–64, cliqueFinset 69–71, cliqueCount 74–75, mem_cliqueFinset 78–81 | Actual vertex subsets, cardinality k, distinct pairs adjacent. Full powerset eligibility. No orientation multiplicity. |
| Empty clique c0=1 globally | Empty set qualifies by definition; K33 proof 289–301 | K33 proved. Generic c0 theorem absent: unpaid R1. |
| Definition 2.2 every edge <=2 triangles | IsTriangle 85–86, triangleSet 90–92, Flat 101–102, mem_triangleSet 256–265 | Exact unordered 3-clique incidence containing both endpoints, conditional on actual adjacency. No planar/no-isolated-edge restriction. Definitional meaning is faithful. |
| Eq.14 all odd/even clique totals | oddCliqueSum 105–106, evenCliqueSum 110–111 | Inclusive range 0..card V. Generic higher-count zero/support/range-independence and parity-total bridge absent: R1. |
| Eq.14 absolute difference | discrepancyNat 121–122 | Integer subtraction before natAbs, never Nat subtraction. Generic integer/real cast and abs/bound equivalence absent: R1. |
| Balanced means <=1 | Balanced 129–130 | Bound is actual discrepancy. Generic real-source-bound correspondence inherits R1. |
| Positive-index reading separate | evenCliqueSumPos 114–116, discrepancyNatPos 125–126 | Separate definitions and K33 values; not silently substituted into primary endpoint. No separate positive-index universal-negation declaration; ordinary logical consequence of flat witness and >1 is sufficient commentary, not claimed as a named theorem. |
| K3,3 genuine graph | K33Adj 136–139, K33 143–154, graph lemmas 157–186 | Only cross edges, symmetric, irreflexive, no hypothetical graph laws. |
| Six vertices | card_V6 193–194 | Sum of Fin 3 types, not assumed six. |
| No triangles / no larger cliques | K33_clique_card_le 222–253; triangleSet_empty 269–279; flat 283–286; ge3 395–409 | Three distinct vertices extracted by erase; same-side contradiction; all higher k proved, not just 3..6. |
| c0,c1,c2 | 289–301, 304–326, 329–392 | Unique empty set, injective singleton image, exact cross-pair image and injection. No double count. |
| Odd=6, even=10 / positive even=9 | 424–441 | Range unfolds through all seven sizes with proved counts; higher sizes vanish for witness. |
| D=4 / Dpositive=3, both >1 | 448–466 | Closed Int.natAbs arithmetic via decide after rewrites; not answer assumptions. |
| Flat but not balanced | 469–473, 490–493 | Bound contradicted, existential contains actual graph and proof data. |
| Negation of universal conjecture | 497–500 | Assumed Hall specialized to existential V/hV/G/hflat, contradicts hnb. |

Ordinary generic bridges, independently checked (not present as new Lean theorems): For any finite V, every finset s is a subset of univ and has card s <= card V. Hence no k-clique exists for k>card V. Only the empty finset has size zero, and its pairwise condition is vacuous, so c0=1 including for V empty. Thus the support of c is contained in range(card V+1); adding any larger cutoff adds zeros. Every natural k has remainder 0 or 1 modulo 2; the odd remainder 1 and even remainder 0 selectors are disjoint and exhaustive. This identifies the bounded sums with the finite source odd/even totals. Natural sums cast to Z and R termwise; for z=(odd:Z)-(even:Z), the integer cast of z.natAbs equals |z| and the real cast equals the real absolute difference. Order-preserving casts identify <=1. Removing only size 0 reduces the even total by one, keeping the conventions distinct. These observations validate semantics, but do not meet the requested all-bridges kernel-proof requirement until explicit generic theorems are added and audited.

No bridge to commonNbrFinset is needed: Flat is defined using actual triangles directly. No polynomial, Euler formula, planarity theorem, connectedness, chordality, or upstream clique-root theorem is used to close the endpoint.
