# MathDB 366370 — independent preliminary review r526

Recommendation: **EXCLUDE from discovery credit: direct source restriction**, retaining the valid ordinary counterexample. No acceptance, Lean, manuscript, registry clearance, count change, or sibling work is proposed. Root adjudicates. Coverage remains 4,183 reported literal reviews; counts remain 9 additional / 39 total / next 40.

The decisive finding is stronger than a small independently discovered counterexample: **the producer's precise ordinal type is already the restriction of the primary source's Example 6.2 to {a,b,e,f}**, followed by relabeling and monotone rank normalization. This is a complete source-adaptation objection under the campaign standard, analogous in principle to the r363 Cayley decision. It does not assert that the source printed a separately labeled refutation.

## Verdicts

| Gate | Verdict | Evidence and limit |
|---|---|---|
| SOURCE | PASS for literal scope; chronology correction | Definitions 1.2/3.1, all of Section 6, Figure 2, and surrounding conventions agree between arXiv v1 and the actual published PDF. Source publication is online 5 September 2019, journal volume 160 (2020), pp.119–152, rather than first stated in 2024. |
| MATH | PASS | All source hypotheses hold; exactly nine distinct balls, 9 < 10. Independent literal-cut and threshold checks, hand proof below, and source-example controls pass. |
| SUBSTANTIVE | FAIL | Exact producer witness is isomorphic to a four-point restriction of the source's own table (6.1), printed pp.136–137. Restriction and increasing relabeling supply the complete applicability bridge. Metric lifting adds no credit. |
| PRIOR | HOLD globally; sufficient source-adaptation exclusion established | Published Echeloned Spaces body obtained and relevant actual theorem/proof read. It does not supply a ball-count refutation in those inspected passages. No complete global subsumption or registry clearance; no absence-of-hits inference. |
| FORMAL-FEASIBILITY | FEASIBLE interface only; no investment recommended | Finite rank table, cut-to-threshold lemma, exact family cardinality and 9 < 10. No Lean certificate or dependency replay attempted. |

## Exact scope and conventions

The literal target is bound r522 records.json/dispositions.json entry 366370; its statement hash is `460fb9a5c4269620bfb4c8e71ce128aa80d3bf8b6a67aaa7f2efe1cc8a0e5b88`. The independently checked original is r301 corpus chunk 0011, line 572. The canonical record hash is `b6ea1c25fde2726f7dcb19fb07c1d38858fa1888652a36e4a49322320ea8816a`. No MathDB request was made.

Definition 1.2 requires a surjection δ:X×X→L, where L has a linear order and least element 0, δ is symmetric, and δ(x,y)=0 iff x=y. The seven comparison axioms of Definition 1.1 follow from comparison of these ranks: reflexivity, symmetry in each pair, reversal under exchanging pairs, and transitivity are inherited from the linear order; self-pairs have least rank. After Proposition 1.5 the paper globally restricts to semimetric-like ordinal spaces. Our finite integer-valued table is itself a semimetric realization, so that restriction is satisfied.

Definition 3.1 uses a cut (A,B) of the center's own spectrum, with A nonempty, every element of A smaller than every element of B, and A∪B the spectrum. B is allowed to be empty. Thus every singleton and the full set are balls, but the empty set is not. Balls are subsets, not center-radius pairs or diagram occurrences. For a finite spectrum every permitted A is exactly its first k elements for some 1≤k≤|Sp(c)|: if A has largest element t, all elements ≤t belong to A, since any missing element would lie in B and contradict the cut inequality. Conversely each such prefix is a permitted cut. This proves exhaustiveness for every center/cut, without treating sampled radii as proof. Open positive-radius and closed positive-radius metric balls give the same finite family; sufficiently small positive radii give singletons and sufficiently large radii give X.

Section 6 imposes distinct δ-values on every two distinct unordered pairs of different points. It imposes neither line/plane embeddability, majorization, nor an ultrametric axiom. Figure 2 is the conjectured equality structure, not an additional hypothesis. Its four-point drawing has four singletons, three adjacent pairs, two adjacent triples and the full set: ten vertices. The published p.137 figure and conjecture were visually inspected. A nine-ball witness disproves the universal inequality regardless of the equality characterization. The record omits the globally understood semimetric-like convention but the witness satisfies it; the omission does not rescue the conjecture.

## Complete ordinary proof for the producer witness

Take X={0,1,2,3}, L={0,1,2,3,4,5,6}, with the usual order, and

```
δ = 0 1 3 4
    1 0 5 6
    3 5 0 2
    4 6 2 0
```

It is symmetric, its zero entries are exactly the diagonal, and it attains every element of L. Its six unordered off-diagonal values are respectively 1,3,4,5,6,2, all distinct. Integer inclusion gives a semimetric realization. Hence all ordinal and distinctness hypotheses hold.

Increasing the cut at each center gives exactly the following rows:

| Center | All balls at that center, in increasing order |
|---|---|
| 0 | {0}, {0,1}, {0,1,2}, X |
| 1 | {1}, {0,1}, {0,1,2}, X |
| 2 | {2}, {2,3}, {0,2,3}, X |
| 3 | {3}, {2,3}, {0,2,3}, X |

These rows follow from row orders (0,1,2,3), (1,0,2,3), (2,3,0,1), (3,2,0,1). Each center has four distinct spectrum values, and the finite-cut argument above proves that its four listed prefixes exhaust all balls. Their union consists of four singletons, two pairs, two triples and X; sets of different sizes differ, and the two sets within each of the middle sizes differ. Therefore |B_X|=4+2+2+1=9<10=4(4+1)/2.

For the optional metric realization set d(i,i)=0 and d(i,j)=10+δ(i,j) otherwise. Nonzero distances lie in [11,16]. For three distinct points the left side of every triangle inequality is at most 16 while the right side is at least 22; if any points coincide the inequality is immediate. Increasing rank relabeling preserves every cut ball. This construction is already covered by source Proposition 1.5 and Remark 6.5; it is not an additional result.

## Decisive source restriction and chronology

Published Example 6.2 table (6.1), p.136, restricted in order (a,b,e,f), is

```
0  5  8  6
5  0 14  7
8 14  0  1
6  7  1  0
```

Use L'={0,1,5,6,7,8,14}, the actual image, to retain the surjectivity required by Definition 1.2. Restriction preserves symmetry, zero separation and the semimetric realization. All six positive values are distinct. The full centered ball lists are:

| Center | Restricted balls |
|---|---|
| a | {a}, {a,b}, {a,b,f}, {a,b,e,f} |
| b | {b}, {a,b}, {a,b,f}, {a,b,e,f} |
| e | {e}, {e,f}, {a,e,f}, {a,b,e,f} |
| f | {f}, {e,f}, {a,e,f}, {a,b,e,f} |

Again the cut argument proves exhaustiveness. This already refutes the lower bound. More decisively, label (f,e,a,b) by (0,1,2,3), and replace source ranks (0,1,5,6,7,8,14) by (0,1,2,3,4,5,6). Direct entrywise comparison gives exactly the producer's matrix. Thus the same witness up to ordinal isomorphism is furnished by a routine restriction of the source example, not merely by a similar method. The source's complete six-point example has 29 balls; that correct count does not imply its four-point restrictions obey the conjecture.

The published PDF supplies this table and conjecture in the same article (2020 volume; publisher landing page gives online publication 2019-09-05). The arXiv history cached at 2026-10-31T13:29:16.466361Z lists only v1, dated 2024-12-23T08:44:35Z, and already lists the 2020 journal reference. A late arXiv submission does not establish a 2024 priority date. This old printed table suffices for source-adaptation exclusion. No claim is made that a named refutation was published in 2019/2020 or that global priority of a particular explanation has been settled.

## Source/prior body coverage

| Source | Actual passages read / use | Whole-body and dependency boundary |
|---|---|---|
| Keller–Petrov arXiv2412.17391v1 HTML and bound text | Scientific text across Sections 1–9 and references, with focused rereads of Definitions 1.1/1.2, Prop.1.5 proof, Section 3/Claim3.3 proof, Section 5, all Section 6, and subsequent embeddings | Initial whole display truncated; missing middle sections were subsequently read in bounded ranges. No audit of all external reference proofs. Section 7 assumptions do not migrate into Section 6. |
| Keller–Petrov published Acta Math. Hungar.160 (2020),119–152, DOI10.1007/s10474-019-00972-z | Actual PDF: Definition1.2 p.121, Definition3.1 p.127, Section6 pp.136–138, table6.1, Figure2 and conjecture p.137. Figure/conjecture page visually inspected | Published body obtained; relevant scope compared, not every published proof line reread. No author correction identified in inspected history/landing page. |
| Echeloned Spaces arXiv2312.11141v2,2024-02-12 | Definition and Prop.1.8 with proof and finite corollary; introduction and theorem index | Predecessor relative to the arXiv upload, but later than the target's actual publication. Not a published-2025 successor body. Remainder not fully proof-audited. |
| Echeloned Spaces, Forum Math.Sigma13:e89 (2025), DOI10.1017/fms.2025.47 | Actual PDF pp.1–6: introduction, Definition1.1, Lemma1.5, Remarks1.6/1.7, Theorem1.8, Prop.1.11 entire proof and Cor.1.12; selected Prop.3.1 setup, Thm3.17 proof, Cor.3.18 proof, reference16 | Entire PDF retained; remaining bodies/dependencies unread or index-screened. Prop.1.11 is metrizability, not a lower-ball-count theorem; Thm3.17 is a universal colored-graph identification, not a ball-count extremal theorem. Neither is asserted to exclude this witness. |
| r304 accepted-exclusions/history; r363 decision/disposition; r525 adjudications | Bound before reading. Exact scope screen finds no matching ordinal-ball accepted family in r304. r363's source-adaptation exclusion and r525's no-root-math-replay boundary explicitly applied | Historical cached administrative evidence, not current registry or exhaustive literature clearance. Ledger/prior context bound; metadata/exact-scope screening, not full scientific rereading of unrelated accepted work. |

For Prop.1.11 applicability, define the echelon comparison (x,y)≤(u,v) iff δ(x,y)≤δ(u,v). The rank axioms imply its three defining conditions and total preorder; E(X) is the seven-element rank chain, which embeds in R. Prop.1.11 therefore realizes this ordinal type as a dull metric, and Cor.1.12 also applies because X is finite. This bridge only authenticates the **known metric construction**, not a public ball-count refutation. Its general order-embedding theorem dependency is accepted as published; no reproof is needed here. Published Echeloned Spaces expressly cites Keller–Petrov 2020 in reference16 and distinguishes their ball results from its own. It is a later related publication, not an authenticated correction of Conjecture6.3.

A bounded public search on 2026-10-31 covered exact title/Conjecture6.3, ordinal-ball counterexamples, distinct-distance ball counts, the published Echeloned Spaces article, and semimetric ball-structure terminology. Searches returned substantial unrelated uses of “ordinal space.” Relevant actual bodies, not search abstracts, support the conclusions above. `search-final.json` retains the last search's exact tool response and queries; `search-notes.md` records earlier query batches and limits. No verified classical theorem subsuming the ball counterexample was established. Stop further fishing: the independently verified source restriction is sufficient for exclusion, while global prior status remains HOLD.

Current proof registries remain unavailable under the inherited access restrictions. Cached history and search silence cannot clear them. AIM/Kourovka/EGRES/AIProofWatch, DMGT TLS, ProjectEuclid challenge and ResearchGate403 remain parked. No retry, access-control bypass, browser, account, publication, git, message, or upload action was taken.

## Independent checks, producer limitations and integrity

`check-math.py` is newly written, read-only, and imports no producer functions. It enumerates all subsets of each finite center spectrum and directly tests the cut condition. It verifies exact nine-set equality, ordinal hypotheses, metric inequalities, agreement with explicit thresholds, all six complete source Example6.2 rows and its 29 count, and a generic four-point line's ten-ball interval structure. Negative controls detect a changed edge order, omitted triple, omitted full set and added empty ball. Auxiliary bounded enumeration independently confirms all 720 four-point edge orders, with 48 nine-ball cases; this statistic is not used as proof.

`check-source-subset.py` separately checks the new source-restriction deduction, complete nine-ball list, six distinct ranks and the exact relabeling to the producer matrix. All math runs passed under the fixed guard; stdout and guard outputs are preserved. Neither checker writes files. The producer's ordinal ball loops are compatible with the literal finite-cut definition; no mathematical enumeration flaw found. The substantive failure is its incomplete source-internal qualification, not a hash failure or an invalid nine-ball count. Missing bs4 and stopped404 are retained upstream failures, not evidence against the witness.

Before any scientific/history reading, `bind.py` independently checked all 65 intake manifest entries, exact payload inventory, and every listed direct original/copy SHA256+size binding. It did not execute intake/upstream verify.py. `binding-receipt.json` records the initial result. Relevant original sources, text derivatives, source provenance, producer artifacts and r304/r363 files were bound then; later `finish-binding.py` verified the actual original corpus line and canonical record. `flatbindings.json` contains direct immutable references, no recursive copied trees. New HTTP bodies were SHA256+size bound by fetch scripts before extraction, and their text derivatives bound before search/read. `verify.py` checks the final exact payload, its own bytes, all direct external references and original/copy bindings read-only, failing nonzero on mismatch. Hash, size and extra-file controls are bounded in-memory mutations, never edits of upstream originals.

Two reviewer process deviations must remain visible. A combined read accidentally displayed the mixed producer audit-witness.py, including unrelated stack scientific code, before the review isolated ball-only ranges; that violated the requested reading separation. No stack functions were executed, no stack mathematical conclusion was adopted, and no further stack investigation followed. Also the rendered Figure2 PNG was viewed before its own derivative hash was recorded; its bound parent PDF and text had already been verified, but that does not retroactively repair the derivative timing requirement. `figure-binding.json` records the subsequent PNG binding. Initial source/context display truncations were handled by bounded rereads; no truncated output is represented as a complete read.

## Literal formal interface only

A possible endpoint would define `rank : Fin 4 → Fin 4 → Fin 7`, prove symmetry/surjectivity/zero iff equality and injectivity on unordered off-diagonal pairs; define `isBall S` by existence of a center and a nonempty downward-closed subset of its spectrum; prove its equivalence to a finite threshold; then prove `ballFamily = {four singletons, two pairs, two triples, univ}` and `ballFamily.card = 9 < 4*5/2`. An optional metric endpoint uses rational distances 0 or 10+rank and proves triangle inequalities. These are interface sketches, not Lean declarations or an assurance of a completed formal replay. No certificate, manuscript, additional variant, equality classification, or substitute target is authorized by this review.
