# Independent preliminary adversarial review

Recommendation: **INVEST in a literal certificate; HOLD acceptance and novelty credit.** SOURCE and MATH pass. SUBSTANTIVE is provisionally favorable, with a serious classical-mechanism objection. NOVELTY remains HOLD. FORMAL-FEASIBILITY is favorable as a plan, not a verified endpoint. Root alone decides acceptance; this report changes no counts.

## SOURCE — PASS, including published version

Reviewed the frozen candidate PROOF.md against actual arXiv:1501.04540v2 text, Definition 1.4, Theorem 1.5, Proposition 1.9, Section 4.1, Proposition 4.20 and Question 6.6. Independently retrieved the published primary PDF, DOI **10.1007/s11083-016-9408-x**, *Order* **34** (2017), 441–463. Its first page says received 18 March 2015, accepted 1 September 2016, published online 6 October 2016. Crossref corroborates the online date. The candidate's 10 December 2017 date is the arXiv v2 date, not first publication. The source receipt's HTTP Last-Modified is not publication chronology.

The published Question 6.6 explicitly concerns the group of linear automorphisms of the cube centered at the origin with vertices (±1,…,±1), acting on the Boolean algebra with **2^n ground elements**, namely cube vertices. It does not concern just B_n on coordinate positions, the face lattice, or the 2n signed coordinate directions. Definition 1.4 requires X and Y each covered by the same Z, Y in the full G-orbit of X, and an X-to-Y transport in the setwise stabilizer of Z. These are exactly the candidate's quantifiers.

Signed coordinate permutations are real linear symmetries of this centered cube; complementing a binary coordinate means negating its real coordinate. It would be a translation in a {0,1} realization, but that is only the encoding. The candidate does not confuse these actions. Every real linear automorphism of the cube preserves its polytope edges, hence cube graph distance, hence Hamming distance. This proves the needed full-group invariant without presupposing orthogonality or restricting to a subgroup.

The published Definition 1.4/Theorem 1.5 and Question 6.6 match the preprint. The separately retrieved primary REU report retains the same cube question as Question 9.12, and the regular-action statement as Proposition 4.22. It supplies no refutation in the inspected sections. The report is associated with the 2014 REU; the server modification timestamp alone does not certify its first public date. ArXiv metadata frozen by the candidate gives initial submission 19 January 2015 and v2 update 10 December 2017. No post-2017 correction is inferred absent evidence.

Theorem 1.5 is sufficient, not converse. Failure of CCT leaves Conjecture 1.3 about Peckness untouched. The result answers the universal cube question negatively and establishes failure for each n≥5. It does not classify every n; no conclusion for n<5, including n=4, is part of this review's result.

## MATH — PASS by independent reconstruction

I fixed Z={2,9,10,13,19,20}, X=Z−{9}, Y=Z−{2}, independently of candidate certificate files. In low-bit-first notation the coordinate permutation sends 0→0, 1→3, 2→4, 3→2, 4→1, then flips bit 0. Its images on X, in increasing order, are 2→9, 10→13, 13→20, 19→10, 20→19. Thus gX=Y. Both X and Y have five elements and are proper subsets of the six-element Z, so both are covered by Z in the Boolean order.

Using explicit five-character binary strings and coordinate mismatches, my checker independently obtains the distance matrix, ordered by Z:

```
0 3 1 4 2 3
3 0 2 1 3 4
1 2 0 3 3 4
4 1 3 0 4 3
2 3 3 4 0 3
3 4 4 3 3 0
```

The six profiles c(v) counting distances 0,…,5 are respectively
(1,1,1,2,1,0), (1,1,1,2,1,0), (1,1,1,2,1,0),
(1,1,0,2,2,0), (1,0,1,3,1,0), (1,0,0,3,2,0).
Consequently every distance-preserving permutation of Z fixes 13. If hZ=Z and hX=Y, bijectivity gives h(Z−X)=Z−Y, so h9=2. Invariance would equate d(9,13)=1 with d(2,13)=4, impossible. This excludes even all metric automorphisms of Z, therefore certainly every full cube stabilizer element.

Appending n−5 constant zero bits preserves every displayed distance and profile. Extend g by the identity on new coordinates. Any ambient symmetry stabilizing padded Z still fixes its intrinsically unique-profile point 13; it need not preserve the embedded five-face for this argument. The same contradiction works. This is a uniform proof for all n≥5, not finite extrapolation.

`independent-check.json` records my arithmetic and, as a redundant check, all 5!·32=3840 signed-coordinate maps in dimension five. Exactly two transport X to Y; Z has just the identity stabilizer. The proof needs only the weaker no-stabilizer-transport fact. I inspected the candidate's search/reduction/verification scripts, but did not replay its dimension-four exhaustive search or its discovery history; none is a premise of the proof. No claim of smallest witness or independent validation of the candidate's dimension-four search is made.

## SUBSTANTIVE — provisional PASS; explicit subsumption attempts

The strongest objection is that this is a small pseudosimilarity construction using a classical broken orbit and a classical metric signature. Those ingredients are old. The question is whether old results already supply the full cube action with the necessary deletion congruence and lack of stabilizer transport. Shortness alone does not decide substantive credit.

1. **Source Proposition 4.20(2), actual proof read:** if G is not elementary abelian 2, choose g²≠e in the left-regular action on G. The singleton pair {e},{g} below {e,g} witnesses failure. For the five-cube group that Boolean ground set has 3840 elements, not 32. In the cube action every pair of vertices can be exchanged by XOR with their difference, a signed-coordinate involution. Thus the regular-action singleton witness cannot transfer directly. This is a concrete obstruction to the simplest proposed bridge, not merely an appeal to different notation. Subgroup failure also need not survive enlarging the group: enlarging a stabilizer can supply a missing transport.

2. **Semidirect/product/wreath results, actual statements and local proofs read:** Proposition 1.9 needs CCT of K on P/H, not just CCT for abstract factors. The elementary-abelian flip subgroup is CCT by 4.20(1); that does not discharge the quotient hypothesis. Proposition 4.3 concerns P×Q; 4.8 concerns P^ell with its product order. In the cube question the poset is P(vertices of a product), which is not the product of the Boolean algebras on the factors. S2 wreath Sn on signed coordinate directions gives B_(2n), while its product action on cube vertices gives B_(2^n). In particular n=5 distinguishes 10 from 32 ground elements. Their abstract group identity supplies no applicable CCT preservation theorem for this target.

3. **Classical pseudosimilarity body obtained:** Kocay, *Graphs, groups and pseudo-similar vertices*, J. Austral. Math. Soc. A **37** (1984), 181–189, DOI 10.1017/S1446788700022023. Read Definition 2.1, partial permutations, Theorems 3.1–3.3 with construction proof, Example 4.1, and Construction 4.5 through its concluding stabilizer argument. Theorem 3.3 embeds an already given pseudosimilar graph in a larger graph, generally infinite, carrying extended automorphisms; Construction 4.5 uses a chosen group/subgroup and a Cayley graph/GRR to control graph automorphisms. It does not embed that graph into the five-cube, or assert that deletion graph isomorphisms extend to signed-coordinate permutations. Graph adjacency alone forgets the other Hamming distances. Conversely a full cube stabilizer must preserve all those distances. Applying the construction here would still require the precise cube representation and a proof that its larger stabilizer cannot repair failure. Those are exactly what the six-point certificate establishes. I found no automatic complete bridge in this actual classical body.

4. **Modern primary comparison:** Ivanov, arXiv:2609.00394v1, title page 31 August 2026, Sections 1–3, 7 and Appendix A.2. Its sliding-gap Lemma 2.2 and proof are the same generic orbit mechanism underlying the search: translate the deleted interval to obtain isomorphic cards. Its clocks are graphs, with a 17-vertex example and larger asymmetric constructions; there is no specified five-cube vertex representation in the inspected construction. This is significant methodological prior, not a demonstrated exact-action subsumer. No full audit of every asymptotic theorem is claimed.

5. **Hypomorphic systems/configurations:** Couceiro–Lehtonen–Schölzel, arXiv:1306.5578v1, definitions of cards and ground-set isomorphism, Definition 3.8, Proposition 3.13 and proof, and Section 7 Proposition 7.2 and complete local proof. They construct two nonisomorphic hypergraphs with matching vertex-deleted cards. Deleting a hypergraph ground element removes all incident blocks; our deletion removes one cube vertex (one binary word). Their coordinate identifications likewise differ from removing a word. Their exact parity-toggle proof gives no union Z differing by one word on either side and no ambient cube transport, so I cannot transfer its conclusion. Hongyu He, arXiv:math/0511475v2 (26 June 2006), introduction Theorems 1–2 and Section 3 definitions/Gram presentation and geometric reconstruction conjecture: arbitrary real Gram configurations with congruent cards are not binary-coordinate configurations with transports in the cube group. This limited body comparison does not clear all geometric reconstruction literature.

Conclusion: the required action-sensitive obstruction is real mathematical work. No complete classical-to-target bridge was located in the inspected bodies. This supports investment, subject to root's substantive judgment; it does not establish priority.

## NOVELTY — HOLD

Primary bodies were used, rather than snippets or arXiv IDs alone. Current bounded Crossref title queries identify the published source and classical pseudosimilarity papers; a current arXiv query identifies the primary comparisons above. Exact URLs, UTC times, response bytes and hashes are in `primary/*.receipt.json`; extraction records bind each PDF before extraction and its text before reading. `page-map.json` indexes decisive literal terms. The candidate's frozen version metadata and source receipts are retained. The classical 1984 paper predates the 2015/2016 question; the 2026 paper also predates this candidate and deserves methodological credit. These comparisons are not proof of absence elsewhere.

Kimble–Schwenk–Stockmeyer 1981 was identified from current Crossref metadata but the Wiley PDF request returned 403. It was stopped and not retried. Godsil–Kocay 1982's own full body was not obtained; Kocay 1984 is an actual classical successor, not a substitute falsely labeled as the 1982 original. Full current public registry heads/bodies and comprehensive citing coverage remain unavailable here. Previously denied GitHub API/raw/codeload/diff/patch, ScienceDirect and Google challenge routes were not used. Old inaccessible intervals remain parked. No novelty inference is drawn from candidate historical registry screens, open labels, metadata-only results or inaccessible bodies.

## FORMAL-FEASIBILITY — favorable PLAN ONLY

Represent vertices as Fin n → Bool and Boolean-poset elements as finite sets of vertices. Define CCT literally using covers, orbit membership and a setwise stabilizer. Prove covers from a one-point deletion; define g using the explicit coordinate permutation and sign change. Certify the finite mapping and distance table with kernel-checkable finite reasoning. Prove generic profile invariance under a distance-preserving bijection and complement-image identity, then obtain the 1≠4 contradiction. Embed Fin 5 into Fin n for n≥5 and prove constant-coordinate padding preserves distance. The all-n theorem should quantify the full signed-coordinate group, and a separate proved bridge must identify its action with all real linear cube automorphisms (or prove directly that every such automorphism preserves cube distance). Omitting this bridge would silently weaken the source endpoint. No Lean code or manuscript was written or tested. Allowed-axiom audit, complete source endpoint, independent formal review and extracted strict replay remain required.

## Remaining gates and provenance

Before acceptance root needs: (i) bounded current citing/registry and nearest classical body follow-up through lawful distinct routes, with unresolved access gaps explicitly adjudicated; (ii) substantive-credit decision on the classical broken-orbit objection; (iii) literal complete formal endpoint and geometric/full-group bridge; (iv) independent formal/final review, paper and fresh extracted replay. No further historical HEAD loop or exhaustive freshness campaign is recommended. A useful targeted next question is whether the classical binary-code/set-reconstruction literature already gives deletion-congruent inequivalent points under the full signed-coordinate action in dimension five.

All scientific candidate inputs were copied and SHA256-bound before scientific reading; administrative ledger/context are snapshots only. `freeze.json` binds 69 flat source/report/script inputs; no historical trees were copied. `before-after.json` verifies every original and copy again after review. Immutable original paths remain named, not recursively embedded. The checker hardcodes the witness rather than loading the candidate certificate. `manifest.json` excludes itself and `verification-receipt.json`; a distinct guarded invocation verifies the completed manifest, originals/copies, downloaded primary bytes and extracted bodies. The receipt records the result.

All Python, downloads, extraction and hashes ran through the designated helper_guard.py with OPENBLAS_NUM_THREADS=1, OMP_NUM_THREADS=1, PYTHONDONTWRITEBYTECODE=1 and fixed AS/group-RSS 512 MiB, CPU 210 s, wall 230 s. Native reads and apply_patch were used within the permission given. No child agents, git, shared edits, public posts, browser, MathDB, Lean or manuscript actions occurred.

Failures/limits retained: the initial filename search was accidentally too broad and its listing truncated; it read no scientific body. Some later combined read outputs also truncated, so decisive passages were read separately. Two independent Crossref queries were launched together before their returned concurrency-limit header was known; no 429 occurred, and no further Crossref request followed. The chains PDF extracted with a font-type warning, exit 0; the local cited proof is coherent but no visual PDF audit is claimed. Wiley 403 is retained. Springer returned actual PDF bytes after its ordinary automatic redirect with a cookies_not_supported query; no browser, challenge solving or custom cookie/proxy bypass was used. No inaccessible source is described as read.
