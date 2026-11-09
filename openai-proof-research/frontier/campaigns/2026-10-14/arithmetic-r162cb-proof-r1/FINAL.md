# R162CB independent proof review — round 1

**Full-scope correctness verdict: PASS.**

The entire unchanged frozen statement follows from the stipulated operative Source162 proofs at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb and the deductions reconstructed in private/DERIVATIONS.md. There is no actual proof defect and no essential unverified dependency within that stipulated scope. No author repair or new freeze is needed.

Reviewed statement SHA256: b69dd8585357682a27bb327cfcd789ebab99c828c00f928ec79322e1b525f53a.
Reviewed complete proof SHA256: c8e2cf054d11162c11b4e2eb0e042820caa493d7d039bee86f670fa33415a25e.

## Reasons

1. **One common source placement.** The small-plane gadget, every direction/group membership, full-subplane separation, exact deletion counts, pool pencil property, undeleted-line occupancy and external five-group bound apply simultaneously to the same selected translates. Independent pool trials are not confused with the dependent selected translates. All proper subfields at odd degree have size at most q^(1/3). The fixed-constant order is s,Y; selection constants and K; deletion constants delta and rho=delta/10; then q=s^n. The strict occupancy inequality holds for q>5/(2delta). All thresholds fit the frozen for-every-s/for-every-sufficiently-large-odd-n order.

2. **Exact balance and nonisolation.** Only ordinary labels for deletion lines are isolated. Each direction d has exactly q+z_d nonisolated labels, where z_d is one or two. The doubled directions are exactly T=F_s^* minus {u,v}, shared by groups 1 and *. Each omitted line O_d is undeleted and misses every exceptional group. Its identification with any chosen same-direction group-1 special label removes exactly one vertex in that part and no vertex elsewhere. Every part therefore has exactly q+1 nonisolated vertices and remains a transversal part for all edges.

3. **Intersection cap and simplicity.** The source's label rules give exactly one old intersection for each distinct edge pair, including same-group exceptional pairs because cubing preserves both axes. If X met an embedded subplane, all its nonzero-slope lines through that point would have to be omitted, placing f(Y) in two nonparallel axes, contrary to the gadget. Thus X misses every P_i. Any two omitted group-1 lines meet in P_1, so an ordinary edge has at most one merged ordinary label. Merging creates new intersections only between an ordinary edge and a group-1 exceptional edge, and at most one per such pair. Old intersections persist. Distinct image edges consequently intersect in one or two vertices; since their rank exceeds two, no distinct originals have identical images.

4. **All quotient covers are tested.** An arbitrary cover of size at most q has distinct, unique ordinary representatives covering X. The source forces an almost pencil. If an undeleted pencil line's quotient label were absent, its ordinary points could be covered in at most 1+rho*q positions, strictly below delta*q/2. All undeleted pencil labels are therefore forced. A merged label has exactly its old special exceptional action: its ordinary component adds none. This prevents double-counting or an uncharged action in every subsequent case.

5. **Every projective center is excluded.** At infinity, a singleton altered group receives no free special line and would need to be covered by at most s-1 lines. A doubled direction receives exactly one free group-1 line; every additional label costs at most one across the two groups under the source line/point weights. Available cost is at most 2(s-1)+1<2s. At a finite internal center, the two coordinate axes must be retained as covering resources. For group 1 the free omitted directions and deleted directions are disjoint, giving h_p+a(p)<=s-1; other internal groups have no free resource. The resulting at-most-s-line cover contains both nonparallel axes, impossible. At an external finite center, h_p deleted lines come from h_p distinct groups, giving 5h_p distinct witnesses. There is at most one free special line, and its nonzero cubic equation hits at most three witnesses for every special-label choice. Every additional label covers at most five witnesses. The bound 3+5(h_p-1)<5h_p excludes this case, including h_p=1; h_p=0 already exceeds the forced-label budget. Ordinary, special, merged and empty-action labels are all included.

6. **Conclusion.** No cover has size at most q. Any one of the parts is a cover of size q+1, so tau=q+1. This holds together with all required finiteness, partition, exact size, nonisolation, simplicity and intersection assertions on that same quotient hypergraph.

## Surviving obligations

None for the full frozen theorem relative to the stipulated source proofs. No weaker replacement statement was used. This verdict does not assert an effective construction or threshold, fractional-cover claim, all-rank result, or linearity of the quotient. Contribution grading, novelty, acceptance and campaign count are not assigned here.

## Reading and integrity limits

All seven required author inputs were read completely. Both actual source proofs and all 18 canonical non-PDF texts (291,598 bytes) were read completely, including both actual wrappers and every mathematical include. Twenty blobs were authenticated against the specified complete tree; six tree entries were recorded. Source PDFs were authenticated but not visually read. The source truth itself was stipulated and not audited.

My primary reading comprises 40 distinct PDF pages: HS 1--9; SW 1--8; ABPS 1--5; Bucic--Jain--Sivashankar 1--5; FHMW 1--3 and 10--13; DKMS 1--4 and 50--51. Relevant construction proofs and interfaces were read at these extents; no broader primary or transitive-ancestry reading is claimed. Fresh PDF extraction matched the allowed text copies. No primary visuals, web search, optional history traversal, foreign-review inspection, or author verifier execution occurred. Initial tool truncations of combined instruction/proof output and their operative recoveries are disclosed in private/READING-LIMITS.md. All source-window displays and primary-page displays were untruncated. All review reads occurred after the author freeze. No needed access failed.

All 61 author files retain their listed bytes and FULL modes. Semantic-false files received raw integrity checks only. The final packet has its own exact sorted manifest, full file/directory modes, and read-only verifier requiring explicit detached FINAL/MANIFEST/outside-REPORT anchors. Tiny copied integrity controls use the same verifier logic. Artifact verification is not a mathematical gate.

Provenance: Codex / GPT-6 Astra / reasoningEffort high / serviceTier default, STANDARD speed. No nested agent, author edit, shared-index edit, git operation, browser UI, publication, contact, or downstream formal/manuscript/release work.
