# Independent formal-fidelity review: MathDB 355217

This is a review, not acceptance. A PASS; B PASS; C PASS; D PASS (bounded formal spot check); E QUALIFIED_PASS (manuscript integration conditions below). No required correction to the reviewed Lean endpoints was found. Root alone decides acceptance, credit and the decisive fresh replay. Credit remains zero in this review.

The object reviewed is the source-only archive in ../middle-formal-r1/middle-source.zip, SHA-256 **5a3e8ac8153651c55942d8f1288b50dd0c578b089c02d01c353b750b2c5bb62b**. References to Lean files below mean the byte-identical members in extracted/. Source references mean ../expanded-corpus-r139/sources/txt-2206.15439.txt. The previous mathematical review and root ruling were read; they are evidence and scope instructions, not assumptions in the Lean proofs.

## A. Definition fidelity — PASS

The source standing assumptions, lines 31–38, are finite, undirected, simple graphs, and closed-neighborhood domination. Definition 1.2, lines 55–58, requires domination and connectivity of G minus S, then takes the minimum cardinality. Definition 1.3, lines 63–75, specifies the literal middle graph. Conjecture 7.1, lines 460–461, is the strict inequality at order at least 2. The cached MathDB record raw/355217.jsonl:1 reproduces that conjecture. This review uses the cached primary text; it makes no fresh claim about current publication status.

- MiddleBase.lean:202–210 defines G8 on Fin 8 with exactly the 11 unordered edges 01, 06, 16, 23, 27, 37, 46, 47, 56, 57, 67. adjB includes both orientations and no additional pair. The list has no loops or duplicate unordered edges. MiddleWitness.lean:103–108 proves connectivity using a concrete spanning tree. Sanity.lean independently checks 11 edges.
- MiddleBase.lean:34–35 defines IsDominating as every vertex belonging to S or having a neighbor in S. This is exactly the source's closed-neighborhood condition, with no missing self-domination case.
- MiddleBase.lean:39–44 uses the graph induced on the complement, with Preconnected for convention A and Connected for convention B. MiddleFinal.lean:4–8 gives the same complement predicates separately. IsOCD and IsOCD' are definitionally domination conjoined with these predicates. The distinction is precisely nonemptiness of the complement. Our own full-set examples verify vacuous preconnectivity and failure of Connected on the empty complement.
- MiddleFinal.lean:10–36 states four attained IsLeast minima. Membership supplies an actual feasible set of cardinality 4; the second part bounds every feasible cardinality below by 4. Swapping the order of the cardinality and feasibility conjuncts relative to the internal sInf definitions changes no set of attainable values.
- MiddleBase.lean:47–52 uses sInf of attainable cardinalities, but MiddleWitness.lean:5–15 and 116–126 supplies a nonempty feasible-cardinality set in every application to G8 or its middle graph. No Nat.find, missing minimum or empty-set default proves the credited result.
- MiddleBase.lean:57–75 defines middle G on the tagged disjoint sum W ⊕ G.edgeSet. Its four adjacency branches are, in order: no vertex–vertex edges; incidence for vertex–edge; incidence for edge–vertex; distinct edge nodes sharing a vertex for edge–edge. G.edgeSet is the subtype of unordered Sym2 edges, so each original edge occurs once. This is Definition 1.3, with no surrogate Fin 19 graph or unproved isomorphism.
- MiddleFinal.lean:38–52 separately negates the two universally quantified inequalities over every Type in Lean's base universe, every Fintype instance and every connected SimpleGraph with order at least 2. This matches the root-authorized connected restriction. Every finite abstract graph has a representative here; in particular Fin 8 is an explicit admissible instance. Generic definitions are universe-polymorphic, and restricting the universal proposition to Type does not weaken the exhibited counterexample. There is no hidden nonstandard Fintype for Fin 8 and no requirement of an extra middle-graph Fintype in the statement: the cardinality minima use finite sets on its literal type.

The internal Conjecture71Connected at MiddleBase.lean:87–89 still conjoins the two conventions. It is not a final endpoint and is not used as a substitute for the two separate negations. The final statements resolve the previous review's conjunction objection.

MiddleFinal.lean:64–103 explicitly proves no convention-B OCD set exists for the edgeless graph and records its totalized value as 0. Lines 107–123 give an uncredited domain control. Neither connected refutation uses it. Under convention B the domain control is a statement about totalized numbers, not an attained source minimum.

## B. Proof structure — PASS

The proof dependencies terminate in ordinary mathematical proofs and kernel-reduced finite decisions, not hypotheses imported from discovery scripts.

1. G8 upper bound: MiddleBase.lean:216–233 uses S0 = {0,2,4,5}, a finite domination check and the parent chain 1 to 6, 7 to 6, 3 to 7 on its complement. Generic reach_of_parent and connected_of_parent, lines 99–121, prove reachability by strong induction on decreasing depth, then connect arbitrary vertices through the root. The root also witnesses nonemptiness.
2. G8 lower bound: MiddleSmall.lean:5–312 contains exactly bad_0 through bad_92. Each either exhibits an undominated vertex, or a component closed under adjacency inside the complement plus a vertex outside it. The generic separation lemma at MiddleBase.lean:124–137 propagates membership along every walk, contradicting reachability. There is no assumed component computation. Our independent script confirms all 93 distinct subsets of cardinality at most 3 appear, precisely 1 + 8 + 28 + 56.
3. Coverage and assembly: MiddleSmall.lean:313–314 lists the subsets and kernel-checks that every small finite set belongs to the list. Lines 315–412 split this disjunction and apply each corresponding certificate. Line 413 transfers the lower bound to convention B by forgetting nonemptiness. Coverage is proved, not inferred from the Python generator.
4. Middle lower bound: MiddleBase.lean:141–180 chooses a selected dominator for each original vertex node. Fibers over a vertex node have at most one vertex, and fibers over an edge node have at most its two endpoints. Summing fibers yields |V| ≤ 2|D|. MiddleWitness.lean:110–114 specializes this to 8 ≤ 2|D| and hence 4 ≤ |D|. Connectivity is unnecessary for this lower bound.
5. Middle upper bound: MiddleWitness.lean:20–43 constructs the literal edge subtype values, the matching mate map and D8 = {m01,m23,m46,m57}; the generic lemma at MiddleBase.lean:183–194 proves domination from endpoint coverage. It does not assume a separate theorem about perfect matchings. MiddleWitness.lean:47–101 defines the tree depths, endpoint selector, parent map and strict descent proof for every complement vertex. Original vertices go to a remaining incident tree-edge node; every edge node goes to an incident original vertex. The root is inl 6. This proves Connected on the actual complement.
6. G8 connectivity uses the same original-vertex tree at MiddleWitness.lean:103–108. The sInf equalities in that file use attained witnesses and lower bounds. The four IsLeast endpoints in MiddleFinal.lean:10–36 directly assemble the same witnesses and bounds. Finally lines 42–44 and 50–52 specialize the universal claim to connected G8 and reduce it to 4 < 4.

All 207 local declarations in the proof closure were checked for forbidden metadata and transitive axioms. The finite certificates are trusted because Lean checks their terms; generation and brute force are not proof oracles.

## C. Independent semantic sanity — PASS

scripts/sanity.py is newly written in this lane and uses only Python's standard library under python3 -I. It constructs G8 from the 11 edges and constructs the middle graph independently with integer-labeled original and edge nodes. Domination is closed-neighborhood bitset coverage; complement connectivity is a bitset traversal. It enumerates all subsets at each cardinality through the first feasible cardinality. It does not import or execute discovery or packet Python code.

Under each empty-complement convention it finds:
- G8: minimum 4, exactly 8 minimizing sets.
- Middle graph: minimum 4, exactly 2 minimizing sets, corresponding to {01,23,46,57} and {01,23,47,56}.
- Orders and sizes: (8,11) and (19,48).
- {0} in G8 fails domination; {6,7} dominates but has disconnected complement; the first three edge nodes in the middle graph fail domination. S0 and D8 are valid under the nonempty convention.

Sanity.lean:7–25 checks the counts, the failed singleton, the failed outer-connectivity of {6,7} under both conventions, forbidden vertex–vertex adjacency, both witnesses, and the four values against the compiled packet. Lines 26–32 additionally test the empty-complement distinction directly. Value examples intentionally use the packet's theorems; their independent numerical comparison is the brute force, not a claim of a second independent formal proof.

The first sanity compile failed because my test file lacked a decidable middle-adjacency instance for edge counting and decide. A local instance at Sanity.lean:4–6, obtained by unfolding the literal adjacency, fixed it. This was a test-harness issue, not a packet definition or proof defect. Both the failed log and the successful logs are retained.

## D. Bounded formal spot check — PASS

This reviewer extracted the bound archive into the lane-local extracted/ directory and built only into build/. scripts/checks.sh records the serial reproduction commands. Every Lean command used -j1 -M3500 -DwarningAsError=true. MiddleBase, MiddleSmall, MiddleWitness, MiddleFinal and MiddleAudit each compiled and each passed leanchecker with that explicit module argument. Upstream pinned mathlib oleans were read only; this did not rebuild all of mathlib from source. The full imported declaration closure was inspected by MiddleAudit.

MiddleAudit.lean:5–53 reconstructs the import closure and verifies equality of its declaration inventory with the audited set. It reports 252,066 declarations and 207 local proof declarations. scripts/verify.py independently reads every audit row, checks unique names and dependency-name coverage, and checks the local metadata and allowed transitive axioms; missing dependencies: zero. audit-summary.json records the results. Upstream compiler/runtime metadata is separately reported and is not misrepresented as absent.

Sanity.lean prints axioms for all seven requested endpoints and G8_connected. Every list is exactly propext, Classical.choice, Quot.sound. scripts/sanity.py strips nested block comments, line comments and strings before scanning every packet Lean module for sorry, admit, axiom, unsafe, partial, native_decide, ofReduceBool, implemented_by and extern. All eight files have zero matches. MiddleAudit additionally checks local declaration metadata including generated declarations and opaque values; the text scan alone is not the audit.

The three packet negative controls were also run: NegativeValue rejects 4 = 3, NegativeAdjacency rejects False, and NegativeConnected rejects the asserted preconnectivity. All fail with actual false-proposition diagnostics, exit 1, rather than timeout or import failure.

Resource enforcement is in scripts/run.sh: two CPUs (0,1), CPU 120 s, wall 140 s, MALLOC_ARENA_MAX=2, a polling process-group RSS watchdog killing at 6 GiB, and lane-local TMPDIR/cache. One heavy process ran at a time. The largest observed sampled process-group RSS was 2,278,288 KiB (MiddleAudit compilation); no cap was reached. All stdout, stderr and receipts, including the initial failed sanity test, are retained in logs/. The wrapper waits for its launched process; no review background job remains.

This is the required bounded independent spot check. It does not replace or claim root's decisive fresh replay.

## E. Manuscript readiness — QUALIFIED_PASS

The finite formal result is ready for root consideration. The formal packet explicitly excludes the infinite family and smallest-order enumeration from its formalization scope (../middle-formal-r1/STATEMENT-CORRESPONDENCE.md:15). The discovery PROOF.md is a working candidate document and still describes an obsolete uncompiled draft at lines 75–96. It must not be passed off as a final paper for the current endpoints.

Required manuscript integration, without changing the immutable reviewed inputs:

1. State the 11-edge connected counterexample, both attained values 4, witnesses and the G-side lower-bound proof. Include the literal middle-graph construction and the middle counting argument. Cite Definition 1.2, Definition 1.3 and Conjecture 7.1 with their exact quantifiers.
2. State separate empty-complement conventions and the connected scope of the credited negation. Explain that the edgeless observation earns no credit; under convention B it has no attained minimum, so its 0 is solely a totalization.
3. Include the equality family G_{a,b}, a,b ≥ 1, n = 2a + 2b + 4, with its four-case lower bound, explicit upper witness and matching. State the perfect-matching characterization for connected finite simple graphs of even order n ≥ 2: equality at n/2 in M(G) iff a perfect matching F leaves the spanning graph G minus F connected. Give both directions, using disjoint coverage in the equality case and projecting paths in the remaining middle graph. These are ordinary mathematical results checked in the prior mathematical review, not endpoints of this Lean packet.
4. Label uniqueness at n = 8 and absence of smaller connected examples as exhaustive computation up to isomorphism, with generator counts, coverage, search method, scripts and independent cross-checks. Do not label it a Lean theorem. The previous review reproduces 11,117 connected order-8 representatives (../middle-review-r1/REVIEW.md:117–146); this lane did not rerun that classification.
5. Record, as uncredited corrections, Theorem 4.12 at K_{2,2}: correct middle value 3 rather than 2; and Section 7's friendship value: gamma-tilde-c(F_n) = n rather than 1 for the source's n ≥ 2. See source lines 276–287 and 455, and prior review lines 67–77. These errors are not used by the formal counterexample.
6. Keep significance modest: a concrete equality refutation in a specialized domination problem. Explain the source-ingredient status of the middle counting/matching construction and the separate content of the G8 lower bound. Preserve the source-standing and near-tightness caveats in the root ruling and prior review. Do not claim worldwide priority, major impact, or a strict reversal.
7. Describe the finite certificate audit, exact versions and archive hash, IsLeast endpoints, allowed axioms, independent brute force, negative controls and bounded resource discipline. State that the family and classification are outside the finite formal proof and that root's decisive replay remains separate.
8. Preserve dated access limits. Prior work reports bounded arXiv/OpenAlex and registry checks, not exhaustive literature clearance; no Scholar, MathSciNet, zbMATH or publisher clearance was obtained by this lane. No network was used here. The source's live status and priority have not been re-established by this fidelity review. Remove stale draft/build status claims from the final manuscript and point to the final endpoint names.

No Lean repair is required by A–D. These eight manuscript conditions and root's own decisive replay/acceptance remain required before any final acceptance claim.

## Input binding and artifacts

hashes-before.txt and hashes-after.txt bind all requested formal handoff files, the archive, the two prior review files, root ruling, discovery PROOF.md, raw record and every file recursively under expanded-corpus-r139/sources/. They match byte for byte. scripts/verify.py also verifies every extracted archive member byte for byte against the zip, with safe relative member paths.

review.json contains separate A–E verdicts, fixes and evidence references. sanity.json stores independent enumerations and source-scan results. audit-summary.json summarizes the full audit.jsonl retained under extracted/. scripts/checks.sh, scripts/run.sh, scripts/env.sh, scripts/sanity.py and scripts/verify.py reproduce the bounded checks. hashes-own.txt binds review artifacts and logs.

No child agents, git commands, shared ledger edits, publication, uploads, external messages, network or browser tabs were used. All created files are inside this review lane.
