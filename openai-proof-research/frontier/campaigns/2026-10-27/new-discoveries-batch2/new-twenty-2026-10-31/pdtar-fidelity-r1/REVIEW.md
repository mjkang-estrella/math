# Independent formal-fidelity review: MathDB 353203

This is an independent review, not acceptance. A–D: PASS. E: QUALIFIED_PASS. No blocking formal-fidelity defect found. The final endpoint proves the positive-integer conjecture without residual mathematical hypotheses. Root decides acceptance, novelty, significance and credit; this review claims zero credit.

## Inputs and boundary

The binding TASK.txt and the three requested AGENTS.md files were read first. All work was performed without child agents, git commands, network access, external messages, browser tabs, shared ledger edits or writes outside this lane. The 14 specified read-only inputs were SHA256-bound before extraction in before.json and rehashed after verification in after.json; the dictionaries are identical. These include the four r4 documents, four predecessor summaries, ordinary proof and review files, and both TeX sources. The packet hash is `3a599c52f33e8fcbed9294de07b9b6a549606b7d6bd693fdfd834304a67173b4`, as required. All 51 extracted packet files remain byte-identical to the archive (extracted-source-hashes.json). No inherited Lean source was edited.

References to PDTAR files below mean the hash-bound files under extracted/PDTAR/. Source means pdtar-proof-r1/sources/r119-cached/2201.01798-PD-recon.tex; survey means the adjacent 2406.05509-CFH24TARarxiv.tex. Line numbers are one-based. This is a bounded formal spot check, not root's decisive full replay.

## A. Definition fidelity — PASS

* Defs.lean:10–12 defines closed by membership or adjacency to a member: exactly N[S], using undirected adjacency (source:177).
* Defs.lean:14–17 retains O and adds a neighbour u of an observed v when every neighbour outside O equals u. For u outside O this says N(v) minus O is the singleton u; for u already inside O it changes nothing. SmallStatement.lean:9–35 proves the literal singleton-difference equivalence. No sequential update is hidden in this definition.
* Defs.lean:19–25 iterates that simultaneous step: propagate 0 is its input, obs 0 is S, obs 1 is closed S, and obs(n+2) is step(obs(n+1)). This agrees with source:193–201, including the initial domination round. IsPD at Defs.lean:27 is eventual equality with all vertices. The source starts with nonempty S; SmallStatement.lean:65–70 excludes the empty set on every nonempty vertex type. My independent induction proves the same fact at ReviewerExamples.lean:65–82.
* Defs.lean:30–32 requires a nonempty fort and a second distinct neighbour in it whenever an outside vertex has one neighbour. This is exactly the survey:411 cardinality condition; SmallStatement.lean:37–63 proves that equivalence. FortDuality.lean:40–67 derives fort duality from these actual rounds and finite stabilization; it does not redefine PD.
* NoIsolated (Defs.lean:34) means every vertex has a neighbour. tar (36–39) has all PD finsets as vertices and symmetric-difference cardinality one as adjacency: source:425–426, with no artificial cardinality cutoff. Equality is not adjacency.
* TARUnique (Defs.lean:42–44) is source:568, with isomorphism orientation reversed harmlessly. W has no prescribed order or connectedness. It includes every finite graph isomorphism class via universe-zero Fin n representatives and exact round transport (ReductionTransport.lean:13–74).

The two domain differences are harmless here. First, the source defines uniqueness only when G has no isolated vertices; sum_noIsolated (CoreProofAssembly.lean:22–27), also small_sum_noIsolated (SmallObligations.lean:29–34), proves this for every s,t at least 1. Second, Lean permits empty W. small_empty_comparison (SmallStatement.lean:71–78) rules out its TAR isomorphism to the positive target by applying the unconditional reduction and pulling back an actual target vertex into W. The reduction includes empty types: its degree bound/top argument (ReductionCube.lean:45–82) uses no Nonempty instance. Thus this exclusion is not circular. On empty W, PD consists of its sole empty subset and TAR has one vertex.

The target graph is the actual mathlib completeBipartiteGraph on Fin s ⊕ Fin t; sum_parts (CoreProofAssembly.lean:10–20) proves precisely disjoint covering parts with all and only cross edges. Positivity is the source's coherent range: nonempty graphs at source:177 and no isolated vertices at source:568 exclude zero parts. The endpoint matches the conjecture at source:738 in that range.

There is no PD-family or isomorphism vacuity: the full set is PD (Basic.lean:48), the empty set is not PD on nonempty types, examples include both outcomes on the same graph, identity yields a TAR automorphism, and the actual added-edge witness gives a TAR isomorphism between nonisomorphic base graphs (SmallTwoWitness.lean:21–42).

## B. Endpoint and discharged obligations — PASS

FinalComplete.lean:5–7 applies Final.mathdb_353203_conditional (Final.lean:19–23) to starRigidityRemaining and threeThreeRigidityRemaining. The conditional assembly in CoreSmallProof.lean:23–58 covers exactly: (1,1), both star orientations with at least 3 leaves, (3,3), every other pair with both parts at least 3, and all positive pairs having a part of size 2. Arithmetic case splits preserve precisely hs and ht.

Every Prop in Remaining.lean and SmallObligations.lean is supplied by a proved theorem, directly or by specialization:

| Prop | Discharge and use |
|---|---|
| ReductionRemaining (Remaining:6–10) | reductionRemaining, ReductionProof:5–17 |
| CoreRemaining (Remaining:13–16) | coreRemaining, CoreSmallProof:5; core_remaining_proved, CoreProofFinal:6–16 |
| EdgeRemaining (Remaining:18) | edgeRemaining_of_reduction reductionRemaining, CoreSmallProof:11–12; SmallEdge:39–49 |
| StarsRemaining (Remaining:19–21) | stars_of_rigidity reductionRemaining starRigidityRemaining, SmallObligations:36–48 |
| ThreeThreeRemaining (Remaining:22) | threeThree_of_rigidity reductionRemaining threeThreeRigidityRemaining, SmallObligations:50–55 |
| TwoRemaining (Remaining:23–24) | two_of_witness twoWitnessRemaining, SmallObligations:57–60 |
| StarRigidityRemaining (SmallObligations:6–12) | SmallStarComplete:5–31, both orientations |
| ThreeThreeRigidityRemaining (SmallObligations:15–18) | SmallK33Complete:41–143 |
| TwoWitnessRemaining (SmallObligations:23–26) | SmallTwoWitness:67–71 |

These statements are genuine universally quantified claims with appropriate size restrictions, not True aliases or implications with impossible generic premises. Complete bipartite graphs and reflexive SamePD instantiate the rigidity/core antecedents. The size-2 witnesses are constructed explicitly. Historical OPEN/unproved comments describe earlier packets and do not survive as hypotheses in the endpoint.

ReductionRemaining is exactly the PD specialization of survey Theorem t:main (survey:764–765): from no-isolation and a TAR isomorphism, obtain H' on G's vertex type, isomorphic to H, with precisely G's PD sets. It requires neither fixed labels nor that the original TAR isomorphism itself be induced by a coordinate permutation. The replacement proof is sufficient in full:

1. ReductionCube:45–82 obtains equal base orders from maximum TAR degree; the full set attains the order, without asserting it is the only vertex to do so.
2. ReductionBasis:17–48 gets the coordinate bijection from images of the distinct co-singletons.
3. ReductionPaths:10–97 constructs union walks of Hamming length and bounds every walk below by Hamming distance. Mapping walks through the isomorphism and inverse proves ReductionHammingRemaining (ReductionMetric:7–11), with no additional hypotheses.
4. ReductionMetric:16–61 reconstructs the affine coordinate action from distances to the full set and co-singletons, and uses surjectivity for an iff on all sets.
5. ReductionFlip:12–44 removes the flip using upward closure in both directions. ReductionTransport:77–82 pulls adjacency back and proves exact SamePD, using the proved transport of each round.

The core proof derives no-isolation, two-sided cross-degree bounds, cross-completeness and internal independence (CoreProofLocal:8–31; CoreProofDegree:88–116; CoreProofComplete:77–152; CoreProofIndependent:50–68). It excludes (3,3) exactly where needed and swaps the larger side in CoreProofFinal:12–16.

The star proof establishes labelled equality via supported pair forts, centre/leaf singleton distinction and a third leaf (SmallStarLocal:6–108; SmallStarRigidity:8–121). K(3,3) proves every pair PD and singleton non-PD, forces degree three, then builds a balanced bipartition with a two-vertex fort (SmallK33Local:6–69; SmallK33Degree:7–41; SmallK33Complete:41–143). These replace published small-case arguments with real proofs. The size-2 witness covers t=1 as P3 versus K3 and t≥2 uniformly; triangle obstruction proves nonisomorphism, including the swapped case. No enumeration replaces an obligation.

## C. Independent semantic sanity — PASS

My own ReviewerExamples.lean compiled strictly against the extracted endpoint. It is not a copy of the packet's negative fixtures. Checks are:

* K(2,3): left singleton is PD by round 2 (line 8); right singleton is not PD, using a separately constructed opposite unobserved pair fort (line 16).
* K(3,4): mixed pair dominates in round 1 (line 38); two left vertices are PD by round 2 (line 43); left singleton is not PD (line 53, specializing K3's pair obstruction).
* Empty sets are not PD on any nonempty finite graph, by my direct induction on the literal rounds (line 65).
* K(2,3): the left singleton and its extension by a right vertex are TAR-adjacent (line 84).

These agree with K1–K3 (KstFamily:26–85; PROOF.md:79–82) and source k2tminimalsets (source:629–635). Independent python3 -I synchronous rounds reproduce every result, with full observed sets in logs/review-python-rounds.log. The Python is only a sanity check, not a formal proof. Successful Lean log: extracted/logs/review-examples-5.log. Four earlier failed development attempts are preserved; they were local tactic/linter errors, not packet failures.

## D. Bounded formal spot check — PASS

All 34 modules in the local import closure of PDTAR.FinalComplete were compiled serially from the source-only archive, using Lean 4.34.1, -j1 -M3500 -DwarningAsError=true -DElab.async=false. Full per-module output and resource receipts are under extracted/logs/; build-driver.log lists all 34 successful steps. The local closure equals all 34 supplied modules (source-scan.json, independently checked and confirmed inside the Lean audit).

leanchecker PDTAR.FinalComplete exited 0 (review-leanchecker-final.log and receipt). ReviewerExamples.lean:90–92 prints the axioms of mathdb_353203, coreRemaining and reductionRemaining: each is exactly propext, Classical.choice and Quot.sound. Running the inspected packet audit on the rebuilt closure reports 318 declarations and zero violations (review-declaration-audit.log), including generated declarations and checks of unsafe/partial flags, implemented_by, extern and all transitive axioms. My raw-token scan of all 34 mathematical modules finds none of sorry, admit, axiom, unsafe, partial, native_decide, ofReduceBool, implemented_by or extern. The audit script itself necessarily mentions forbidden names as checks; it is not an imported mathematical module.

Every heavy process used the inspected lane-local limited.py: affinity at most 2 CPUs, RLIMIT_CPU 120 seconds, wall limit 140 seconds, sampled process RSS limit 6 GiB, MALLOC_ARENA_MAX=2, local TMPDIR/XDG_CACHE_HOME; only one heavy process ran at a time. RLIMIT_AS is 16 GiB to accommodate mappings; this is distinct from the 6 GiB sampled RSS cap. Maximum sampled RSS was 3,533,508,608 bytes and longest process was 10.688 seconds. No cap was reached; sampling cannot exclude unsampled peaks. No background process remains.

The exact configured binaries and mathlib Basic source match the packet manifest pins; the read-only mathlib checkout HEAD is d13f23b723b8a846827a245b89c10fc7d3f11612 (toolchain-verified.json). Toolchain pins were verified during the review after closure compilation, rather than claimed as a pre-build independent hash snapshot. The 14 specified source inputs were bound before extraction. No cache or toolchain writes were requested. This review did not repeat all 34 leanchecker calls or the seven expected-failure controls of the implementation packet: root's decisive replay remains separate.

## E. Manuscript readiness — QUALIFIED_PASS

The correspondence is sound, but PROOF.md is not yet a final manuscript. It must state the exact positive-integer quantifiers, finite simple graph scope, source definition of uniqueness and the two harmless domain extensions above; define PD by simultaneous rounds and TAR by one-token symmetric difference; identify SamePD as a labelled-family condition; state the unconditional Lean signature and archive/toolchain hashes; distinguish the formal Hamming reduction and new star/K(3,3) arguments from the cited published proofs; list the axiom budget and this bounded check separately from root's fresh replay. Formal correctness alone does not establish novelty or significance.

Carry forward all seven non-blocking prose fixes numbered 1–7 in pdtar-review-r1/REVIEW.md:293–299 (the JSON groups the two optional edits together):

1. At PROOF.md:36 and 200 cite source pd-deg-dist(1), or survey x-deg, for maximum TAR degree equalling base order. c:pd-iso-props(1) supports equality of base orders under TAR isomorphism.
2. At PROOF.md:31 add DOI 10.1007/s00373-023-02677-1 and Graphs Combin. 39(4), 2023; verify or drop article number 86.
3. At PROOF.md:25 justify positivity using source:177 and 568; exclude empty graphs and zero-part cases explicitly.
4. Qualify the journal numbering and journal conjecture-status claims (PROOF.md:10, 201–202, 220; predecessor SUMMARY:38–40) as unverified search-engine evidence. Preserve the earlier review's reported access failures (Springer/Swarthmore denied, Iowa State timeout, AIM 404, SelectedWorks retired), and distinguish its indirect survey evidence from direct reading of the journal text. I made no new prior-art/access checks in this lane.
5. At PROOF.md §8, explicitly call fort duality (Lemma 0) standard; locate the claimed new ingredients in Lemmas 1–6 rather than implying the duality is new.
6. Optional strengthening: state that the core uses only K1–K3; explain this from the proof rather than presenting finite computation as proof.
7. Optional cosmetic clarification: Lemma 6's second branch is contradictory independently of the initially selected a; the formal core_complete_large makes this explicit.

The earlier review also has a separate Lean item 8 (REVIEW.md:300; L1–L3 at 282–289). This review discharges it: target no-isolation, empty W and full proofs of reduction/stars/K(3,3) are all accounted for in A–D. No blocking Lean fix is requested. Required manuscript edits above remain editorial qualifications, not a reason to change the endpoint or silently edit read-only inputs.

## Reproducibility and handback

The retained scripts are extracted/scripts/build.py, compile.py, check.py, limited.py and Audit.lean (unchanged packet scripts, inspected before use), my finish-checks.py, scan.py, verify-inputs.py, extracted/ReviewerExamples.lean and extracted/reviewer-rounds.py. Build from a fresh extraction with the build script; after a successful build, finish-checks.py runs the final examples, leanchecker and audit. Its exclusive log names intentionally refuse reuse; use fresh tags for a repeat. Run the Python rounds through limited.py and verify-inputs.py after all checks. All full formal logs, including unsuccessful example diagnostics, are retained. before.json and after.json contain every exact input path and SHA256; review.json duplicates the bindings and summarizes results.

Recommendation: no formal-fidelity blocker found; finish the manuscript qualifications and let root perform and adjudicate the decisive replay. NOT self-accepted.
