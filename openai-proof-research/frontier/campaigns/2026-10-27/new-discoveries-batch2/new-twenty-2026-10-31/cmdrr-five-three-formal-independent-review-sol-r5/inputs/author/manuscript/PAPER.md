# Nonexistence of a complete mixed doubles round robin tournament CMDRR(5,3)

MathDB 326555 - source-bound theorem and Lean 4.34.1 certificate

Implementation record, 8 November 2026 UTC. Credit 0. Campaign 55/60 beyond 39 prior results. Independent final review and root acceptance are unpaid.

## Abstract

No CMDRR(5,3) satisfying Berman and Wakeling Definition 1.2 exists. Games are unordered pairs of mixed teams and schedules are arbitrary finite collections of occurrences. Three arbitrary disjoint spouse pairs are allowed; neither rounds nor resolvability is assumed. The essential incidence identity A+B=1+z rules out the undetermined 3+2 cycle type in either single row. Sex-swap correspondence then determines all column cycle types. The signs of the row, column and opposite-team permutations contradict their actual composition relation. The literal universal endpoint is kernel checked, and an empty-build source-only replay with module checkers passed. This is an implementation result awaiting independent scientific and process adjudication, not a new-to-literature or acceptance claim.

## Source statement and conventions

The source is David R. Berman and Ian N. Wakeling, Complete Mixed Doubles Round Robin Tournaments, arXiv:1310.5240v1 (19 October 2013), Definition 1.2 on PDF pages 2-3 and Conjecture 2.4 on page 5; the cached published scan places the definition on printed pages 66-67 and the conjecture on page 69. Exact cached files and source hashes are frozen inputs. The MathDB literal delegates the term to the paper; its gloss of k as games/rounds is inaccurate. Here k means disjoint spouse pairs, exactly as in Definition 1.2.

For n men and n women with k disjoint spouse pairs: spouses never share a game; nonspouse mixed pairs partner once and oppose once; a player with a spouse opposes every same-sex player once; each single repeats opposition twice with some other single and opposes all remaining same-sex players once. A mixed game has two different men and two different women. All multiplicities count occurrences, not ordered displays. The proof below uses labels H={1,2,3} and singles 4,5. The Lean canonical model subtracts one from every label, so spouses are 0,1,2 and singles 3,4. A, B and z are unchanged occurrence counts under this stated bijection.

## Theorem

For arbitrary types M,W with Fintype instances, not ExistsFiveThree M W. Expanded: if both cardinalities are 5, any matching of exactly 3 spouse pairs admits no finite occurrence schedule satisfying Source. The occurrence type is quantified inside the existence proposition. No incidence identity, cycle fact or sign premise is supplied as an additional hypothesis.

## Exact object and normalization

A game is an unordered pair of mixed teams { (M_i,F_j), (M_k,F_l) }, with i different from k and j different from l. A schedule can initially be regarded as a finite collection of game occurrences. Opposing and partnering multiplicities count occurrences, not ordered displays of teams. There are five distinct players of each sex and three disjoint spouse pairs. Enumerate the three pairs arbitrarily and label the male and female in each pair by the same element of H={1,2,3}. Label the two remaining players on each side arbitrarily by 4,5. These are bijective relabelings of each player set. Transport every game occurrence along them; partnership, opposition, and co-occurrence counts are preserved because relabeling induces bijections on occurrences of every relation. Thus a contradiction for the canonical spouse relation proves impossibility for any spouse matching of size three.

The source conditions become: spouses M_i,F_i for i in H never share a game; every other mixed pair partners once and opposes once; every same-sex pair opposes once except the pair of singles {4,5}, which opposes twice. The last assertion follows directly from the definition: a single must repeat opposition with another single, and only one other single exists. There are 25-3=22 allowed partnership cells X. Each occurs in exactly one game, and each game contains exactly two such cells, distinct because its two men and two women are distinct. Consequently there are eleven games. No partnership cell can belong to two distinct occurrences; in particular repeated copies of the same game would violate uniqueness. Switching team order does not create another occurrence.

## Genuine row and column bijections

For a man i let S_i be all women except his wife, if any. Given j in S_i take the unique game where M_i partners F_j and let p_i(j)=l be its opposing woman. This lies in S_i by spouse avoidance, and differs from j by distinctness of women in a game. For every l in S_i the unique game where M_i opposes F_l has a unique female partner F_j; that j gives an inverse to p_i. Thus p_i is a permutation, not merely a map with an assumed surjectivity. Its domain has size four for i in H and five for i=4,5. Each game involving M_i contributes one directed edge j -> p_i(j) and exactly one cell in row i; there is no division by two here.

Similarly, for a woman l define q_l(k)=i in the unique game where F_l partners M_k and opposes M_i. The unique mixed-opposition occurrence supplies its inverse. It is a fixed-point-free permutation of her allowed men, with the same domain sizes. This convention is partner-to-opponent in both sexes.

## Spouse rows and the structural identity

If p_i has a two-cycle (a b), its edges a -> b and b -> a come from two distinct games: M_i has different partners in them and has just one partner within any game. Both games contain the female pair {a,b}. The global female opposition count permits a repeated pair only when {a,b}={4,5}. This establishes the restriction for every row.

Every finite permutation partitions its domain into disjoint cycles: successive iterates of an element first return to it by bijectivity, and intersecting orbits coincide. No fixed point means every cycle length is at least two. On four elements the only possibilities are a four-cycle or two disjoint two-cycles. Two disjoint two-cycles would repeat two different female pairs, whereas only one female pair may repeat. Hence each spouse row is a four-cycle on {j,k,4,5}, where H minus {i}={j,k}.

The four directed edges of a four-cycle yield four distinct undirected edges: an undirected edge could repeat only if both directions occur, which would be a two-cycle. Each vertex has undirected degree two. Let e be the indicator for the edge {4,5}, f the indicator for {j,k}, and c the number of edges between these two pairs. The degree sum on {4,5} is 4=2e+c and on {j,k} is 4=2f+c. Thus e=f. This supplies the opposite-edge bridge without enumerating cycles or schedules.

Let A be the number of games having both men in H and women {4,5}; B the number having men {4,5} and both women in H; z the number having both the male and female pairs {4,5}. These are nonnegative integer counts of game occurrences. Sum e=f over the three spouse rows. Exactly two games contain the female pair {4,5}. Among them A contain two spouse men, z contain none, and 2-A-z contain one. The e-sum therefore counts spouse-man incidences in those games and equals 2A+(2-A-z)=2+A-z.

For the f-sum fix an unordered pair {j,k} in H and let i be the third member. There is exactly one game containing F_j,F_k, since they oppose once. Neither M_j nor M_k can participate because each would share a game with his wife. The two men must therefore form one of {i,4}, {i,5}, {4,5}. In the first two cases that game contributes exactly once to f, in row i; in the last case it contributes zero. Each pair in H has exactly one complementary index i, and there are three such female pairs. Exactly B of their games use men {4,5}. Thus the f-sum is 3-B. Equating the sums gives

                 A+B = 1+z.                     (*)

This identity uses only the already proved spouse-row four-cycles; it does not presuppose the type of any single row.

## Elimination of every single-row two-cycle

Suppose p_m for a single man m has a two-cycle. Its support must be {4,5}. The remaining three elements of the permutation cannot have fixed points; hence form one three-cycle, on H. The two games of its two-cycle are distinct and contain F4,F5; the global count of that female pair is two, so they exhaust those games. Both contain M_m and consequently none can have two spouse men. Therefore A=0. All other games of M_m correspond to the three edges of the three-cycle on H and have both women in H.

Let t be the other single man. The pair M_m,M_t opposes in exactly two games. Exactly z of them have women {4,5}, by the definition of z. Every other such game, because it contains M_m, belongs to his remaining three games and has women in H. Conversely every B-game has men {m,t}, so contains M_m and is one of these two games. Hence B=2-z. Equation (*) now gives 2-z=1+z, or 2z=1, impossible for an integer. Explicitly, z=0 gives 0=1, and z>=1 gives 2z>=2. Thus neither single row has a two-cycle.

A fixed-point-free permutation on five elements has cycle lengths at least two. If it has more than one cycle the only partition of five into such lengths is 2+3, which includes a two-cycle. Consequently each single row is one five-cycle. This is cycle-length reasoning, not enumeration of schedules.

Definition 1.2 and all arguments above are invariant under interchanging men and women. Apply the entire argument with the sexes exchanged, including its own identity (*) and its single-column contradiction. Thus the three spouse columns q_l are four-cycles and the two single columns are five-cycles. Merely asserting that a column must have the row type without this symmetry of hypotheses would not suffice.

## Permutation sign contradiction, with direction and domains

Define U on X by U(i,j)=(i,p_i(j)), and C on X by C(k,l)=(q_l(k),l). Their inverses are assembled from the already constructed row and column inverses, so both are genuine permutations of X. A cycle of length r is a product of r-1 transpositions (fix one vertex and successively swap it with the other cycle vertices); its sign is (-1)^(r-1). Sign is multiplicative and is unchanged by extending a permutation to act identically off its support. The row supports partition X. Hence U has three four-cycles of sign -1 and two five-cycles of sign +1, giving sign(U)=-1. The same reasoning on column supports gives sign(C)=-1.

For x=(i,j), let the unique game of that partnership have opposing team (M_k,F_l), and set T(x)=(k,l). This lies in X. The unique game of (k,l) is the same game, since that partnership already occurs there; therefore T(T(x))=x. It cannot fix x because the teams have different men and different women. Its two-element orbits are exactly the two partnership cells of individual games. There are eleven such orbits, so T is eleven disjoint transpositions and sign(T)=-1.

In the same game F_l partners M_k and opposes M_i; thus q_l(k)=i. Consequently C(T(i,j))=(i,l)=U(i,j) pointwise. Taking signs of C composed with T=U gives (-1)sign(T)=-1 and hence sign(T)=+1. This contradicts sign(T)=-1. No admissible schedule exists.

The conclusion is the asserted nonexistence, not a refutation of nonexistence. It applies to all games satisfying the source multiplicities with three arbitrary disjoint spouse pairs. No extra assumptions have entered the proof. The formal endpoints and validation evidence are described below.

## Formal source-to-definition and proof map

CMDRRBase defines Game as a Finset of exactly two mixed teams with distinct men and women, Matching as a partial one-to-one spouse relation, Schedule.game on an arbitrary occurrence type, count as filtered cardinality, and Source as the six literal multiplicity clauses. ExistsFiveThree quantifies both cardinalities, the matching with count 3, and a finite occurrence type and schedule. No conclusion is included in a structure field.

CMDRROccurrence proves mixed partnership and opposition uniqueness and derives occurrence injectivity. CMDRRCells constructs the actual incidence-to-cell equivalence and opposite-team involution T. CMDRRRows constructs genuine U and C and proves C(T(x))=U(x). Counts gives 22 allowed partnership cells and 11 occurrences. Transport, SourceTransport, Normalize, Canonical and NormalizationBridge prove synchronized relabeling and canonical_transport for arbitrary five-element player sets.

Repeat, SingleCounts, Cycles, FourOrbit, OrbitCard, RowDomain and SpouseCycles establish the genuine restricted row permutations, forced repeated single pair and spouse-row four-cycles. Degree and RowDegree prove complementary internal directed-edge counts by bijective degree balance. Incidence and ZeroA preserve actual two-cycle occurrences and define exactly A, B and z as used in the proof.

IncidenceSums partitions actual occurrences. RowOccurrences proves a bijection from actual row edges to occurrences containing the chosen man, preserving both female endpoints. GameIncidences proves the per-game spouse-man incidence formula. WeightedOccurrences performs Fubini and obtains the single-female incidence sum plus z = 2+A. FemalePairs uses the three unordered pairs in H, spouse avoidance, and occurrence multiplicities to obtain the married-female incidence sum plus B = 3. CentralIdentity proves A+B=1+z without a single-row type premise.

SingleElimination proves preservation of the single-female subset by an oriented two-cycle, the full occurrence partition, B+z=2, the odd-integer contradiction and the arbitrary-orientation bridge. FiveOrbit uses cardinal complements and injectivity to exclude 3+2 and 4+1 decompositions, proving the full five-cycle. This is not an enumeration of permutations or schedules.

Transpose proves the canonical sex-swap source and the explicit swapped U/original C correspondence, including column_cell_correspondence on the actual column domain. ColumnCycles records spouse-column four-cycles and single-column five-cycles. RowSigns proves row signs from actual single-cycle support, and extends each row by the identity on a forbidden wife cell. The disjoint row product has sign -1. Signs bridges the extension to the original 22 cells, applies the entire row argument to the swapped Source for C, obtains signT=-1 from the fixed-point-free involution, and proves the contradiction.

Nonexistence contains canonical_noSource, noSource_five_three and universalExistsFiveThree_negation. The arbitrary endpoint depends transitively on canonical_transport and on the actual Source, A, B, z, central incidence identity, elimination, five-cycle and permutation-sign declarations. The audit explicitly checks their membership in the endpoint closure. ColumnCycles is an explicit additional record of the column classifications; the endpoint sign chain uses the same swapped row classification through canonical_swap_source.

## Validation and reproducibility

Lean is 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52, with mathlib revision d13f23b723b8a846827a245b89c10fc7d3f11612. PINS.json is immutable; actual version, executable hashes and package metadata were checked. Every compile uses -j1 -M3500 -DwarningAsError=true. Permitted transitive axioms are exactly propext, Classical.choice and Quot.sound. No added axiom, sorry, admit, unsafe, native_decide, unchecked certificate or schedule search is used.

CMDRRAuditFinal enumerates the entire imported environment with module origins and body presence, selects production declarations by actual originating modules (including private/generated declarations), traverses types and opaque bodies into an origin-labelled dependency DAG, and prints 15 individual exact endpoint closures and axiom unions. It rejects any disallowed production axiom. This machine audit is not an independent human proof review.

The full replay copied every current Lean source into extracted-r4/src and asserted an empty extracted-r4/build. LEAN_PATH included only that build and pinned upstream packages. Each source compiled strictly in dependency order, then each module passed leanchecker by module name. Original and extracted source hashes were equal before compilation and after every checker completed. No old author or legacy olean was used as a replay input. REPLAY-R4.json and separate true-exit receipts preserve the evidence.

Controls construct the source-valid two-game strict MMDRR(2), test both the one-time mixed partnership and twice repeated single opposition, unordered team symmetry, distinct occurrences, duplicate-partnership detection and a forbidden-spouse violation. Clean isolated copies of Source and this positive object compile without any author modules. Changing repeated same-sex multiplicity from 2 to 1 or mixed partnership multiplicity from 1 to 2 rejects the same positive object with the intended false-proposition diagnostic. The first negative attempts also had a missing sum_boole import and are retained as contaminated failures, not counted as clean controls; corrected identical imports make the unmutated control pass and both semantic mutations fail.

Small explicit control objects, three unordered female pairs, fixed integer/sign calculations and structural four/five-point orbit arguments are kernel-proved. They are not an enumeration of candidate tournament schedules. No mathematical Python, solver, CAS, numerical experiment, new network access or child delegation was used.

## Scientific and process limits

The ordinary proof was independently reviewed in the copied prior source-review record. No independent final source-to-Lean, deep-body, proof or manuscript review has occurred for this completed certificate. Root acceptance and process adjudication remain separate and unpaid. Credit remains 0; the shared campaign ledger remains 55/60 beyond 39 prior. No files outside the exclusive lane were authored and no ledger or git operation was performed.

The bounded prior review did not identify an authenticated applicable prior theorem in the inspected source bodies. The Berman-Smith 2013 companion body returned HTTP403 and remains unread; prior registry-body coverage is limited. These facts do not establish worldwide novelty. No new access or alternate retrieval is claimed in this continuation.

The historical r3 process breach remains UNRESOLVED and UNACCEPTED: an initial workspace-root recursive inventory may have traversed protected metadata; its interrupted run lacks a normal runner receipt and normal group-reap evidence. No protected body bytes were reported read. Later hashes and completed receipts do not cure that missing evidence. The r4 immutable runner changes cwd to its own lane before child dispatch; that prospective repair is not a retroactive waiver.

All r4 exec commands explicitly used the assigned absolute workdir. Substantive reads, Lean execution, audits and rendering used the immutable runner. The root prospectively authorized standalone documentary display of explicitly named own saved logs with timeout20, CPU10 seconds, address-space512MiB and affinity at most2, installed before file reads. Displays are capped at16KiB and tracked with offsets and exits. These displays did not run through the compiler runner and have no sampled group or native UI telemetry. One mistyped own-log timestamp caused FileNotFoundError; no external path was accessed. A wrong lane-relative PDF-marker path returned MODULE_NOT_FOUND; the corrected installed absolute marker succeeded once before current-lane PDF authoring. ReportLab was absent; groff PDF-device and MS-macro attempts failed. Installed plain roff/PostScript generation succeeded, and a pending-line footer issue was fixed after visual inspection. These failures and the rendering retry on an invalid PDF are retained. The initial direct runner-helper display and the first failed visibility handback are preserved in the process inventory.

Runner caps are CPU120 seconds per process, address space12GiB, at most2 CPUs, sampled groupRSS guard6GiB, devguard130 seconds and wall140 seconds, with arena2 and own temporary/cache paths. Completed receipts record true exits and reaping notes; sampling is not a perfect cgroup claim. No blanket procedural PASS or independent acceptance is asserted.

## References and retained evidence

[1] Berman and Wakeling, Complete Mixed Doubles Round Robin Tournaments, arXiv:1310.5240v1, Definition1.2 and Conjecture2.4, cached original and published scan in inputs/original/original/author/sources.

[2] MathDB326555 exact literal: inputs/original/original/author/literal326555.jsonl. Source-bound interpretation and independent ordinary proof: inputs/original/original/review/REVIEW.md and INDEPENDENT-PROOF.md.

[3] Current source certificate: src/CMDRRNonexistence.lean and its imported modules. Full body audit: src/CMDRRAuditFinal.lean, audit/FINAL-AUDIT-SUMMARY.json and audit/ENDPOINT-CLOSURES.json. Replay: results/REPLAY-R4.json. Exact receipts, hashes and process limitations are retained in results/326555.json, CHECKPOINT.md and the terminal manifest.

Audit totals: 271358 environment declarations; 444 production declarations; 9733 reachable body/type nodes; 15 exact closures. Full replay: 39 source modules. Universal endpoint closure: 9562 declarations.
