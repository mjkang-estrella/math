# Sustained routes and their dispositions

## 335230: closed ordinary proof and full Lean candidate

First reviewed the literal target and source simplex/overlap definitions; checked current public proof registry receipts and title/author/target searches before the grid investigation. Read v1, v2 and the author manuscript's relevant definitions and general/two-color proofs. The source's total-defect averaging bound is not enough to prove the conjecture: at m=4,k=3,a=2 it only yields total defect at least 8, hence maximum at least 1, rather than the proposed 2. The argument that whole-part replication is always optimal has no justification: a minimum of concave overlaps under a maximum need not be preserved by symmetrizing vertices in an independent part.

Second, searched rational simplex colorings modulo vertex permutations within a part and permutations of parts, without forcing each part to be constant. Integer sums of coordinatewise minima were used, with no floating point. Six exact finite grids were exhausted: 10,626; 53,130; 455,126; 424,270; 888,030; and 5,006,386 configurations respectively. The last four include violations at m4,a3,k3,q2; m4,a2,k3,q3; m5,a2,k4,q2. The three-color eight-vertex witness was selected; other witnesses have zero separate credit. Grid optimality is not claimed for the continuous source problem.

Third, independently recomputed the eight-vertex witness with Python Fraction arithmetic, then proved the real-valued source conditions, vertex defects, graph maximum bound, minimum predicate refutation, infimum bound, and universal negations in Lean. No enumeration or external solver is trusted by Lean. Final extracted strict replay passes. See PROOF.md, lean/FractionalDefect.lean and replay/final-extracted/replay-result.json.

Remaining: independent adversarial fidelity/significance/novelty/formal review; Xu thesis body blocked by official download403; possible journal version unidentified; source/citer coverage remains bounded; manuscript and root acceptance later. Zero accepted credit.

## 334900: no closed upper-bound route

Read original labeled-chip definitions, Lemma12 position bounds, the complete even sorting proof (Theorem13 with internal Lemmas14–15), and odd-case Conjecture26. Published paper labels the corresponding conjecture27; this numbering difference is explicit. Read the later Klivans–Liscio2020 Section4 passage retaining the odd inversion upper bound as Conjecture4.2; did not audit the entire later paper's proof machinery.

Attempt1: transfer even sorting induction after adding/removing one chip. It needs uniqueness of the smallest extreme label at the outermost site; this is explicitly parity-sensitive in the original proof. The odd position bound permits multiple extreme labels. The added-chip sorted result is only a necessary condition; source itself gives an unreachable permutation satisfying its stated necessary conditions. No way to count inversions from that extension was established.

Attempt2: optimize complete legal schedules, choosing an unstable site and two labels there, sending the lower left and upper right. Mutation hill climbing plus periodic random restarts tested 246415,146049,92667,61403,30900 schedules for n11,13,15,17,21 respectively. The move count is checked against sum(i^2), and all output is terminal. No inversion count exceeded m. The severe drop in best found inversions at larger n indicates search bias, not a better bound. Known construction holding chip1 fixed gives m inversions but is already source content and uncredited.

Attempt3: exhaust position-bound-compatible terminal permutations at n5,7,9, independently of reachability. The maximum allowed inversions are 3,6,10, all above m=2,3,4. Thus the elementary label-position invariant alone cannot prove the target; these are NOT reachable counterexamples. A genuinely stronger invariant or a legal violating schedule is still needed. No Lean partial result is promoted.

## 334986: alphabet-merging shortcut has a concrete obstruction

Read original word/factor/Parikh/abelian-square definitions and Conjecture27. These count distinct factors, not occurrences or equivalence classes of Parikh vectors. The existing abelian-square-rich constructions give asymptotic lower bounds and do not prove exact extremality at every length. No complete proof audit of those unrelated richness theorems is claimed.

Attempt1: seek a letter-to-bit map that preserves at least the original number of distinct abelian squares. Every abelian square remains abelian after mapping, but distinct squares can collide; this is the missing inequality. Exhaust all canonical words (arbitrary alphabet via restricted growth strings) through length9 and every binary letter quotient. Binary maxima were 0,1,1,2,3,4,5,7,9 and no quotient failure appeared. This is finite evidence only.

Attempt2: targeted ternary-word mutation, optimizing original count minus best binary quotient count. At length16 the word 0200200002221122 has 13 distinct abelian squares but every binary alphabet quotient has at most12. Larger examples occur at lengths24 and32. This explicitly defeats the proposed universal quotient argument. It does not defeat the actual conjecture: the source may choose any binary word of the same length, and known binary examples at length16 already have26 distinct squares. No arbitrary-binary extremality counterexample or alternative universal construction is obtained.

The source comparison search found Simpson2018 survey and a recent circular-minimum result. Those search passages are not full-body audits and are different scopes (maximum versus minimum, linear versus circular). No novelty inference follows from the search. Parked with precise missing obligation: construct an unrelated binary word preserving count, or beat the true binary maximum with a full all-binary certificate.

## Other targets and historical reconciliation

All40 literal records were read, preserved, and assigned individual reasons/remaining obligations in results.json. Only the above three received sustained mathematical attempts. 335392's original expansion/torsion definitions and conjecture passage were additionally read; the 2026 group-theory successor was only a search passage, not audited or claimed to settle it. 334645's current primary abstract says the source proves the bound; this is a known-result exclusion cue, not a proof-body review. Literal statements for 334944 and335224 themselves report proofs and are not promoted from open labels.

Historical matching initially used naive substrings and found many hash/numeral false positives. Exact six-digit-token reconciliation removed those; only the current ledger reservation remains in the scanned named result/review/context/coverage files. This bounded scan is not an exhaustive historical-body audit. Parent prior-campaign-context.json and current ledger were read; the reservation is disjoint only against its listed inputs. Prior exclusions remain:320321 wording/mate noninvariance;325519 generic spectral cardinality;327346 known graph extremizer;328367 known guard theorem;328705 routine Fermat adaptation. Accepted388087 remains one credited result;330264 remains held and was not investigated. Another worker's333569 was not touched. No ledgers or shared files were written.
