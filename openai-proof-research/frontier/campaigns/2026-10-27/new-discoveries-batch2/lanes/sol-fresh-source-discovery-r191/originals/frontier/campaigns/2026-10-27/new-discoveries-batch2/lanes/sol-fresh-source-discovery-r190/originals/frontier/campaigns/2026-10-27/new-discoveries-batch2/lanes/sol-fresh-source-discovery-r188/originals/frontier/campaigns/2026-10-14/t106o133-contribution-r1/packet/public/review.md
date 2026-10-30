# T106O133 contribution review, round 1

Reviewer: Factory Droid / claude-opus-5-5, independent contribution reviewer, 2026-10-20.
Pin: openai/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (stipulated true, including its operative proof operations).
This is the first independent contribution review of T106O133. There are no prior independent verdicts.
I did not read proof-review briefs or results, or any other active review.
This review assigns no correctness gate, acceptance or count.

## 1. Verdict

**TECHNICAL**, conditional on the full unchanged frozen theorem (Theorem A and all of Corollary B) being correct.

- Not REDISCOVERED. I found no prior statement of Theorem A or of an unconditional Brakensiek-Guruswami (BG) theorem in any source I read (Section 6). Worldwide priority remains unresolved within the stated limits. That does not affect the TECHNICAL classification.
- Not SUBSTANTIAL. Beyond the stipulated source 106 proof, every mathematical step is either a substitution of one hardcoded constant or a folklore argument already recorded in the primary literature. No nonroutine compatibility step survives the comparison (Sections 3 and 4).
- The named consequence is significant. Under the pin, the frozen nominee yields the full BG conjecture (KOWZ Conjecture 1.2). As recently as 18 Oct 2026, Banakh-Barsukov-Nakajima described BG as known only under the Rich 2-to-1 Conjecture. The significance belongs to a corollary of the source 106 method, not to new mathematics in the nominee. The review brief anticipates exactly this case: "A major named consequence can follow technically from a stronger stipulated method."

Confidence: high for the proof-level technical comparison, because I read the full operative source proof. Section 5 gives the strongest argument against the verdict and my answer to it.

## 2. Inputs and authentication

- I authenticated the author packet against the detached anchors in `review-context-r1.txt` before using any of it: FINAL.json, packet/MANIFEST.json, REPORT.md, frozen-statement.md and proof.md all match. The manifest is closed: its 47 files and directory tree match exactly, and its public-report hash matches FINAL.
- The frozen statement agrees with the scope quoted in the parent context. I assessed that full scope:
  - Theorem A: for every fixed integer k >= 1 and real delta > 0, a deterministic polynomial-time reduction maps 3-CNF formulas to nonempty simple graphs. Satisfiable formulas give graphs with G -> C_{2k+1}; unsatisfiable formulas give alpha(G) < delta |V(G)|.
  - Corollary B: PCSP(H, G) is NP-hard for all finite loopless H, G with H non-bipartite and H -> G. The search version is NP-hard under Turing reductions. The density form holds for every non-bipartite H and every delta > 0.
- I fetched my own pinned copies of source 106 (all build/source TeX and README), source 105 (all build TeX and README) and three files of companion 102. Each file was authenticated by Git blob SHA-1 against the complete 13223-entry `sources/preprints-tree.json` (SHA256 eeecc1da…5e09b). The 13 files that overlap with the author's private source copies are byte-identical.
- I downloaded my own primary copies of Banakh-Barsukov-Nakajima arXiv 2605.09815v2 (TeX source; v2 is the latest version, 18 Oct 2026), FMW ECCC TR26-179 revision 2, the FMW arXiv abstract page, the Brakensiek-Guruswami arXiv 1704.01937v2 TeX source and two web pages. For KOWZ and the original FMW ECCC text I read the author's copies, which the packet manifest authenticates. Exact extents are in `reading-limits.md`.

## 3. The strongest integrated existing reduction: what source 106 already provides

Source S = `preprints/Hardness-of-finding-large-independent-sets-in-three-colorable-graphs-September-24-2026/build/source/`. I read introduction, preliminaries, construction, lists, alignment, coefficient and parameters in full.

**Threshold occurrences.** The threshold appears only at these places:

- construction.tex 79 (clique test `dist(x,Tx) <= 1/8`) and 126 (edge rule `dist(x,Ty) <= 1/8`);
- construction.tex 149-150 (exact comparison with 1/8 in the encoding);
- construction.tex 192-198 (completeness: adjacent phases are at least 3/8 > 1/3 apart, so three arcs colour);
- lists.tex 18 (separation `dist(A,TA) > 1/8`), 28-29 (bump slope 32) and 36 ("64-Lipschitz").

**The soundness interface.** S states it explicitly at lists.tex 33-40: f takes values in [-1,1], f(Tx) = -f(x), f = 1 on A, f is constant across zero links, and f is L-Lipschitz within copies. Every later step consumes only this interface and the symbol L:

- `thm:junta` and `lem:influences` (preliminaries.tex 60-99) are stated "for every 0 <= L < infinity".
- McShane extension, `eq:compatibility`, `lem:subchain-lists` and `prop:aligned-bound` use L symbolically (lists.tex 42-135; coefficient.tex 11-286).
- `lem:separated-lists`, `lem:alignment` and `lem:good-pairs` do not involve L or the threshold.
- The parameter order (parameters.tex 10-37) chooses beta, K, m, lambda, s, gamma, P, d, r, mu and sigma after L.
- "Set L=64" is a bare instantiation, at lists.tex 11, parameters.tex 11 and coefficient.tex 13.

**What S's operative proof already proves.** Read at proof level, S's proof proves the following for any fixed threshold rho in (0, 1/4], after the mechanical substitutions 1/8 -> rho, 32 -> 1/rho and L = 2/rho. Satisfiable instances admit a circle map under which adjacent vertices are at circle distance at least 1/2 - rho. Unsatisfiable instances have alpha < delta n. The source's own figure caption (construction.tex 236-245) describes the geometry in exactly these terms: neighbours lie "within 1/8 of the antipodal phase".

**What the primary literature already records.**

- Folklore circular colouring (KOWZ 2003.11351v3, text lines 307-333): K_{(2n+1)/n} is isomorphic to C_{2n+1}, and chi_c(G) <= 2 + 1/n iff G -> C_{2n+1}. A circle map with adjacent phases at least k/(2k+1) apart is a (2+1/k)-circular colouring. So completeness with rho = 1/(4k+2) gives G -> C_{2k+1} by this folklore discretisation. The nominee's arc Claim and the map j -> -2j are one explicit instance of it.
- The sandwich reduction from PCSP(C_k, K_c) to PCSP(H, G) is stated in KOWZ (text lines 286-296; also BBN Prelims.tex 123-128, citing BG21 and BBKO). The fibre count turning alpha < n/c into "not c-colourable" is in S's own `cor:coloring` proof (introduction.tex 53-58). Search-to-decision via checking the output homomorphism is standard.

## 4. What the nominee adds

| Nominee step | Status relative to S and the primary literature |
|---|---|
| Threshold 1/8 -> rho = 1/(4k+2) in the clique test and edge rule | Substitution of one hardcoded constant |
| Exact comparison D(4k+2)·dist versus D | Same argument as construction.tex 146-150 |
| Separation `dist(A,TA) > rho` | Same argument as lists.tex 17-24 |
| Bump (1 - u/rho)_+, L = 2/rho | Same argument as lists.tex 26-40. The radius equals rho instead of rho/4; this is harmless because the separation is strict |
| Re-run of the parameter order with L_k = 8k+4 | Already parametric in L |
| Completeness by 2k+1 arcs | Folklore K_{(2k+1)/k} = C_{2k+1} discretisation (KOWZ 307-333), applied to S's own phase map |
| Corollary B and the density form | Standard sandwich (KOWZ 286-296) and fibre count (S, introduction.tex 53-58) |

**Search for a nonroutine compatibility issue.** I looked for any place where a smaller threshold could interact with the rest of the proof:

- Clique branch: the test only fires less often. Completeness still excludes it, since the phase map gives dist(x, Tx) >= 1/2 > rho.
- Graph density: soundness bounds every independent set and never uses edge abundance.
- Range of delta: S's restriction delta < 1/3 is only for meaningfulness.
- Polynomial degree: it depends on (k, delta) through constants alone, which the frozen statement allows.
- Multiplicity expansion and the trivial branches: independent of the threshold.

I found no nonroutine compatibility issue. The author's own proof.md (Sections 3, 7 and 8) and working notes (Observation O1) describe the operation the same way: a constant change inside the source proof plus a different completeness colouring.

**Genuinely new.** The observation that S's hardcoded threshold is a free knob. Because S's soundness is threshold-uniform, shrinking it pushes completeness down to circular chromatic number 2 + 1/k, and through KOWZ's equivalence this reaches BG. The checklist confirming that nothing else depends on 1/8 is careful, but each entry is a one-line instantiation. No new lemma, estimate, construction or parameter dependency is introduced.

**Black-box comparison.** This confirms the author's comparison, but it is not the basis of my verdict. S's `thm:main` used as a black box covers only H that contain a triangle. KOWZ's delta iteration provably cannot reach C_5 (text lines 1581-1584). The Lambda_k/Gamma_k adjoints yield looped targets. So the black-box gap is real, and it is closed only by opening S's proof, and there only by the routine substitution above.

## 5. Strongest argument against TECHNICAL, and my answer

**Argument.** BG is a well-known conjecture: BG 1704.01937v2, pcsp.tex 292-297, and KOWZ Conjecture 1.2. On 18 Oct 2026, after pinned 105 and 102 and FMW, BBN 2605.09815v2 (Introduction.tex 474-480, 246) still described BG as following only from the Rich 2-to-1 Conjecture, and approximate graph homomorphism as unclassified. S's authors, who explicitly compared their result with the BKLM Rich 2-to-1 route (introduction.tex 101-112), stated only three-colourability. An unrecorded resolution of a named conjecture looks substantial.

**Answer.**

1. The project's acceptance standard (NEW-TEN-2026-10-14.md line 17) excludes routine transfers. The nominee's mathematics beyond S is a routine instantiation of a proof that is stipulated true and already parametric in L, plus folklore. The large consequence was already present in S's operative proof. The nominee identifies it but does not supply new mathematics to obtain it.
2. BBN v2 does not cite S. Its bibliography has the 105 and 102 OpenAI entries and FMW, but no OpenAI independent-sets entry. Its statement therefore says nothing about whether S's proof was examined and the step missed.
3. Proof length and slogans are not the criterion. The criterion is whether any nonroutine step survives the proof-level comparison, and none does (Section 4).

**When this verdict could change.** The verdict would move toward SUBSTANTIAL only under one of two conditions:

- a correctness review finds that some step does depend nontrivially on the threshold and needs a new argument (I found none);
- the parent's standard deliberately credits the identification of a high-value corollary of a stipulated method as substantial.

I flag this as a high-significance TECHNICAL corollary. Correctly described, it is "the proof of [S] with threshold 1/(4k+2) yields the Brakensiek-Guruswami conjecture".

## 6. Rediscovery and comparison tests

**Rich 2-to-1, pinned 105 and BBN 2605.09815v2** (tested exactly, not assumed):

- **BBN's Rich definition** (Prelims.tex 143-163): a bi-regular instance in which, at every fixed left vertex u, the map pi_{uv} for a uniformly random neighbour v is uniform over all 2-to-1 maps [2n] -> [n]. The conjecture requires perfect completeness. BBN derive BG from their Theorem `th:blackbox` with r = 2, assuming this conjecture (Introduction.tex 466-480).
- **Pinned 105** (`thm:main`, 00-introduction.tex 32-45) gives ordinary exact 2-to-1 maps with perfect completeness, and it explicitly states that the Rich condition is not part of the theorem (lines 75-80). S says the same (introduction.tex 109-112). In the operative construction:
  - each legal edge map `pi_{f,D,a}(P) = out_g^{-1}(Q_{D,a} out_f(P))` places two legal labels in one fibre only when their restored outputs differ by the single kernel vector of Q_{D,a} (02-construction.tex 279-305);
  - fibre completion fixes all legal images and redistributes only illegal labels (07-parameters-output.tex 164-210).

  Richness requires every pair of left labels to share a fibre with probability 1/(2q-1) at every left vertex. Two legal labels whose output difference is not such a kernel vector for any incident edge never share a fibre. I did not certify that every output instance contains such a vertex. No pinned source asserts richness, and 105's structure is not shaped to provide it.
- **Pinned 102** (`thm:ugc`, 00-introduction.tex 22-39) has completeness 1 - epsilon, not perfect completeness. BKM's equivalence with UGC holds only on almost-satisfiable instances (BBN Introduction.tex 379-381), so 102 does not supply the perfect-completeness Rich premise either.

  Conclusion: the BBN conditional route is not paid by the pin. It neither makes the nominee REDISCOVERED nor makes it a transfer from BBN. The nominee's route runs through S's proof, not through richness.

**FMW** (4-to-1 with perfect completeness):

- Its applications, Corollaries 1.7-1.12 (ECCC original, text lines 240-299), are 3-colourable versus not c-colourable and 8-colourable versus small independent sets. The d-to-1 route of [GS20] gives 2d-colourable completeness, which cannot reach odd cycles.
- Remark 1.13 cites a supplement with further applications found by ChatGPT 5.6. I could not locate it: the arXiv 2610.12378v1 abstract page has no ancillary files, and the ECCC page links only the PDF revisions. ECCC revision 2 (8 Oct 2026, 119 pages) no longer contains Remark 1.13 or the supplement reference, and has no BG, odd-cycle or homomorphism mention. **The supplement remains unread.** I make no absence claim about it.

**Other sources:**

- S (all read TeX): no odd-cycle or BG statement.
- 105 introduction: none.
- 102 introduction (read extent): none.
- BG 1704.01937v2: states the conjecture (pcsp.tex 292-297) and lists partial progress only (545-551).
- KOWZ: open (Conjecture 1.2, Theorems 1.3 and 1.4).
- Two web searches, Fortnow's 11 Oct 2026 blog post and his OpenAI-TCS catalogue page: no BG resolution found.

These are bounded searches, not an absence certificate.

## 7. Apparent proof blockers (flags only; this is not a correctness review)

None found in my reading. Points I checked:

- f = 1 on A uses strict separation, and bump(rho) = 0.
- Within-copy Lipschitz uses dist <= d_infinity (S, lists.tex 39-40).
- The arc Claim: the window [(i+k)/N, (i+k+2)/N) has length 2/N < 1. The two arc indices differ by k or k+1 = -k, and -2k ≡ 1 mod N.
- Disjointness of the two promises needs delta < k/(2k+1); proof.md Section 1 reduces to delta_0 <= 1/4.
- Corollary B: c = |V(G)| >= 3, and a loopless G makes the fibres independent.

The separate correctness review must decide correctness.

## 8. Exact scope of this verdict

- **Applies to:** the full unchanged frozen Theorem A (all k >= 1 and delta > 0) and the full Corollary B (decision, search and density forms, for all finite loopless non-bipartite H and loopless G with H -> G), assuming correctness and the pin stipulation.
- **Does not cover:** correctness, acceptance, count, worldwide priority, or the content of the unlocated FMW supplement.
