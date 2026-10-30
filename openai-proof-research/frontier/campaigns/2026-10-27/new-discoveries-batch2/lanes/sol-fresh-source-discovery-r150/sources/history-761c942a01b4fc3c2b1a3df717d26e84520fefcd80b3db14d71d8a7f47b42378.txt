# T008M independent contribution and eligibility review, round 1

Reviewer role: independent contribution/eligibility gate only. No proof verdict. The proof is assumed correct solely for classification. Source theorems at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true. No count, acceptance, staging, commit, upload or shared edit. Original prose CC BY 4.0; original code MIT.

## Verdict

**TECHNICAL** for the full unchanged frozen T008M scope. Not countable.

No exact published duplicate was found, so the verdict is not DUPLICATE. The packet is eligible in form and its identity is verified, so it is neither INELIGIBLE nor BLOCKED. The open literature leads could only move the verdict toward DUPLICATE; none of them could make it SUBSTANTIAL.

Short reason: every operation in the candidate is either source-paid, classical, or a direct transfer of a standard device. The top-weight detection lemma, which is the only nonbookkeeping step, is the prefix/suffix coefficient matrix of noncommutative algebraic branching programs (Nisan 1991, §3, definition of M_k(f) and Theorem 1). It is realized as a module by joining the deletion action that the source already uses (section 04) to the standard creation action at an empty state. The weighted "gap markers", the three caps with e_3 padding, the level separation and the ρ^{T/2} state count are bookkeeping. The square-root rate is the order of the trivial lower bound dim g ≤ μ(g)^2, and Cagliero–Rojas 2020 §1.1 already predicts square-root behaviour for free nilpotent Lie algebras.

## 1. Identity

* Brief anchors matched: manifest.json 2a476225…7a19, verify.py f69ed255…164e, candidate-008.md 0bf87bca…2fba5f, scope-008.md 8ad29468…9039. The brief capitalizes the two Markdown names; the frozen files are lowercase and carry exactly the briefed hashes.
* The author verifier was read in full before execution. With both external anchors, `--private` and `--source-tree` set to the real path of `sources/preprints-tree.json` (SHA256 eeecc1da…5e09b, `truncated: false`), it returned PASS_INVENTORY_NOT_PROOF (25 public files, 1 public directory, 43 private files, 13 private directories, canonical tree checked). A zero manifest anchor failed with exit 1.
* Reviewer-side check written separately from the author verifier: all 14 non-PDF blobs of `preprints/The-Deligne-Drinfeld-conjecture-September-23-2026/` in the complete tree match Git blob SHA1 values recomputed from the author's private copies; the one PDF blob was not downloaded.
* Copied mutation controls on disposable `/var/tmp` copies (author-integrity-controls.json): baseline passed; wrong manifest anchor, wrong verifier anchor, wrong source tree, edited payload, deleted payload, extra file, extra empty directory, symlinked payload (inside and outside target), hardlinked payload, FIFO, edited private source body, root symlink invocation and ancestor symlink invocation were all rejected.
* The original packet was not modified. Its git state is "staged by others"; this review did not stage anything.

## 2. Exact scope coverage

The frozen scope is assessed as a whole: every characteristic-zero field F; W_F the source008 noncanonically free graded Ihara Lie algebra on one generator in each odd weight at least 3; g_N = W_F/W_{>N}; ρ>1 with ρ^3=ρ+1; absolute c, C, N0 independent of F and N with c ρ^{N/2}/√N ≤ μ_F(g_N) ≤ μ_nil,F(g_N) ≤ C ρ^{N/2} for N ≥ N0; both Nth-root limits equal √ρ; explicit finite 0/1 generator matrices in any homogeneous free-generator system. The stated exclusions (no canonical Ihara coordinate conversion or efficient conversion, no fixed alphabet or class, no exact minimum, no improved polynomial factor) are respected by the candidate.

Classification covers all parts: lower bound, upper bound, nilrepresentation, field uniformity, 0/1 explicitness and both limits. No narrowed or substituted statement was evaluated in place of the frozen one. The reviewer's unweighted remark in §4 is context for the classification, not a substitute target.

## 3. Operation-level decomposition

| Step | Candidate location | Operation | Paid by |
|---|---|---|---|
| S1 | §1 | W_F is the free graded Lie algebra on e_3, e_5, …; generators noncanonical | Source 01-introduction.tex, Theorem thm:main (stipulated) |
| S2 | §1 | g_N embeds in A_N = F⟨e_3,e_5,…⟩/(weight > N), so a faithful A_N-module restricts to a faithful g_N-module | Source 02-algebra.tex, Lemma lem:lie-lattice (weighted Hall/PBW embedding); grading argument is standard |
| S3 | §5 | Lower bound: m^2 ≥ dim g_N ≥ l_N, weighted Witt/Möbius inversion, root analysis of t^3−t−1 | Trivial bound dim g ≤ μ(g)^2 (Burde–Moens 2010, Lemma 2.10; Moens 2009 dissertation §1.2.1); classical weighted Witt identities (credited by author); project history rejected free-GT dimension formulas as routine (proposals/algebra_geometry.md line 131, commit cf875aeb, 2026-10-08) |
| S4 | §2, top-weight detection lemma | States P (prefix still to delete) and Q (suffix already created); the (P-state, Q-state) entry of Φ_T(w) is 1 exactly for the concatenated word | Nisan 1991 §3: M_k(f) has rows indexed by k-terms, columns by (d−k)-terms, and entry equal to the coefficient of their concatenation; Theorem 1's ABP levels factor M_k(f) = L_k R_k through prefix/suffix states. Deletion side: source 04-deletion.tex, prop:deletion-representation and lem:deletion-kernel already extract coefficients by deletions on words; Burde–Eick–de Graaf "Dual". Creation side: truncated regular/PBW quotient module (Birkhoff, as recalled in Moens 2017 §1; Burde–Moens Prop. 3.3; BEG "Regular"). Single-word path matrices: Mazorchuk–Steinberg Theorem 24 proof |
| S5 | §2 | Integer gap markers r, s let the cut fall inside a letter; the crossing letter is fixed by r+s | Unit subdivision of a weight-d letter into d steps; uniqueness uses the source fact of one generator per odd weight. Bookkeeping |
| S6 | §3 | Three caps T=N−2,N−1,N, right padding by e_3^j, separation of homogeneous degrees by level difference | Bookkeeping. Not essential: one module with all prefix lengths and all suffix lengths, joined at a shared empty state, detects every weight ≤ N directly (see §4) |
| S7 | §4 | a_j ≤ ρ^j from a_j = a_{j−2}+a_{j−3}; |P_m|, |Q_b| sums give D_T ≤ K ρ^{T/2} | Routine linear-recurrence count |

Rate: the exponent ρ^{N/2} is the square root of dim g_N up to the √N factor, i.e. exactly the order of the trivial lower bound. Cagliero–Rojas 2020 §1.1 conjectures μ(L_{r,k}) ~ 2√(r^k/k) via a block factorization (a_0,…,a_k) and reports experiments; the author already credits the square-root objective and block factorization as antecedents.

## 4. Why TECHNICAL and not SUBSTANTIAL

The author's proposed residual (source-and-credit.md, "Exact residual credit") is the integrated marked half-weight construction: two half-weight word segments with gap markers, simultaneous coefficient extraction, caps and padding, level separation and the half-growth count.

1. **Simultaneous coefficient extraction is Nisan's matrix.** For homogeneous f of weight T, the block of Φ_T(f) from level −m to level b is the weighted form of Nisan's M_m(f): in the candidate's row-to-column reading order, rows are P-states (prefix a with gap r), columns are Q-states (suffix v with gap s), and the entry is the coefficient of a e_{r+s} v. Faithfulness on A[T] is the statement that M_m(f) ≠ 0 whenever f ≠ 0, which is immediate because each word occupies its own entry. Nisan uses exactly these prefix/suffix states as ABP levels. Using all prefixes and all suffixes at once (an identity-shaped coefficient matrix) instead of a rank-minimal basis is the universal case of the same factorization, not a new mechanism. The candidate's comparison with Mazorchuk–Steinberg ("its required property is stronger") is correct, but the stronger property is supplied by this standard prefix/suffix device.
2. **The module structure is two known actions joined.** Deletion of leading letters is the derivative/coregular action already used by the source in section 04 to extract coefficients; creation is the regular truncated module. Joining them at the empty state through a crossing transition is a one-line combination.
3. **Gap markers, caps, padding and counting are bookkeeping.** Subdividing a weight-d letter into d unit steps is the standard way to cut a weighted word at a fixed weight. The caps and e_3 padding can be avoided entirely (see below), so they are presentation choices. The dimension estimate is a linear recurrence.
4. **The GT-specific content is entirely paid.** Everything about Grothendieck–Teichmüller or Ihara structure enters through S1–S2. After S2 the problem concerns a weighted free associative algebra with one letter per odd weight at least 3, and the GT label adds nothing to the residual operation. NEW-TEN excludes routine transfers.

**Considered counter-argument (recorded, not adopted).** The strongest SUBSTANTIAL-side evidence is bibliographic, not mechanistic:

* No source read states a square-root-order faithful module for free nilpotent Lie algebras, or truncated free associative algebras, of growing class. Cagliero–Rojas 2020 cites only Lo–Ostheimer's 1+r+…+r^k and the general (dim n)^k+1 bound, then poses the square-root behaviour as a conjecture for fixed k.
* Reviewer's own unweighted remark (proof, not computation): for r letters of weight 1, take deletion states for words p with 1 ≤ |p| ≤ m, one shared empty state, and creation states for words q with 1 ≤ |q| ≤ n. A letter x deletes a leading x from p (sending a one-letter p to the empty state) and appends x to q (zero beyond length n). The image of a word w has entry (q, p) equal to 1 exactly when w = q·p, so distinct words of length at most m+n have disjoint nonempty supports, and longer words act by zero. This gives a faithful nilpotent module of the truncated free associative algebra, hence of the free nilpotent Lie algebra of class m+n, in dimension (r^{m+1}−r)/(r−1) + 1 + (r^{n+1}−r)/(r−1). (Here letters act on column vectors, rightmost letter first, and q·p means q written to the left of p.) For r=2, m=n=4 that is 61 for N_{2,8} (dim 71), while Burde–Eick–de Graaf 2008 Table 2 reports Regular and Dual outputs of dimension 117. reviewer-sanity.py illustrates this one finite case and is not relied on. The same remark shows that the three caps are unnecessary.

This suggests that the elementary construction may be unrecorded in the faithful-representation (μ) literature read here, i.e. possibly new to that literature. It does not show a non-routine mechanism. The brief states that absence of a theorem or a new asymptotic number is insufficient, and the campaign criteria exclude routine transfers. Applying Nisan's prefix/suffix factorization to a faithful module is such a transfer.

**Why not DUPLICATE.** No read source states the T008M bounds, or a faithful module of a truncated weighted free associative algebra with square-root dimension. Nisan treats circuit size of a single polynomial, not modules. Lewin 1974 I, Theorems 9 and 11, embed into matrices over commutative polynomial extensions, not over the base field with compressed dimension. Mazorchuk–Steinberg §7.1 concerns semigroup effectiveness of N_{m,n}, not linear faithfulness. Burde–Eick–de Graaf, Burde–Moens, Moens 2017, Moens 2009, Gul–Weiß and Cagliero–Rojas 2014 give PBW-quotient, cohomological, polynomial-in-dimension, embedding-size or lower-bound results, not square-root constructions.

**Why not BLOCKED.** Identity is verified. The unread leads (Lo–Ostheimer, Lewin II, truncated path algebra minimal faithful modules, Hankel/rational series realization theory of Schützenberger and Fliess, Reutenauer's book) could only supply an earlier statement of the same construction, which would move the verdict to DUPLICATE. None could make the mechanism non-routine.

## 5. Objections

### Required

R1. **Count status.** T008M must be recorded as TECHNICAL for the full unchanged scope and must not be counted. No narrowed statement, unweighted generalization, constant improvement or single-cap variant may be counted on the strength of this review. Each would need its own frozen scope and its own gates. The reviewer judges that the same Nisan-transfer objection would apply to them.

R2. **Missing credit for the detection operation.** source-and-credit.md does not cite the prefix/suffix coefficient matrix of noncommutative ABPs (Nisan 1991, §3 and Theorem 1). Any retained technical note must credit it as the operation behind the top-weight detection lemma, not only the Mazorchuk–Steinberg single-word path test and the source's section 04 deletion.

R3. **Lower-bound attribution.** The lower bound must be attributed to the trivial bound dim g ≤ μ(g)^2 (e.g. Burde–Moens 2010 Lemma 2.10; Moens 2009 §1.2.1) together with classical weighted Witt counting. The author's "elementary dimension lower bound" wording should name this source. The step lies inside the project's earlier rejection of free-GT dimension formulas as routine.

R4. **Residual wording.** The phrase "simultaneously stores two half-weight word segments with fixed integer gap markers, detects all associative coefficients, and obtains the square-root exponential state count" (source-and-credit.md, section 04 paragraph) must not be presented as a new mechanism in any retained note. It describes Nisan's state factorization with unit-step subdivision.

### Optional

O1. If a technical note is retained, state the general unweighted construction and its comparison with Burde–Eick–de Graaf Table 2 and Cagliero–Rojas 2020 §1.1, with a first-hand check of Lo–Ostheimer, Lewin II and the Schützenberger/Fliess Hankel-realization literature before claiming it is new to the literature.

O2. The three caps and e_3 padding can be replaced by one module with all prefix and suffix lengths joined at a shared empty state. This shortens the construction and does not change the classification.

O3. Author verifier: without `--source-tree` the canonical tree is not checked, and without `--private` private bodies are not checked. Both facts are reported in its output, but REPRODUCE-style instructions should make the full invocation the documented default.

O4. The candidate says the crossing letter "is determined by r+s because there is only one generator in each allowed weight". This dependence on the source's one-generator-per-weight structure deserves a remark: alphabets with several letters per weight need the crossing letter recorded in the state. This is not a proof objection for the frozen scope.

## 6. Independence and incidental exposure

The proof review directory t008m-proof-r1 was not read. While checking the campaign task list for T008M history, a grep of tasks.json displayed one parent-disposition line for the proof review ("PASS_FULL_T008M adopted … O1 single-cap simplification … must inform favorable contribution adoption"). The parent files proof-adoption.json, proof-r1-parent-verification.json and single-cap-addendum.md were seen in a directory listing and were not opened. The reviewer had independently noted that the caps are unnecessary (O2) from the reviewer's own unweighted remark. The brief states that parent effort confers no favorable presumption, and this line did not alter the verdict.

Reading, search and proof limits are in reading-and-limits.md.
