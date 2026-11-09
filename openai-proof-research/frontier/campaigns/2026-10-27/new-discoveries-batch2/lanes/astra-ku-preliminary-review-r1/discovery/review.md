# Independent preliminary review: Ku torus family

Reviewed 2026-10-28 UTC. Assigned frozen revision: `74092007f2`. All 34 files matched `preliminary-review-hashes.json` before copying and after replay. No git command was used; the commit association itself is supplied by the task, while the bytes are independently hash-verified. All writes are in this review lane. Root alone accepts/counts.

## Recommendation

**Do not accept the frozen dossier as a new general obstruction theorem. Conjecture 5.3 is an immediate instance of explicit 1981 theorems.** This is a decisive exclusion, not a speculative Pólya-method objection. The advertised stronger lower bound `2k+2` also follows routinely from that old integral-matrix obstruction and first moments, as shown below.

**The fourteen-point counterexample to the intended `k >= 6` Conjecture 5.4 remains a plausible, narrowly scoped survivor.** I found no earlier matching construction/refutation in the bounded search. Its source, mathematics and Lean are correct. I do not reject it merely by citing the trivial `k=3` counterexample: that would ignore the explicitly intended domain. The current combined claim must therefore be narrowed before acceptance is considered. No credit is assigned here.

| Gate | Conjecture 5.3 / general obstruction | Intended Conjecture 5.4 refutation |
|---|---|---|
| SOURCE | PASS | PASS |
| MATH | PASS | PASS |
| FORMAL | PASS, literal finite-torus endpoint | PASS, closed intended-domain negation |
| NOVELTY | **FAIL: Johnson 1981** | **Bounded screen clear; priority not established** |
| SUBSTANTIVE | **FAIL: immediate old-theorem instance** | **Plausible PASS as a source-conjecture counterexample**, subject to the specific endpoint objection below |

No manuscript gate was applied. Nothing here resolves Conjecture 5.2 or the separate hypercube record 375265. The family can receive at most one credit, and none for the known obstruction, its formalization, or individual witness parameters.

## Exact primary source and scope

Kuo-Han Ku, *Monochromatic k in a row*, [arXiv:2606.12880v1](https://arxiv.org/pdf/2606.12880v1), printed pp.3,20,21. I independently viewed all three frozen page images. A fresh PDF retrieval returned the identical SHA-256 `a6f88bda9eb3630c5c582288105dc804d168aae41933984e6265a40958963cf8`.

Definition 2.2 uses lines `p + {0,...,k-1}v`, with `v` in `{-1,0,1}^2` excluding zero, on `(Z/kZ)^2`. For positive multiples of three these are precisely the four families `x=a`, `y=a`, `x+y=a`, `x-y=a`, with sign/reversal duplications harmless. Each has k points. Conjecture 5.3 denies a subset having exactly two points in every line. Conjecture 5.4 denies a subset of size at most `2k+2` having at least two points in every line. The immediately preceding discussion on p.21 explicitly excludes k=3; hence the candidate's additionally restricted formulation `k>=6` is justified.

The preceding density discussion explains 5.3 as equivalent to 5.1 via the source's own theorem. That equivalence is **not** present in these Lean files. The correct formal claim is the literal finite torus statement only. I have not audited or formalized an infinite-grid endpoint.

## Decisive prior theorem and exact bridge

Allan Wm. Johnson Jr., *Pandiagonal Magic Square Equations*, **Crux Mathematicorum 7(9) (November 1981), 258–267**, [official journal scan](https://cms.math.ca/wp-content/uploads/crux-pdfs/Crux_v7n09_Nov.pdf):

* Theorem 2, p.260: an integer-entry pandiagonal square of order a positive multiple of six has magic sum divisible by six.
* Theorem 4, p.266: at odd orders divisible by three, that sum is divisible by three.

The definition on p.258 permits arbitrary numbers, and the theorems assume integer entries, not distinct entries or the consecutive integers. Broken diagonals in both directions are included. I read the actual journal text, including the even-order diamond construction and its integrality argument; the odd-order theorem is stated with its verification left to the reader. Local PDF downloading failed (403); the official scan's text was available through web.run. These access differences are explicitly preserved, not described as a successful local PDF download.

Here is the complete application, independently checked. Suppose `A` is a forbidden exact-two set on the k-torus. Its indicator matrix has integer entries and every row, column and wraparound diagonal sum is 2. It is a pandiagonal square. If k is even, Theorem 2 gives `6 | 2`, absurd. If k is odd, Theorem 4 gives `3 | 2`, absurd. Alternatively avoid relying on the odd theorem: form the order-2k matrix `B(i,j)=1_A(i mod k,j mod k)`. Every row and every wraparound diagonal traverses its k-period twice, so all line sums are 4. Its order is divisible by six, and Theorem 2 gives `6 | 4`, again absurd. This covers **all positive multiples of three, including all powers of three**, with no new existence argument.

Halleck's 2000 thesis Corollary 7.2.3(2) is therefore not the limiting prior result. I read its pp.92–94 and freshly retrieved its PDF, matching the frozen hash. It independently covers order `3q` with `3` not dividing `q`. Its reduction formula does not on its own remove that restriction; Johnson does.

The familiar mechanism is also visible in Koshkin–Lee, [arXiv:2606.22221v1](https://arxiv.org/pdf/2606.22221v1), Theorem 2 and proof, pp.5–6: they give the standard first/second-moment proof for one-per-line permutations and credit the congruence proof to Kløve. I read those primary pages. This supports the routine-method concern, but **Johnson's exact integer-matrix theorem**, not an unjustified decomposition into panmagic permutations, is the decisive subsumer.

## Complete mathematical audit

For the candidate's own independent proof put `S2=sum(i^2,0<=i<k)`. Under the exact-two hypothesis each coordinate and each sum/difference label occurs twice. Over `Z/kZ`, the identity `(x+y)^2+(x-y)^2=2x^2+2y^2`, summed over A, gives `4 S2=8 S2`, hence `k | 4 S2`. Since `6 S2=k(k-1)(2k-1)`, writing `4 S2=kq` and cancelling the positive k gives `3q=2(k-1)(2k-1)`. Modulo three, its right side is 2 when three divides k, contradiction. No division by three inside `Z/kZ` is used. The Lean integer cancellation faithfully implements this step.

The stronger lower bound also has a short **old-theorem bridge**. If a two-fold cover has size below 2k, row counting is impossible. At size 2k all four families have constant sum 2, already excluded. At size `2k+1` each family has one line of size 3 and every other line of size 2. Let the four exceptional labels be r,c,s,d for x,y,x+y,x-y. Since `2 sum(i)=k(k-1)=0 mod k`, first moments give `s=r+c` and `d=r-c`. Subtract the single-entry matrix at `(r,c)` from the indicator of A. Regardless of whether `(r,c)` was in A, the resulting matrix is integral (a -1 entry is allowed), and its sums in all four families are exactly 2. Johnson excludes it. Consequently `|A|>=2k+2`. This is valid mathematics but is not a new general theorem to salvage the dossier; it is also not formalized by the frozen files.

For the counterexample the points, with coordinates modulo six, are

`(0,0),(0,2),(0,3),(1,0),(1,3),(1,4),(2,0),(2,1),(3,1),(3,4),(4,2),(4,5),(5,0),(5,5)`.

They are distinct. In label order 0,...,5 the line counts are:

* x: `3,3,2,2,2,2`;
* y: `4,2,2,2,2,2`;
* x+y: `2,2,2,3,3,2`;
* x-y: `2,2,3,2,2,3`.

This independently verifies all 24 distinct lines, every count being at least two, with cardinality `14=2*6+2`. Thus it refutes the precise intended universal statement, not only its k=3 wording. It also attains the lower bound at six, but that optimality is not a further credit or a frozen Lean endpoint. No all-order attainment is proved.

## Formal replay and actual types

`independent_replay.py` copied only the three source modules into a fresh temporary directory **inside this lane**, built them in dependency order using the task's absolute Lean 4.34.1 binary and pinned package library paths, enabled warnings-as-errors, then freshly elaborated `#check` and `#print axioms` commands. The mathlib revision was read from its local git metadata without running git. All module logs are empty, all return codes are zero, and all 25 named declarations passed. I read every reported type and axiom set and all three source files, including the two decidability instances. No proof holes, custom axioms, native evaluation, or unsafe declarations occur in candidate source.

The endpoint types are `source_conjecture53 (k : Nat) [NeZero k] (hk3 : 3 | k) (A : Finset (ZMod k × ZMod k)) : Not (ExactTwo A)`, and the closed negations of `SourceConjecture54` and `IntendedConjecture54`. The latter includes `6<=k`, `3|k`, cardinality `<=2*k+2`, and **all** allowed p,v lines. Definitions were read rather than inferred from theorem names. The direction/fiber bridge is proved in `SourceUniform.lean`; `decide +kernel` proves both witness facts. The only reported axioms are subsets of `propext, Classical.choice, Quot.sound`.

See `replay/audit.json`, `replay/Checks.log`, and `manifest-check.json`. The independently generated checks log happens to match the root log hash; it was rebuilt, not copied as evidence. The 25 count refers to the explicitly named definitions/theorems/abbreviation, not a count of every compiler-generated constant. The two source instances implement decidability and are included transitively in checked endpoints.

## Bounded novelty screen and strongest remaining objection

The live arXiv author search returned this paper and an unrelated Petrie/Pieri paper; the current target listing has only v1. The author's 2025 thesis, pp.60–61 and the earlier k=6 computation discussion, retains the exact-two question and establishes only strictness below `1-2/k` at six; those statements do not give a fourteen-point cover. I did not find that cover there. This is inspection of the relevant body, not a claim to know the author's unpublished searches.

Fresh MathDB API requests for 375263 and 375264 both returned 200 and were read in full. They concern 5.1 and 5.2, respectively; they have empty solutions/replies and are marked open. That does **not** certify novelty and does not turn 5.4 into 375264. The candidate correctly keeps 375265 separate.

The live Ideosphere explore response exposed 333 records with searchable text; exact source IDs, author/title phrases and related terms found no matching Ku result. A plausible hit, *Skirting sets and the inverse football pool problem*, was retrieved and its actual Definitions 2.1 and surrounding discussion read: it covers tuples by coordinatewise-unequal tuples, not all four line families, so it is not a subsumer. Costalonga's actual definitions and Theorems 1.1–1.5 were compared: covering board cells by semiqueens differs from intersecting every line twice. General-web queries included the source ID/title, author, pandiagonal divisibility, toroidal line coverings and double blocking; many yielded irrelevant results. Search details and candid access failures are preserved. A PaperVerse source-specific URL returned only a generic landing page, so its alleged review was not read.

**Strongest objection to the survivor:** once the old obstruction is removed, the only potentially new fact is a very small boundary-attainment construction at `|A|=2k+2`. It does not supply a counterexample below that threshold, does not decide 5.2, and does not establish a new infinite family. The campaign excludes mere endpoint corrections. My judgment is that the intended 5.4 witness is more than the k=3 domain correction: the p.21 calculation actually requires the strict cardinality bound, and the witness defeats that intended sufficient strategy. Still, root should not sell this as a new all-order obstruction or import substantive weight from the known moment theorem.

**Exact next step if retained:** re-scope the proposed single outcome to the intended Conjecture 5.4 counterexample, cite Johnson for all lower-bound/obstruction material, and explicitly decide whether that boundary-attainment refutation meets the campaign's substantive threshold. No additional mathematics or Lean bridge is missing for that narrow refutation. If root requires a result beyond a small endpoint-attainment example, this frozen candidate does not provide one; an all-order attainment theorem or another substantive strengthening would be new work and would require its own proof and prior-art review. Completing the `2k+1` Lean exclusion would not remedy the novelty failure.

The remaining bibliographic limitation is real: unindexed combinatorial constructions, non-English sources, and unpublished computations are not ruled out. No theorem here claims absolute priority. Preserve the correct certificate even if root chooses zero credit for the entire family.
