# Independent review: coefficient positivity, Ova count, and positivity endpoint

Review date: 2026-10-25 (America/Los_Angeles). Reviewed the canonical files in `outcomes/`, not the sibling lanes' compiled artifacts. This review makes no edits to the candidates, acceptance counters, dependencies, or build directories. PDF building, rendering, and release validation remain the parent's responsibility.

## Verdict and counting

| Canonical outcome | Mathematical/source-fidelity verdict | Independent Lean verdict | Count eligibility |
| --- | --- | --- | --- |
| `coefficient-positivity`, MathDB 372794 | **PASS**: the exact coefficient conjecture, for every natural exponent and every coefficient | **PASS**, 24 named declarations | **1 source question**, as verification of an already proved and already formalized result |
| `ova-count`, MathDB 350342 | **PASS**: at least 38 distinct outputs from the actual construction, contradicting both 10 and 13 | **PASS**, 20 named declarations, plus the local decidability instance | **1 source question**, as verification of Patel's known counterexample; the two bounds are not two outcomes |
| `positivity-rigidity`, MathDB 325243 | **PASS**, strictly as a correction to the literal printed endpoint statement | **PASS**, 8 named declarations | **1 literal-source correction** under this campaign's existing correction-inclusive convention; **0 refutations of the intended corrected theorem** |

Thus these packets support three distinct literal source-question outcomes, of which two verify known mathematical resolutions and one corrects a free endpoint. They do not support three new-to-literature theorems. No mathematical or formal-proof blocker was found. The documentation/reproducibility issues below should be fixed during integration; the PASS verdicts do not certify existing PDF or release receipts.

## Material read and source identification

I read `AGENTS.md`, the immutable upstream record (`openai/math` commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`), and the manuscript-catalogue context. None of these proofs needs an upstream theorem as a new mathematical assumption.

For all three outcomes I read the complete canonical `main.tex`, `PROOF.md`, proof module, and available source/metadata files. For the first two I additionally read their sibling lane self-reviews and novelty notes. I read the complete Fill–Janson paper (52 printed pages, including Appendices A–E), the complete 2020 Ova paper (printed pp. 111–119), the complete 2021 Ova v1 paper, and checked v2 throughout against v1, including its changed wording and references. I read the complete endpoint source HTML, with MathML formulas read through their TeX `alttext` rather than counting duplicate accessibility representations as separate text. This includes the surrounding application, all proof sections, and the algebraic appendix. I also inspected the archived Machina Mathematica dossier page and both full MathDB solution records.

The first two original-source archives are in `../next-discovery-lane/sources/`, relative to this campaign directory. The endpoint archive is `../positivity-rigidity-lane/sources/source.html`.

| Source | SHA256 independently calculated from archive |
| --- | --- |
| `2601.19323.pdf` | `54d8f3d7c5feb492e8264c58cf98de05f03204f2b4696055cd19d3d17798bc6a` |
| `2601.19323.html` | `89e85dc517ff0e94b86f44175501bc19769129e495c8b9e9bc7c74d3b8895fa4` |
| `ova-original-2020.pdf` | `1a57ad23b14487d34ddaea3781ddd1ee04cfeed466b114aa2ef4a519972a1b7e` |
| `2104.04522.pdf` (v1) | `8670303008ad064a8f8d0ef5dd4451516cc9c2a781df87021173f47d28fe71ff` |
| `2104.04522v2.pdf` | `07bef72350ab6d46a10212e8ccbdaf7708315183ec9bb024afc7a0bc2b2f6aea` |
| `372794.json` | `30274d0d54ff755efc1aa8f4b69c53c0d98aa949c821510626b289b49471e7c4` |
| `350342.json` | `fda83ff915ffb545ef411f0c60d2e8f1c8b2fdfebee1e3bdfcb899b3bca405ad` |
| `fill-janson-prior-formalization.html` | `f318897480f086d2afaee1842802187a496dd8540f285c284d48f33bf9549182` |
| Endpoint `source.html`, arXiv:1303.6651v1 | `214e6307b06865957f9cb8d5f57b2d0dc23b8c93d64b7f0b4a8230ce0578e2ed` |

## 1. Coefficient positivity — PASS

### Exact source and quantifiers

Fill and Janson, *Positive autocorrelation at unit lag for stationary random walk Metropolis–Hastings in R^d*, arXiv:2601.19323v1, Appendix E, printed p. 38, Lemma E.8(a), equation (E.16), define

\[
\begin{aligned}
h(t,a;r)={}&[1+(3+a)t]^r\big([1+(2+a)t]^{r+1}-[1+at]^{r+1}\big)\\
&-[1+(1+a)t]^r\big([1+(4+a)t]^{r+1}-[1+(2+a)t]^{r+1}\big).
\end{aligned}
\]

Lemma E.8 assumes real `r >= 1` and real `a,t >= 0` and proves pointwise nonnegativity. Conjecture E.9 instead fixes arbitrary `r in N` and asks for nonnegative coefficients of the polynomial in both indeterminates. It imposes no additional numerical condition on these indeterminates. The candidate proves the latter assertion, including `r=0`. This extra case is valid even if the source's natural-number convention starts at 1.

The canonical `sourcePolynomial` matches every factor, sign, exponent, and coefficient of (E.16). The coordinate assignment is `X 0 = t`, `X 1 = a`, over `MvPolynomial (Fin 2) Z`. The final theorem universally quantifies over `r : Nat` and `d : Fin 2 →₀ Nat`. These exponent vectors are exactly all pairs of natural coefficient indices, including zero indices and coefficients outside the support. There is no bounded-exponent or bounded-degree substitute for the question.

### Proof and full certificate

I checked the algebra of the homogeneous expression with

\[
A=(x+3t)(x+2t),\quad B=(x+t)(x+4t),\quad C=(x+t)(x+2t),\quad D=x(x+3t),\quad K=8t^4(x+2t).
\]

With `H_n=(x+2t)A^n-(x+4t)B^n+(x+2t)C^n-xD^n`, `U_n=H_(n+1)-D H_n`, and `V_n=U_(n+1)-C U_n`, the initial conditions are `H_0=U_0=0`, `V_0=K`, and the claimed recurrence is exactly

\[
H_{n+1}=DH_n+U_n,\quad U_{n+1}=CU_n+V_n,\quad V_{n+1}=BV_n+KA^{n+1}.
\]

In particular, `(x+2t)(A-B)(A-C)(A-D)=KA`; there is no missing factor in the forcing term. The Lean ring proofs independently certify these identities for every natural index. Addition, multiplication, constants, variables, and natural powers preserve coefficientwise nonnegativity, so simultaneous induction proves nonnegativity of `H`, `U`, and `V`.

`homogeneous_nonnegative` allows arbitrary nonnegative-coefficient polynomials `x,t` in the bivariate ring. Substituting `x=1+a*t` therefore uses a proved closure argument, not an unproved composition principle. `source_bridge` is a proved polynomial identity for every `r`, and `all_coefficients_nonnegative` applies that identity and the induction. Both the bridge and the entire quantified conclusion are included in the independently compiled module. The proof does not assume the source conjecture or the source's analytic nonnegativity theorem.

### Attribution and limits

Shivam Patel's MathDB response, UUID `46acd5c9-9ae6-4584-a626-588caaf59c7b`, dated 2026-08-20, already supplies the positive generating-function proof. The triangular recurrence expresses that same mathematical structure. The archived Machina Mathematica / Korea Superintelligence Labs dossier, *Swap differences of powers*, version 1, snapshot 2026-09-07, explicitly reports the full conjecture and prior Lean formalization through a general swap identity. The candidate correctly credits both. It is not a first proof, first formalization, or demonstrated new-to-literature theorem. Neither the root conjectures nor the plot-dependent portions of the source's other arguments are claimed or imported here.

## 2. Ova prime-output count — PASS

### Actual source construction and the two bounds

The original source is Y. A. Acevedo Agudelo, *A complete classification of the Mersenne's primes and its implications for computing*, Revista Politécnica 16(32), 2020, pp. 111–119, DOI `10.33571/rpolitec.v16n32a10`. Definitions 1–3 give the residue and rotation frequency; Theorem 7, starting on printed p. 116, gives the Ova–Ova–Prime–Ova construction. Its notation `Gamma_p`, `G_p` corresponds to

\[
k_p=p\bmod360,\qquad f_p=\lfloor p/360\rfloor,\qquad p=k_p+360f_p.
\]

The two inputs are arbitrary primes `p,q`. Let `C` be the complete set of residues of primes modulo 360. For `r in C`, the source first requires `k_p+k_q+2-r` to be a prime. A resulting prime is `r+360(f_p+f_q)` when that integer is prime. A representative lies in `0<r<360`; positivity of the complementary prime forces `r <= k_p+k_q+2`, so the Lean natural subtraction agrees with ordinary integer subtraction.

The original **Conjecture 1 is on printed p. 118, not p. 117**, and gives the upper bound **13**. The 2021 paper, arXiv:2104.04522v1/v2, uses this construction in its Goldbach discussion and cites Theorem 7 of the earlier paper. Its own Theorem 7 is a different result about residue-set closure. The retrieved 2021 versions do not supply the claimed bound 10. **10 is the explicit MathDB 350342 bound.** The candidate properly distinguishes those two bounds in substance; the page citation needs correction.

The source's separate at-least-one-output theorem and its Goldbach argument are not assumed. The finite counterexample is verified directly, so their correctness is irrelevant to this result.

### All conditions, distinctness, and the 38 witnesses

The certified input data are

\[
677=317+360\cdot1,\qquad401=41+360\cdot1,
\]

with both inputs prime. Consequently the complementary and output primes are `360-r` and `720+r`. The canonical witness set is

```
7, 13, 23, 49, 53, 67, 77, 89, 91, 103, 109, 119, 133, 137,
161, 163, 167, 187, 209, 221, 233, 247, 251, 257, 263, 271,
277, 289, 293, 299, 301, 313, 319, 329, 331, 341, 343, 349
```

`witnesses_eligible` checks all 38 possibilities: strict residue bounds, the subtraction bound, and both primalities. `witnesses_count` proves cardinality 38 by kernel reduction. These are genuine residue classes of primes, not a claim that each displayed representative is itself prime: e.g. 49, 77, and 289 are legitimate representatives. `residue_class_bridge` witnesses the original prime-residue condition by the prime output itself and proves its remainder is exactly `r`. `SourceEligible`, `source_condition_iff`, and `source_outputs_eq` supply the full source-set bridge.

`decomposition` proves for arbitrary eligible data that the complementary prime plus the output is `p+q+2`. `distinct_output_count` proves that the image under addition of the fixed frequency term has exactly the residue-set cardinality. Thus the formal conclusion counts distinct output primes, not entries in a list. The final `prime_count_counterexample` proves existence of prime inputs with a source-output cardinality at least 38 and strictly greater than both 10 and 13.

There is one source-version nuance worth retaining: the 2021 exposition eventually restricts `C` to `C* \ {2,3,5}`, whereas the canonical general-purpose `PrimeResidue` definition follows the original complete-residue-set formulation. This does not invalidate the counterexample. Every listed witness is coprime to 360, so every witness also belongs to the later restricted set. I additionally compiled a reviewer-only theorem, appended in memory to the complete module, proving `∀ r ∈ witnesses, Nat.Coprime r 360` by the same 38-way exhaustive split and `norm_num`. No candidate file was changed. A general set equality for the 2021 restricted `C` is not claimed by this review; the full counterexample works under either convention.

As a separate arithmetic cross-check I used trial division through the integer square root: both inputs are prime, the 38 residues are distinct, all 76 complementary/output primalities hold, and all 38 outputs are distinct. An exhaustive scan in this independent arithmetic check gives exactly the same 38 residues. That last exact-total observation is **not** substituted for a Lean theorem: the candidate certifies only the sufficient lower bound, and does not silently claim a formal exact total.

### Attribution and counting

Patel's MathDB response, UUID `cb893380-2a3c-48d8-92d6-21c99c7f1ce8`, dated 2026-08-20, supplies the same input pair and the same 38 residues. The candidate gives appropriate credit. The contribution is independent local formal verification. Bounds 10 and 13 concern the same construction and witness, and together earn only one source-question outcome. No priority claim follows from the bounded novelty search.

## 3. Positivity-rigidity endpoint — PASS as a literal correction only

### Exact printed statement

Lóczi and Ketcheson, *Rational functions with maximal radius of absolute monotonicity*, arXiv:1303.6651v1, Section 2.5, **Conjecture 11**, explicitly fixes

\[
s\in\mathbb N^+,\quad q\in\mathbb R\setminus\{0\},\quad\widetilde q\in\mathbb R,\ \widetilde q>0,\quad
p_0,\ldots,p_{s+1}\in\mathbb R.
\]

It assumes, for every integer `k=0,...,s+1`,

\[
S_k=\sum_{m=0}^{\min(k,s)}\binom{s-1+k-m}{s-1}p_mq^m(-\widetilde q)^{k-m}\ge0.
\]

The full printed conclusion is `p_0 >= 0`,

\[
p_m=p_0\binom{s}{m}(\widetilde q/q)^m\quad(m=1,\ldots,s+1),
\]

and additionally `S_0=p_0` and `S_k=0` for every `k=1,...,s+1`. The original HTML—not only MathDB—includes the endpoint `s+1` in both the free coefficients and this conclusion, while the sum stops at `s`. The surrounding Remark 10's discussion of Mathematica checks and a manual `s=2` proof does not supply a missing constraint on that free endpoint.

### Entire family and full conclusion failure

Take any real `t != 0` and set `s=1`, `q=qt=1`, `p_0=p_1=1`, `p_2=t`. There is no hidden zero denominator, zero initial coefficient, sign violation, or omitted positivity inequality. All three required sums are

\[
S_0=1,\qquad S_1=-1+1=0,\qquad S_2=1-1=0.
\]

Nevertheless the asserted `m=2` conclusion is `t=1*choose(1,2)*1^2=0`, a contradiction. Failure of this conjunct is failure of the full printed conclusion; the other conjuncts need not fail.

The Lean `sourceSum` reproduces the finite binomial expression exactly. Its natural subtraction matches the source integers because `s>=1` and every summation index satisfies `m<=k` and `m<=s`. `Hypotheses` contains all sign/nonzero conditions and every required inequality. `Conclusion` contains every printed conclusion, including all zero-sum equalities. The use of a total sequence `Nat → Real` introduces no extra premise: only its entries through `s+1` appear, and any finite tuple can be extended to such a sequence.

`sum_ignores_endpoint` proves invariance under arbitrary replacement of `p_(s+1)`, for all `s,k,q,qt,p,t`. `candidate_hypotheses` verifies all required `k` for **every** real `t`; `candidate_not_conclusion` proves failure for **every** nonzero `t`. `printed_conjecture_false` specializes to `t=1` to refute the complete universal printed implication. Thus the certificate covers both the structural defect and an actual family satisfying every premise, rather than merely observing that a coefficient does not occur.

### Strict scope boundary

In the surrounding application, the `p_m` arise from derivatives of a polynomial of degree at most `s`, so `p_(s+1)=0` there. The source itself also notes that its conjecture allows independent `p_m`. The plausible repairs—truncate the conclusion at `s`, or explicitly require `p_(s+1)=0`—are not refuted by this example. The candidate properly labels this as a literal endpoint correction, not a substantive resolution of the intended rigidity problem or a refutation of the paper's Runge–Kutta results. It must keep that label wherever counted or released.

## Independent Lean compilation and declaration/axiom audit

Compiler used:

```
/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean
Lean 4.34.1, x86_64-unknown-linux-gnu
commit 5045d0056413266e57c625dcd7c365b10e377c52, Release
```

Each **complete canonical module** was sent directly on stdin, followed in the same input by `#check` and `#print axioms` for every local `abbrev`, `def`, `lemma`, and `theorem`. Invocation was `lean -DwarningAsError=true --stdin`, with working directory `/`. `LEAN_PATH` consisted exclusively of the following pinned packages' `.lake/build/lib/lean` directories under

```
/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
```

No candidate directory or local build directory was on the import path; there were no source-local `.olean` imports or output-file flags. The existing `Checks.lean` files were read, but their local-module imports were not used for this independent check. All three invocations exited **0**, with no warnings or stderr. No `sorry`, `admit`, custom axiom, unsafe declaration, or unchecked native computation appears in the candidate proofs.

I independently read each dependency HEAD and checked equality with campaign `pins.json`:

| Package | Revision |
| --- | --- |
| mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612` |
| plausible | `118aa17ee84656b8bd727fef7c458ee8c833385c` |
| LeanSearchClient | `ddf04cf3949fa556442341e87d47f9f6e6074707` |
| importGraph | `e928b72544873815af278d38681b31c0293588e3` |
| proofwidgets | `106ff4fafc74ef4ac99d81dbf3ab399118f497a5` |
| aesop | `355695d523e41d0554926416cba2a2b3544fbbc9` |
| Qq | `6a489d9af5d0c47e5b259e2e8bcdfc1811b5a259` |
| batteries | `f2effa3d803fda822b1f97b806c47cf2adfbcbc2` |
| Cli | `e92c9f15fdfacc8536f31cfb3b7ad26c3c8cd204` |

Let **S** denote the complete standard axiom set `{propext, Classical.choice, Quot.sound}`. The following covers every named declaration, not just the final theorem:

* **CoefficientPositivity: 24 = 1 abbreviation + 10 definitions + 12 lemmas + 1 theorem.** All 24 report exactly **S**: `Poly`, `NonnegCoeffs`, `nn_add`, `nn_mul`, `nn_C`, `nn_X`, `nn_nat`, `nn_pow`, `A`, `B`, `Cc`, `D`, `K`, `H`, `S1`, `S2`, `initial`, `s2_step`, `h_step`, `s1_step`, `homogeneous_nonnegative`, `sourcePolynomial`, `source_bridge`, `all_coefficients_nonnegative`.
* **OvaCount: 20 = 9 definitions + 10 lemmas + 1 theorem.** `residue`, `frequency`: no axioms. `Eligible`, `PrimeResidue`, `residue_class_bridge`, `SourceEligible`, `source_condition_iff`: `{propext}`. `decomposition`, `witnesses`, `witnesses_count`: `{propext, Quot.sound}`. `outputResidues`, `outputPrimes`, `output_prime`, `distinct_output_count`, `inputs_valid`, `witnesses_eligible`, `count_lower_bound`, `sourceOutputPrimes`, `source_outputs_eq`, `prime_count_counterexample`: exactly **S**. The additional local instance `instDecidableEligible` also independently compiles and reports exactly **S**. Therefore “20 declarations” describes the manifest's named declaration category, not all declarations including instances. The reviewer-only `reviewer_prime_residue_unit` check also reports exactly **S** and is not part of the candidate's count.
* **PositivityRigidity: 8 = 4 definitions + 4 theorems.** All eight report exactly **S**: `sourceSum`, `Hypotheses`, `Conclusion`, `coefficients`, `sum_ignores_endpoint`, `candidate_hypotheses`, `candidate_not_conclusion`, `printed_conjecture_false`.

These are standard logical foundations, not imported assumptions of the source conjectures. The axiom union for each complete module is exactly **S**.

## Hash binding of the canonical review

| Outcome | File | SHA256 |
| --- | --- | --- |
| coefficient-positivity | `formal/CoefficientPositivity.lean` | `5079059191e422b9a39bca188a1e6bd1b754ada16cb840def8a06c47ff6acc7d` |
| coefficient-positivity | `main.tex` | `927e4d502ee297303212a9dea7f54e8b915051f63aec198803c7b3d0a18db52d` |
| coefficient-positivity | `PROOF.md` | `d350fc0b6e3bdbdf097aeae90d3454ecc845b2755e7ec5d8709d3a710683f943` |
| ova-count | `formal/OvaCount.lean` | `c385428dda9740069729c7808d2b260fb4215d156d291bb94958077e1d9a3ebd` |
| ova-count | `main.tex` | `eacd1cef19e915debf01bff474a7f5e9539e1967fae798a097dd423b65fdcb2a` |
| ova-count | `PROOF.md` | `939e1a787dc1c461387c92dd2cebc7a8c54ec4e0c4154b1cf8490ae882966b4f` |
| positivity-rigidity | `formal/PositivityRigidity.lean` | `04a5b9d0804568811939c988703bfeac0d8566ef8a371c23b0f78d7340d34eea` |
| positivity-rigidity | `main.tex` | `4031733eed9508392288908e8bd70106d83486bdbd094073d5b561ffb23c5cc4` |
| positivity-rigidity | `PROOF.md` | `e35426a4c7f855bd4b8e3dc4c8281bdb58664de80543188a236de986e4e45dc7` |

## Documentation and reproduction issues for integration

1. **Ova printed page:** change “Conjecture 1, printed p. 117” to **p. 118** in `main.tex` and the copied README/novelty context. Theorem 7 begins on p. 116 and its proof spans pp. 116–118. The bound itself and the counterexample are correct.
2. **Stale paper receipts:** the coefficient `verification.json` records TeX SHA `8121677c68c1e3f83ea7e0ce16102335b6d59ea33fcd2179bcc8d064497a7114`; the Ova receipt records `6c492d780154237facd06ecc19a24e20b552fd2d20c5d0b1cc636a9281a60c69`. Neither matches the current canonical `main.tex` hash above. Their prior PDF/visual PASS records must not be used as validation of these canonical manuscripts. Rebuild/re-render and regenerate the receipts after final edits. The Lean proof hashes do match the current modules.
3. **Copied lane instructions:** the first two READMEs describe sibling-lane build artifacts and use an invocation whose relative outcome path does not identify `outcomes/<name>` when run from this canonical campaign directory. The correct checkout-level form is `python3 verify_outcome.py outcomes/<name>` from `twenty-proof-campaign/`; this review instead used the no-output stdin method. References in `primary-reference.json` to `../sources/...` are also sibling-lane-relative, not valid source locations relative to the canonical outcome directory. Retain or translate that provenance explicitly in the release.
4. **Declaration-count wording:** Ova's reported 20 named declarations excludes its local decidability instance. Say “20 named def/lemma/theorem declarations plus one instance” if describing every source declaration; the instance is checked and harmless.
5. **Endpoint metadata:** its `source.json` has a conflicting “solved” references field quoting an introduction sentence about other conjectures, while its status is “open.” Neither field establishes resolution of Conjecture 11. The actual original statement and certified family, not this metadata, support the literal correction. The endpoint packet has no candidate-local `coverage.json`/`verification.json` in the reviewed tree; this review supplies independent evidence, and the parent should generate any release-required receipts.
6. **Keep scope labels:** preserve Patel's credit for both prior results, the Machina Mathematica prior-formalization credit, the Ova lower-bound rather than certified-exact-count language, the 2020/2021 residue-set distinction, and the endpoint's literal-correction-only status. Existing candidate text largely does this correctly.

No candidate proof was weakened or repaired during this review. No result was accepted by trusting a stale `.olean`, a numerical search, the self-review, or an unchecked source theorem. Only this assigned review file was written.

## Parent integration addendum

The parent applied the requested minor documentation corrections: the Ova source page is118, and its audit now explicitly includes `instDecidableEligible` in addition to20 named definitions/results. The Ova paper's current TeX SHA256 is `184475df5905052ccff58aa33fe61a9b51ded5d7a89b40d2776f5e72ec12ab9c`. These changes alter no mathematical statement or Lean proof. All three current papers were rebuilt, and every rendered page was visually inspected. Stale verification records and lane-relative README paths were replaced. Canonical MathDB source records now retain selected question fields rather than full third-party solution bodies; the full source snapshots remain in the development lane.
