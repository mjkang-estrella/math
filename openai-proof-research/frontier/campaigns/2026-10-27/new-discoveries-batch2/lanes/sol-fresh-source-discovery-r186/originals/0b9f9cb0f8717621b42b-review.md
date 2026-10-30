# Preliminary adversarial review — Svinin Conjecture 3.1 ordinary proof candidate

Slot 3, 2026-10-28. Reviewer: pi (GLM-5.3-Flash, thinking high), SOLO, no children.
Reviewed candidate: frozen `../root-svinin-shape-r11/` @ review-freeze.json (15 entries).
All 15 SHA-256 verified before review; own copy in `frozen-copy/`; all 15 re-verified
unchanged after review (see `frozen-copy/hashes-after-copy.txt` and `provenance.json`).

## VERDICT: HOLD

- SOURCE: PASS (arXiv:1610.05387v2 Conjecture 3.1 and all definitions read literally
  from the actual cached v2 HTML; two residual flags below, non-blocking for a
  preliminary review, blocking before any acceptance).
- MATH: PASS (independent line-by-line re-derivation confirms every step; two-route
  bounded computational check agrees; no gap found).
- NOVELTY: HOLD (closest prior-art body — the author's own 2019 J. Math. Sci.
  239(2):159–171 — could not be lawfully obtained via public routes exhausted
  today; per the task rule, unread closest body => HOLD).
- SUBSTANTIVE: HOLD (no known public exact theorem found and no classical bridge
  located, but the proof is short and built from Concrete-Mathematics-level
  ingredients; the routine-corollary objection cannot be finally dismissed while
  the closest body is unread).
- FORMAL: not assessed; no Lean endpoint exists, no formal PASS claimed.

## SOURCE gate (PASS)

Read from `frozen-copy/sources/svinin2016-v2.html` (actual arXiv HTML, v2):

- Section 2: `(a+...+a^n)^j = sum_{q=0}^{j(n-1)} C_{j,q}(n) a^{q+j}` (2.1) and
  `s_{k,j}(n) := sum_q C_{j,q}(n) x_{j+q}`, `x_r := r^{2k+1}`. Hence `s_{k,j}(n)`
  equals literally `sum over j-tuples in {1..n}^j of (x_1+...+x_j)^{2k+1}`: the
  coefficient of `a^{j+q}` counts exactly the tuples with coordinate sum `j+q`.
  The candidate's tuple definition of `s` is a literal restatement. Verified.
- Section 3: `S_{k,j}(n) = sum_{q=0}^{j-1} binom(j(n+1),q) s_{k,j-q}(n)` (3.1);
  reindexing r=j−q gives the candidate's `sum_{r=1}^{j} binom(M,j-r) s_{k,r}` with
  `M=j(n+1)`. Verified.
- `S~_{k,j}(n) = sum_{λ∈B_{j,jn}} {λ_1^{2k+1} + (λ_2−n)^{2k+1} + ... +
  (λ_j−jn+n)^{2k+1}}`, `B_{j,jn} = {1≤λ_1≤...≤λ_j≤jn}` (weak tuples). This is
  exactly the candidate's `sum_i (λ_i−(i−1)n)^{2k+1}`. Verified.
- Conjecture 3.1: `S~_{k,j}(n) = S_{k,j}(n)` for all k≥0, j≥1 (n implicit ≥1 in
  the paper's setting). Only j=2 is proved in the source. Scope of the candidate
  (all k≥0, j≥1, n≥1) matches. No even-exponent claim is made anywhere; the
  candidate's antisymmetrization produces exactly odd exponents and claims nothing
  for even ones — no silent odd/even issue.
- arXiv v2 date confirmed via arXiv API: 1610.05387v2 updated 2017-03-01.
- MathDB 334350 cached snapshot: post_type "conjecture", status "open",
  lean_formalization_count 0. Recorded as a status fact only; never novelty evidence.

Residual source flags:
1. The 2018 journal PDF (Exp. Math. 27(4), DOI 10.1080/10586458.2017.1306815) was
   not visually read. Indexed texts (zbMATH 1405.11026, MathSciNet MR3894723 via
   Springer reference list) agree with the arXiv v2 statement.
2. Page-range discrepancy: the task brief says "437–443"; zbMATH and the Springer
   reference entry both give **437–448**. Root's brief likely has a typo; must be
   corrected in any paper-stage provenance.

## MATH gate (PASS)

I re-derived the whole route independently before running anything:

1. Pointed subsets `a_i = λ_i + i − 1` biject weak tuples with j-subsets of
   {1,...,M−1}; `λ_i − (i−1)n = a_i − (i−1)(n+1)`; count
   `binom(a−1,h) binom(M−1−a, j−1−h)` for rank h. Gives candidate eq. (2). Checked
   by direct re-enumeration in my script (order-statistic count == literal weak-
   tuple count for all 20 grid pairs).
2. Sum over a of `z^a(1+u z^{−(n+1)})^{a−1} B^{M−1−a}` with B=1+u telescopes to
   `z(B^{M−1}−R^{M−1})/(B−R)`, R=z+u z^{−n}; `B−R=(1−z)(1−u A_−)` (expanded and
   verified: (1−z)−u(1−z)(z^{−1}+...+z^{−n}) = (1−z)+u(1−z^{−n})). ✓
3. `[u^{j−1}] B^{M−1}/(1−uA_−) = T(A_−)`. ✓
4. `[u^{j−1}] R^{M−1}/(1−uA_−) = z^n T(A_+)`: exponent
   `M−1−(n+1)(j−1−r) = j(n+1)−1−(n+1)(j−1)+(n+1)r = n+(n+1)r` and
   `z^{n+1}A_− = A_+`. ✓ (This is the only place M=j(n+1) enters; confirmed
   exact, not off-by-one.)
5. Inversion: `C(z^{−1}) = (T(A_+)−z^{−n}T(A_−))/(z−1)`; subtracting,
   `(1−z^{n+1})/(1−z)=1+A_+` and `(z−z^{−n})/(1−z) = −(1+A_−)`
   (checked: multiply num/denom by z^n). ✓
6. Pascal: `(1+A)T(A) = binom(M−1,j−1) + H(A)`, coefficient
   `binom(M−1,j−1−s)+binom(M−1,j−s)=binom(M,j−s)` for 1≤s≤j−1, top coefficient
   binom(M−1,0)=1=binom(M,0). Constant cancels in (4). ✓
7. Moment functional: L[H(A_+)]=S (positive exponents only), L[H(A_−)]=−S
   (odd f), L[C−C^{inv}]=2S~, hence S~=S for f(q)=q^{2k+1}. ✓

My independent check `check_review.py` (own code, pure-dict exact Laurent
arithmetic + brute-force enumeration, no sympy, peak memory well under 1 MiB):

- Route A: literal weak-tuple enumeration (S~ side) vs literal r-tuple
  enumeration with binom(M,j−r) weights (S side), moment equality for
  k=0..6, all 20 pairs n=1..4, j=1..5. All match. (This directly tests the
  exact conjecture, independent of the proof.)
- Route B: full Laurent identities `C−C^{inv} = H(A_+)−H(A_−)` and
  `(1−z)C − z T(A_−) + z^{n+1} T(A_+) = 0` verified coefficient-wise for all
  20 pairs; odd-exponent moments of H(A_+) cross-checked against S~ moments
  for k∈{0,3,6}. All match.
- Edge j=1, n=1, k=0: S~_{0,1}(1)={1^1}=1=S_{0,1}(1). OK.
- Results: `review-checks.json`; script `check_review.py`.

Note: the frozen checker's `sp.cancel` identities and my dict-algebra identities
are different computational routes and agree. Two reviewer-caught bugs were in my
own scratch code (constant polynomial encoded `{0:1}` not `{1:1}`; a wrong extra
assert), not in the candidate. No defect found in the candidate's proof or checks.
The proof is complete, all-parameter, uses no limiting/interpolation argument,
and the only genuinely special input is the coefficient relation M=j(n+1).

## NOVELTY gate (HOLD) — the decisive open item

Closest prior art: A. K. Svinin, "Generalization of the Power Sum Arising in the
Theory of Integrable Hierarchies", J. Math. Sci. 239(2):159–171 (2019),
DOI 10.1007/s10958-019-04299-6, translated from Problemy Matematicheskogo
Analiza 96 (2019) 43–53. Same class of odd-power multiple sums. Body UNREAD.

Access attempts (2026-10-28, all lawful public routes; failures recorded):
- Springer landing: public content = abstract + reference list only; subscription
  content; no OA PDF. Abstract: "We consider a class of multiple sums involving
  odd powers of natural numbers... continuous limit of the integrable hierarchy...
  Itoh–Narita–Bogoyavlenskii lattice. We discuss the problem of constructing
  polynomials that allow us to calculate the values of the corresponding sums."
  Does not state whether 3.1 is proved. Received 13 Nov 2018, published 24 Apr 2019.
- Unpaywall API: `is_oa:false`, `has_repository_copy:false`, zero OA locations.
- Semantic Scholar API: `openAccessPdf` CLOSED, abstract elided, **citationCount 0**.
- zbMATH Open API (doc 7084260 = an:1416.37064): review text "unavailable due to
  conflicting licenses"; full public reference list obtained: cites only Knuth
  (Faulhaber), Svinin 2011/2014, Itoh, Narita, Bogoyavlenskii, Svinin Exp.Math 2018,
  Graham–Knuth–Patashnik, Agoh–Dilcher, Adelberg, Kimura–Siebert, Tuenter,
  Gandhi. No identity-type source that could contain a same-object proof.
- ResearchGate: first-page preview only (per root; not re-attempted).
- MathNet.ru: `jrnid=pma` is "Progress in Mathematics" (wrong journal);
  "Problemy Analiza" (jrnid=pa) is a different series (2019 ≈ vol 26, not 96);
  PMA is a Nauchnaya Kniga (Novosibirsk) print interuniversity collection, not on
  mathnet. Svinin's MathNet person page (personid=18154, 11 publications) omits
  the paper — omission is not clearance but confirms no public full text there.
- arXiv API (42 results for au:"Svinin"): no arXiv version of the 2019 text.
- scholar.archive.org: browser challenge (captcha) — NOT bypassed.
- Web searches (EN/RU) for the Russian original and any posted PDF: nothing.

Indirect signals (weak, non-clearing):
- 0 citations: nobody has built on it publicly either way.
- Author's own 2018 preprint 1806.07022 (= Izv. VUZ Mat. 2019 no.8 / Russian Math
  63(8)) and 2017 preprint 1710.04779 both retain (3.3)/(3.2) as a hypothesis —
  but both predate the 2019 submission (13 Nov 2018). The 2019 body could close it.
- Author's next paper (ivm9613, arXiv 1911.10650, Genocchi polynomials; full text
  read on mathnet) does not cite the 2019 paper and does not address the
  multiple-sum conjecture — consistent with either outcome.
- Abstract phrasing emphasizes polynomial construction (conjectures 5.x/6.x
  territory), but S~-type sums are exactly "multiple sums involving odd powers";
  proving 3.1 en route is plausible. Cannot be resolved from the abstract.

Per the task rule: unread closest body => NOVELTY = HOLD. Exact prior proof =>
FAIL; only actual body access can move this to PASS.

## SUBSTANTIVE gate (HOLD)

- No public exact theorem producing S~=S for j≥3 was located. The author's visible
  record (2016 conjecture paper, 2017, 2018/ivm9490) treats it as conjectural for
  j≥3; j=2 is elementary (source itself).
- No cycle-lemma / ballot / Lagrange-inversion / Abel / Vandermonde bridge giving
  the exact cancellation `C−C^{inv} = H(A_+)−H(A_−)` was found. The structure
  resembles a queue/reflection count for lattice walks with steps in {1..n} vs
  {−1..−n}, but no published same-object identity is known to me.
- Honest tension: the proof uses only Concrete-Mathematics-level tools and is
  short. The author (an expert on exactly this object) proved j=2 "using simple
  arguments" in 2016 and evidently did not see the general antisymmetrization
  through 2017–2019 — which cuts both ways: it shows the step is not a
  mechanical routine corollary for the field (nobody, including the originator,
  recorded it), but also that once seen it is elementary. Under this project's
  rules, shortness alone is not failure; no known public theorem subsumes it.
  However, if the unread 2019 body proves 3.1, the candidate is both subsumed and
  likely method-near-duplicated. SUBSTANTIVE cannot be PASSed while NOVELTY is
  HOLD; it also cannot be FAILed on present evidence.

## Remaining Lean bridges (if the candidate survives to formalization)

1. Literal weak-tuple type: define S~ over `1≤λ_1≤...≤λ_j≤jn` with signed terms
   `(λ_i − (i−1)n)^(2k+1)`; do NOT assume the pointed-subset reindex without
   proving the bijection `a_i = λ_i + i−1` in Lean.
2. Counting reindex: prove `sum over pointed subsets == [u^{j−1}]` coefficient
   extraction, then the telescoping/finite-geometric steps over Q(z)[[u]] — or
   avoid u entirely and prove the Laurent identity by induction on the pointed-
   subset sum; either way every binomial identity (Pascal step, the two
   geometric quotients, `z^{n+1}A_− = A_+`) must be proved, not assumed.
3. Coefficient-moment identity: prove the linear odd-functional step
   `L[C−C^{inv}] = 2 S~` and `L[H(A_+)]−L[H(A_−)] = 2S` for `f(q)=q^{2k+1}`
   (uses oddness only), with literal `s_{k,r}` as tuple sums matching the
   source's coefficient definition via `[a^{j+q}](a+...+a^n)^j` counting.
4. Endpoints: only propext/Classical.choice/Quot.sound; no sorry/admit/axiom/
   unsafe/native_decide.

## Reviewer independence statement

I did not run or modify the frozen checker as-is; I wrote my own script and
derived all steps myself. No other lane or shared file touched; no git
operations; no external communications; no child agents; no captcha/paywall
bypass (scholar.archive.org challenge respected; Springer/Unpaywall/S2/zbMATH/
arXiv/MathNet queried within their public terms, low volume).

- Strongest objection: the 2019 J.Math.Sci/PMA 96 body is unread and is by the
  same author on exactly this class of odd-power multiple sums, submitted after
  three conjecture papers; if it proves 3.1 the candidate dies, and if it uses a
  similar antisymmetrization the candidate also loses substantive eligibility.
  Every lawful public route to that body failed today (documented above).
- Second objection: the proof is short and classical; even absent a same-object
  prior proof, a referee could call it a routine corollary of elementary
  generating-function manipulations. Its eligibility rests on the demonstrated
  fact that the exact cancellation was not recorded by anyone through 2019
  (visible record), which is an argument about the record, not about depth.
- Third (minor) objection: root's brief cites Exp. Math. 27(4) as pp. 437–443;
  zbMATH/MathSciNet say 437–448 — provenance error to fix before paper stage.
