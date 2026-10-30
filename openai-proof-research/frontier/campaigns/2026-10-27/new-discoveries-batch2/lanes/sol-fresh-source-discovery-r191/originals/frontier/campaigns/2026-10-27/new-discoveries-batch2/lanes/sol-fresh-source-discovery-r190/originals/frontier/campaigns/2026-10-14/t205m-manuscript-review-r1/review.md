# T205M independent manuscript review, round 1

**Verdict: PASS_FULL_MANUSCRIPT_T205M.**
Required repairs: none.
Optional items: O1-O4 below. They improve exposition or context; none
affects correctness, quantifiers, credit, or reproducibility.

This review covers the immutable manuscript packet
`frontier/campaigns/2026-10-14/t205m-manuscript-v1/` only. It is not a new
contribution decision or an acceptance decision, and it changes no campaign
count (14/20 at dispatch). No favorable presumption was applied.

## 1. Target and claim checked

Theorem 1.1 states, for every integer m >= 2, N = m(m+1)/2,
rho_m = (m, m-1, ..., 1), and every lambda |- N other than (N) and (1^N):
g(rho_m, rho_m, lambda) >= m-1 for the ordinary complex diagonal tensor
square, with equality at (N-1, 1). This is exactly the frozen full target
(scope 3eb9d790...). Section 1 explicitly disclaims symmetric/exterior
components, the cyclic submodule, integral and modular statements, and the
I19/I21 signed target. No restricted family, asymptotic-only or minimum-over-
cyclic statement is substituted. The quantifiers in (1.1), (2.6) and Section 8
agree.

## 2. Identity and inventory

Every anchor in the brief was hashed externally before use and matches:
manifest 88bf34eb...782f26, article.tex 035d5cc2...cfbe1, PDF 4144bf0f...34765,
public inventory d0bc6f05...e56c5, author manifest 29ab2fdb...41db9, candidate
17b2b35c..., scope 3eb9d790..., proof review 4b41e5dd..., contribution review
e70b5707..., formal 3037eddf..., formal review 5824a6bd..., certificate
5ffb1880...99263. My own checker (`identity_check.py`,
`identity-check-out.json`) confirms 29 checks, including all 60 provenance
receipts byte-equal to their originals, the I19/I21 credit copies byte-equal to
`frontier/iterations/`, and the canonical tree `sources/preprints-tree.json`
(eeecc1da..., 13223 entries, `truncated: false`) against which all 21 private
source blobs match their git blob SHA. The author `verify.py` passes with the
external anchor (183 payload + manifest = 184 files, 36 directories, 21 blobs,
10 primaries, 13 pages) and rejects a zero anchor with "external manifest
anchor mismatch"; its integrity controls pass all 14 cases with exact reasons
(`logs/`). `git status` shows the author packet clean before and after.

## 3. Mandatory new primary interface: KSS

I downloaded arXiv math/9901037v1 myself into /var/tmp. It is byte-identical
(sha256 06103df5...) to the packet's private copy, and my own `pdftotext` output
is identical too. I read Section 2.1-2.2 and Theorem 2.10 directly.

* (2.4): |nu^(k)| = sum_{j>k} lambda^t_j - sum_a mu_a max(eta_a - k, 0). With
  every rectangle a column, R_a = (1^{mu_a}) (eta_a = 1), the correction term
  vanishes, giving the manuscript's (5.1) with target alpha^t, i.e.
  |nu^(k)| = sum_{i>k} alpha_i.
* (2.5): P^(k)_n = Q_n(nu^(k-1)) - 2Q_n(nu^(k)) + Q_n(nu^(k+1)) + Q_n(xi^(k)(R)),
  nu^(0) empty, xi^(k)(R) the heights of width-k rectangles. Width-one
  rectangles give xi^(1) = mu and xi^(k) empty for k >= 2. This matches the
  manuscript's convention nu^(0) = mu in (5.2).
* Admissibility is P^(k)_n >= 0 for all k, n >= 1. There is no string-length
  cutoff, and the size constraints keep everything finite. This is the
  unbounded convention the manuscript needs (E1).
* Theorem 2.10 / (2.6) at q = 1 is the positive binomial-product formula (5.3).
  Its left side is the GL multiplicity of s_{alpha^t} in prod_a s_{R_a} =
  prod_a e_{mu_a}. Applying omega (omega e_r = h_r, omega s_beta = s_{beta^t})
  and Young's rule gives K_{alpha, mu}. Theorem 2.10 has no further
  hypothesis, and the manuscript applies it only with mu = rho_d.

The specialization is correct, and the manuscript states it accurately in
Section 5.1. I did not rely on the author's crosswalk. Kirillov credit for the
maximal configuration and the one-cell perturbation is retained (Section 5,
Section 8, bibliography [3]).

## 4. Source interfaces (stipulated truth, checked labels)

In the pinned private copies I read the five cited labels:
`thm:cyclic-saxl`, `dom:signed-average`, `dom:repeated-row-cyclic`,
`dom:noncancellation`, `dom:permutation-quotient` (`dominance.tex`);
`prop:band-quotient` (`band-quotient.tex`); `path:one-band` and
`prop:two-band` (`path-band.tex`). Each exists and supports the use in
Proposition 2.1:

* (i) support of every S^lambda in W_m;
* (ii) the *entire* induced module as a quotient for s in {1,2}, h = m-s >= 1;
* (iii) U_{m,1} = S^(m), and four-row support of U_{m,2} for m >= 3. Only
  this support is load-bearing (E5). The stronger band identification is
  labeled as context;
* (iv) the signed-average and repeated-row maps, the nonzero constant
  c_m = (-1)^{sum C(r,2)} prod r!, and the permutation-module quotient, which
  give [W_m:S^lambda] >= K_{lambda^t, rho_m} by Young's rule. I21's stronger
  isomorphism is noted as unused.

The recurrence (2.3) keeps the specified smaller cyclic modules W_{m-1},
W_{m-2}, never the ambient squares. Contributions are added only within one
quotient and maximized across quotients. Sign symmetry is used only for the
ambient square in (2.4), never for W_m. This matches I19 Section 4 and I21
Section 2.1 (both read in the provenance copies, byte-equal to the originals).

## 5. Mathematical audit of the new deductions

I re-derived every step by hand. Below, "checked" means I re-derived the step
myself and did not rely on the earlier reviews.

**Section 3 (wide, lambda_1 > m, m >= 9).** The interlacing generating
function (3.1) and the claim "every strictly interior coefficient of a product
of >= 2 nonconstant initial geometric sums is >= 2" are checked, including the
convolution step. The exception analysis is checked: a row predecessor forces
<= 2 rows; a column predecessor forces a hook whose two predecessors have
consecutive widths, which cannot both lie in {1, h}; if both H_h and J_h fit,
then nu' = (h+1, 1^{N_h-h-1}) interlaces (lambda_1 >= h+1 >= lambda_2,
lambda_2 >= 2 >= 1 >= lambda_3) and is nonexceptional. The one-band term then
gives (m-2) + 1. For rectangles (a^b), the complements of
eta_1 = (m+1, m-2) and eta_2 = (m, m-1) are as stated. Their nonexceptionality
is checked, including the m = 4 one-row coincidence. The two-band term gives
2(m-3) >= m-1.

**Section 4 (high capacity).** k = C - (2m-1) >= 2 is checked. The column
description of S = lambda/mu (rows max(1, H_j - 3) .. H_j, all nonempty) is
checked. The unique-rank ideal argument (adjoining b < a stays acyclic, and a
linear extension yields a second ideal) is checked, as are the four
column-position cases. The exception analysis is checked: the column, H_h and
J_h force lambda_5, lambda_6, lambda_7 <= 1; len(lambda) >= (m-2)(m-3)/2 >= 10
separates the four column-one cells; the predecessor lengths lie in
[H_1 - 4, H_1]; and the case k = 2 with both H_h and J_h gives
lambda_5 >= m-3 and C >= 4(m-3) > 2m+1. The four-row filling
(entry i - nu^t_j) giving c^lambda_{nu,eta} > 0 for some len(eta) <= 4 is
checked.

**Section 5 (low capacity, Lemma 5.1).** I recomputed the maximal
configuration directly from KSS: for k >= 2, P^(k)_j = min(j, alpha_k) -
min(j, alpha_{k+1}) >= 0, which is 0 at occupied lengths. P^(1)_j =
D_j + min(j, t+s) - min(j, t), using the self-conjugacy of rho_d. The
multiplicities b_j(nu^(1)) = L_j - L_{j+1}, minus 1 at j = t+s, are checked.
The E3 remark for s = 0 (actual multiplicity L_t - 1, D_t = 0, both factors 1)
is correct and present (lines 415, 422-424). The one-cell move (5.8) changes
only the vacancies on [u, v) by -2 and +1. The bounds (5.5), (5.9), (5.10) and
every width branch are checked, as follows.

* Widths 3 <= w <= d-2: the cases t = 1 to 4, then t >= 5 via the move with
  M + W in the w = d-2 subcase.
* Width two: the concave D_t, and for t > d with s <= d-2 the alternative
  configuration (t-2, 2) with first vacancies d-4, 2d-9, ..., s and weight
  (2d-8)(s+1).
* Width d-1: t = 2 gives (d-v) C(d-1, v-1). For t >= 3, a < d/2 uses the
  maximal factors, and a >= d/2 uses the move u = 2, v = t with weight
  (a-1)^2 >= d.

The listed exceptions have the stated weights. The no-cutoff remark is apt:
the (t-2, 2) configuration has a string of length t-2 > d.

**Section 6 (assembly).** The column-deletion identity (6.1) is checked in
both directions. The E2 exclusion L_1 = h+1 by area is present (line 562).
The case L_1 = h is excluded, and L_4 <= (h+1)/3 gives top-four sum
<= 4(h+1)/3 <= 2h. Lemma 5.1 at d = h = m-1 gives K >= m-1 off its listed
shapes. Transporting the shapes back is checked: column -> H_m,
(2,1^...) -> J_m, double-(h-1) impossible (2h-1 > h+1), and (h-1, 1^...) ->
(m, m-2, 1^{N_m-2m+2}). Lemma 6.1 is checked: lambda/nu is D plus a
detached four-cell column, s_D = h_{m-2}h_{m-3} - h_m h_{m-5} =
s_(m-1,m-4) + s_(m-2,m-3) (valid for m >= 5), and multiplying by e_4 gives
(m, m-3, 1, 1) and (m-1, m-2, 1, 1). The sum is in fact exactly 2 (my
recomputation gives lr4 = 2 at m = 7, 8). nu = (2, 1^{n-2}) lies outside
E_{m-2}, so the contribution is 2(m-3) >= m-1.

**Section 8.** Every label other than the row and the column is either
outside E_m or equal to H_m or J_m. The transposes of H_m and J_m have first
part N_m - m + 1 or N_m - m, which exceeds m, so they lie outside E_m. Then
(2.4) gives the bound. The corner value is checked:
<Res chi, Res chi> - 1 = (number of removable corners) - 1 = m - 1.

No mathematical error, gap, or quantifier mismatch was found.

## 6. Finite part: independent recomputation

`independent_finite.py` imports nothing from the author or manuscript code.
Its algorithms differ from both the author's code and the proof reviewer's:

* characters by Murnaghan-Nakayama over cell-indexed rim hooks;
* Kostka numbers by largest-letter strip removal, cross-checked against
  brute-force SSYT enumeration for n <= 7;
* four-row LR sums by Weyl alternation of the four-variable skew Schur
  polynomial, cross-checked against brute-force lattice LR tableaux on all
  pairs with n <= 8 and |lambda/nu| <= 6.

It also checks character orthogonality (n <= 8) and dimensions (n <= 9). The
certificate is read only after recomputation, for an entrywise comparison.

Results (`independent-finite-out.json`: PASS_REVIEWER_INDEPENDENT_FINITE).

* **Algorithm self-checks.** All pass, including 707 LR pairs against
  brute-force lattice tableaux.
* **Small squares.** The minima over nonrow, noncolumn labels are 1, 2, 3 at
  m = 2, 3, 4. The corner value is m-1 for m = 2 to 5. At m = 5 the minimum is
  also 4 (evidence only). Every small-square coefficient in the certificate is
  equal entrywise.
* **Exact recursion R_m for m = 2 to 6.** Computed from R_1 with
  max(1, K, one-band, two-band), using exact LR sums. All 1024 certificate
  rows (K, one, two, R) are equal entrywise. Invariant (2.6) holds at h = 5, 6
  on all 172 and 788 nonexceptional labels, with minima 4 and 5. On the
  exceptions, R(H_h) = 1 and R(J_h) = h-2. This shows why J_h must be an
  exception.
* **Boundary m = 7, 8.** I used the weights of (2.6) (h-1 off E_h, 1 on E_h)
  at m-1 and m-2.
  * At m = 7 (3718 labels): the weighted one-band sum settles 2349 labels and
    K >= m-1 settles 1120. On all 245 remaining labels, the exact-LR two-band
    sum is at least 11.
  * At m = 8 (17977 labels): one-band settles 12161, K settles 4948, and on
    the remaining 864 labels the exact two-band sum is at least 13.
  * These equal the manuscript's table (four-strip + critical = 244 + 1 and
    863 + 1).
  * The minimum equals the value at the critical label
    (m, m-2, 1^{N_m-2m+2}), which is 11 and 13. These equal the proof review's values, which
    were computed differently. The critical LR sum for nu = (2, 1^{n-2}) is
    exactly 2 at both orders.
  * Exact LR here replaces the author's four-strip lower bound, so this also
    checks that bound's use independently.

Public verifier. I ran `python3 -B code/verify-finite-proof.py` in its
default mode on a /var/tmp copy of `public/`. It returned PASS_FINITE_BASES
with certificate sha 5ffb1880...99263, exact cyclic recurrence counts
2/11/42/176/792 (nonexceptional 172 and 788 at m = 5, 6), and boundary counts
m = 7: one 2349, K 1120, four-strip 244, critical 1; m = 8: one 12161,
K 4948, four-strip 863, critical 1. These equal the table in Section 7.2. `finite-crosscheck.py`
returned PASS_FINITE_GRID_CROSSCHECK (3582 character values, degree <= 10). In
a wrong control, I changed one K entry of the certificate in a separate copy;
the verifier exited 1 with "finite certificate differs from exact
recomputation". This confirms that the certificate is recomputed and not
accepted by hash. The copy stayed byte-identical to canonical `public/` after
the positive run. The critical branch invokes the symbolic Lemma 6.1 and says
so (E4).

Lemma-statement controls (evidence only, `lemma_controls.py`). These check
the all-order lemma statements beyond the finite starts:

* Lemma 5.1 at d = 8, 9 (1129 and 3788 shapes): no violation. The listed
  noncolumn shapes have K exactly d-1, and the minimum K off the list is 21
  and 28.
* Lemma 4.1 at m = 7 to 10 (up to 98946 shapes): at least 3 usable
  predecessors in every case.
* The Section 3 wide case at m = 9, 10 (63802 and 338471 shapes): the
  weighted one-band minimum is exactly m-1, and the only rectangles are
  (15^3) and (11^5).

None of these is used as a proof.

## 7. Build, PDF, and visual check

I read `public/build.py` before running it. It builds with tectonic 0.17.0
(sha a98aa59a...) from the canonical `public/` into a new /var/tmp directory,
and separately from an isolated copy of `public/` alone. Both builds exited 0
and produced the PDF 4144bf0f...34765, byte-identical to the anchored PDF.
`public/` was unchanged afterwards. There were no LaTeX warnings beyond a
package banner and no hidden private dependency. The receipt's source hashes
match (article.tex 035d5cc2..., certificate-hash.tex 4f58bce8...). pdfinfo
shows the correct title and author, 13 pages, and the fixed creation epoch. I
inspected all 13 pages at 110 dpi. The equations, the Section 7 table, the
references [1]-[12], and the hyperlinks render correctly. The certificate
hash printed on page 11 equals the actual certificate hash. Build receipts,
public-verifier outputs, and artifact hashes are copied into `logs/`.

## 8. Prior objections

| Item | Status in manuscript |
|---|---|
| E1 unbounded string lengths | Implemented by the KSS specialization (Section 5.1), independently confirmed in Section 3 above. |
| E2 exclude L_1 = h+1 | Implemented, line 562. |
| E3 s = 0 vacancy and multiplicity | Implemented, lines 415 and 422-424; correct. |
| E4 critical branch symbolic | Implemented and disclosed in Section 7.2 and in the verifier. |
| E5 only four-row support load-bearing | Implemented in Proposition 2.1(iii) and its proof. |
| E6 no campaign count, history not mathematical | Implemented; no count appears in the article. |
| C1 I19 Section 4 / I21 Section 2.1 credit | Implemented (Sections 1, 2, 8, references [8], [9]). |
| C2 new-to-project only; parent high-capacity authorship | Implemented (Sections 1, 4, 8, references [10], [11]). |
| Formal coverage | Section 7.3 states 17 declarations = 2 definitions + 15 theorems, the generic poset coverage, and the unformalized geometric no-cut, exceptions, Kostka, LR, representation theory, finite bases, and full induction. It claims no optional formal improvement. Consistent with the sealed formal review. |

## 9. Optional items (not required)

* **O1 Literature context.** The sealed contribution review read two items
  that the article does not mention. The first is Pak-Panova's general lower
  bound g(lambda, mu, mu) >= |chi^lambda[mu-hat]| for self-conjugate mu, which
  vanishes on many labels and so gives no uniform floor. The second is the
  open question min_lambda g(lambda, rho_k, rho_k) in Lee, arXiv:2512.15035v1
  (unrefereed). A sentence in "Literature comparison and claim boundary" would
  help readers. If Lee is cited, cite it as a pointer to the question only,
  after the author reads it. Nothing in the article is false without these
  references, and it claims no priority.
* **O2 Section 4, "at most two exceptions fit simultaneously".** The stated
  reason is the width-four length window with h >= 5. The precise reason is
  that the column and J_h differ in length by h >= 5. The column and H_h differ
  by h-1, which equals 4 at h = 5 and can fit in the window. Stating this
  explicitly would avoid a reader's double take. The conclusion is correct.
* **O3 Section 7.3.** The unformalized list could also name the
  ideal-partition bridge (mu subset nu subset lambda <-> order ideals of S),
  and could say that the 17 declarations are 7 in `T205M.lean` and 10 in
  `Controls.lean`. The present wording claims no formalization of either, so this
  is clarity only.
* **O4 Table in Section 7.2.** The proof review reported "two-band" counts 245 and 864,
  which include the critical label. A footnote that four-strip + critical
  equals those totals would ease cross-reading.

## 10. Limits

See `reading-limits.md`. In brief: I treated source truth as a premise; I did
not re-prove KSS Theorem 2.10; I did not re-read Kirillov directly; I ran no
fresh literature search; I did not rebuild the Lean code; and every
computation was run once on one machine. This review makes no acceptance or
count decision.

## 11. Seal

`seal.py` writes `review-manifest.json` (exact inventory, verdict,
manuscript anchor, PDF hash, `campaign_count_change: false`). The external
sha256 of that manifest is reported outside this directory. `verify.py
--anchor <sha>` checks bytes only. `review_controls.py` reruns the positive
case and 18 wrong or mutation cases on /var/tmp copies, each with a checked
rejection reason.
