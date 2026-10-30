# T117Q contribution and eligibility review, round 2

Role: independent contribution gate, round 2 (Factory Opus 5.5). This directory supersedes
the round-1 directory assignment. I did not modify round 1, the frozen author packet or the
frozen parent response. Correctness of the final candidate is ASSUMED for this gate only.
The separately adopted proof pass is not used as evidence of substance. No formal,
manuscript, acceptance, ledger or count judgement is made (count stays 14/20). I did not
read any parallel reviewer draft.

## Verdict

**SUBSTANTIAL survives** the added antecedents (still conditional on the independent full
proof pass). Literature novelty is NOT demonstrated; the classification remains
new-to-project with bounded literature coverage.

Response-level status of the round-1 items (the manuscript must still implement all of them):

| Item | Status at response level |
|---|---|
| RQ1 | Addressed, with a verified correction to round 1 and two required refinements (R2-A, R2-B). |
| RQ2 | Addressed. One required addition about the bi-Lipschitz corollary (R2-C). |
| RQ3 | Addressed for ordinary grid substitution. Required refinements R2-B and R2-C. |
| RQ4 | Addressed. |

No checked antecedent, and no reduction I could find or that a read source supplies,
yields the frozen statement or makes the spectral chart selector (candidate §3, Lemma 2)
routine. The required objections are listed in "Required objections".

## Inputs authenticated (identity only)

- Round-1 review MANIFEST.json SHA256 = 6d6366df9904a9d49db95e218c1daf52b444878ee2ec9ecf6938f9b84dfb5013
  (external anchor). Its 7 listed payloads match. Its verifier passes with this anchor and
  rejects a wrong anchor, both on a /var/tmp copy.
- Parent response manifest.json SHA256 = c93929fee2e269bb07015e91254aa8865a57a45a2b9879068da8f52ea0f9deb8,
  response.md SHA256 = d697cfcb0e23fd40ada330443eaf524cbc88318c827d2f771915eaf8df3aeb22.
  The full local inventory (20 files, including 12 ignored private primary files, one
  directory) matches exactly. On a /var/tmp copy, after authenticating the copy, the
  parent's integrity_controls.py passed all 15 cases with their reason strings (only
  `positive` accepted). Its grid_control.py replay (Python 3.14.7, /tmp/agvenv, NumPy 2.5.3
  present but unused) gave JSON identical to grid-control.json.
- Author MANIFEST.json SHA256 = 053986e5…e28ae2; candidate.md e32f7a12…aeea4,
  original-scope.txt fc5a8f87…fe36 and checkpoint.md 0a9a4526…fab2 all match. The author
  verifier passes on a /var/tmp copy (52 payloads, 12 directories, 20 pinned blobs) and
  rejects a wrong anchor. I recomputed all 20 source Git blob ids directly and found each
  at exactly one matching path in the complete canonical sources/preprints-tree.json
  (SHA256 eeecc1da…dc5e09b, 13223 entries, truncated=false).
- Primary copies that the parent took from the round-1 cache have identical SHA256 in
  both places (JLW, NPS, Naor–Young, CEE; pdf and txt).

Details: replay-record.json. No checksum is mathematical or novelty evidence.

Scope, chronology and source-family eligibility are unchanged from round 1: the candidate
and frozen scope bytes are the same, and the response changes neither. I keep the full
frozen scope: every complex Hilbert space H, every 1-Lipschitz map into S_1(H), ordered
uniform pair averages, genuine negative-type metrics, exponent 9/2.

## RQ1: comparisons

### Naor–Pisier–Schechtman and Naor–Young

I checked the parent's descriptions against the bodies (NPS lines 240–330; Naor–Young
lines 590–640). They are accurate: NPS concern dimension reduction and finite-dimensional
subspaces of S_1 and note that coordinate sampling "seem[s] to be inherently commutative";
Naor–Young Question 13 concerns bi-Lipschitz embeddings of the Heisenberg group.

I also tested one possible reduction the parent did not discuss. NPS Theorem 12 (read as
stated in their introduction) embeds any d-dimensional subspace of S_1 into S_q with
distortion d^(1-1/q). In Lemma 2 all relevant matrices span at most m+Sm+SN dimensions, so
q-1 is about (log m)^-2. Type q of S_q then bounds E||sum_j g_j A_sj|| by about
m^(1/q) max_j ||A_sj|| <= N t m^(1/q-1/2), which is N t m^(1/2-o(1)). Lemma 2 needs
C N t (q/m)^(1/2). The transfer loses the whole gain, so it does not trivialize the selector.

### Cordero-Erausquin–Eskenazis Theorem 13 with Luo–Wang–Zhou

**The parent's correction is right.** In CEE's proof (lines 1943–1980), inequality (123)
is the Talagrand-type inequality for the lifted map F = f∘[·]. Inequality (125) uses only
the upper Lipschitz bound. So for any 1-Lipschitz f on a cube quotient one gets

    E_{eps,delta} ||f[eps]-f[delta]|| <= (tau/2) sum_i 1/psi^-1(1/sigma_n(d_i R)),

an average under the pushforward of the uniform pair measure. Round 1's remark "It is also
bi-Lipschitz, not uniform-average" is withdrawn. LWW (abstract and Theorem 1.1) gives S_1
Talagrand type (1, psi_{1,1}) with psi_{1,1}(t) = t/log(e+t).

**Round 1 also overstated the size cap, and the parent did not correct this.** Round 1
said the gain is "at most of order log(dimension) = O(log log of the number of points)".
That presumes the cube dimension is polylogarithmic in the number of classes, which the
route does not force. The correct cap is as follows.

- With t = 2u log(e+u), one has log(e+t) <= 2 log(e+u), because
  e + 2u log(e+u) <= e + 2u + 2u^2/e <= (e+u)^2. Hence psi^-1(u) <= 2u log(e+u).
- A coordinate-path argument gives a_1(R) <= (1/2) sum_i sigma_i. (The intermediate point
  is uniform, and the flip at step i occurs with probability 1/2 independently of it.)
- Therefore the lower bound produced by (37) with p = 1 is at most
  2 tau^-1 max_{i: sigma_i > 0} log(e + 1/sigma_i) <= C n.

So the route's gain is logarithmic in the inverse influences. It is not a priori capped
by log log N.

**Is there a known or source-provided reduction?** I found none. I checked three things.

1. *Target symmetry.* CEE Theorem 42 gives L_1 the same Talagrand type (1, psi_{1,1}) that
   LWW gives S_1. A T117Q-strength output of this route would therefore also prove a
   near-sqrt(log n) uniform-average L_1 bound for negative-type metrics by a Talagrand
   argument. Source117 does not do this. A search of all source117-1 tex files finds no
   Talagrand, KKL, influence or cotype argument, and its final step is the component-wise
   good-chart argument (main.tex lines 270–283).
2. *The source family itself.* The candidate's averages are pushforwards of uniform
   measure on T = (-1,1)^m under the first-chart labels. That is structurally close to
   CEE's pushforward. However, the metric is not a 0/1 cube-quotient metric. On the
   candidate's own representation, a coordinate-sum (Enflo type 1) bound gives
   sum_j E||d_j H_1||_1 <= m · N · O(m^-1/2) · C(m/N)(log m)^3 = C m^(3/2)(log m)^3.
   That exceeds the trivial diameter bound Cm, while the theorem needs C m^(1/2)(log m)^(7/2).
   The required gain is a polynomial Gaussian cancellation across coordinates. An
   influence-logarithmic gain could supply it only through coordinate increments supported
   on sets of measure about exp(-c sqrt m). No such discretization of T is supplied, and I
   did not find one.
3. *A ready-made family.* No read source supplies negative-type quotient metrics with
   equal (or uniformizable) classes and the required influences.

This is a comparison of supplied hypotheses and operations, not an impossibility theorem.
Classification is unchanged.

### KNT, quantum expansion

Round-1 points 3 (KNT Theorem 34 snowflake) and 6 (Escudero Gutiérrez–Muguruza §3.2) are
not contested by the response and remain part of the required manuscript comparison.

## RQ3: sharp metric cotype and nonlinear smoothing

I read Jiao–Luo–Wu arXiv 2610.21445v1 in full (all 1182 extracted lines): Theorem 1.3,
Lemmas 3.1–3.2, Proposition 4.1, Lemma 5.1, Proposition 5.2, the proof Steps I–III and
Corollary 6.1. I also read GMN §1.3 including Question 3, and the MN proof of Theorem 1.12
together with MN Lemma 6.12.

**Grid substitution.** The parent's two arguments are correct, and I re-checked them
independently with exact arithmetic (independent_checks.py).

- For uniform U, V on {0,…,k}, E|U-V| = k(k+2)/(3(k+1)) >= k/3, and E d_inf <= k. So
  x -> x_1 P (P a rank-one projection) is a 1-Lipschitz map with uniform first-average
  ratio at least 1/3, for all d and k.
- The six-point form equals 2 > 0. It survives zero-padding into larger grids.

The first argument is decisive for the T117Q scope, because it applies to any metric that
is boundedly equivalent to a grid. The second shows only that d_inf itself is not of
negative type (see optional item E1).

**Does sharp cotype give a direct reduction?** No such reduction is supplied, and I see no
routine one.

- The cotype inequality bounds the l_2 sum over coordinates j of long antipodal jumps
  x -> x + (m/2)e_j by local jumps. To control the uniform first-moment pair average on a
  negative-type family M, one would need a map phi from Z_m^n to M. The single-coordinate
  antipodal pair law of phi would have to carry a fixed fraction of the uniform pair law
  of M, while local jumps stay short. Grids fail this, which is exactly why their uniform
  average distortion is bounded. No such phi is supplied for source117 or any read family.
- The same target symmetry applies: L_1 also has sharp metric cotype 2 (Cheng–Wang–Xiang,
  as cited by JLW; not read).

**Does JLW's nonlinear mixing smoothing make the selector routine?** No.

- Lemma 2's bound (3.1) is an UPPER bound on a Gaussian average E||sum g_j A_j||_1.
- JLW Proposition 5.2 gives an l_2-gradient bound,
  (sum_j ||d_j g||_1^2)^(1/2) <= 6 sqrt(70) E_W ||F(z+W)-F(z)||_1.
- In S_1 an l_2 gradient converts to a Gaussian average only with a loss of up to sqrt m.
  For example, with A_j = e_j e_j^*, the l_2 sum is sqrt m while E||sum g_j A_j||_1 equals
  m sqrt(2/pi). That loss is exactly the gain Lemma 2 provides.
- Moreover, at smoothing scale lambda, the source macro estimate (4.2) makes the input
  oscillation of order m·lambda. JLW smoothing followed by an l_1/l_2 gradient Poincaré
  bound therefore again gives order m^(3/2) on this family.
- Cotype is a lower-bound property for Rademacher/Gaussian sums and cannot supply (3.1).
- JLW's Φ_mix factorization controls oscillation, not the multichart coefficient
  structure A_sj = sum_i u_sij b_si. Nothing in JLW performs a Loewner-order spectral
  cutoff or a selection over noncommuting projections with a positive pairing.

There are two genuine parallels, both paid standard tools rather than the bridge:

- JLW's Bessel/orthogonality step (4.5) mirrors the candidate's X_j = E[g_j sign A(g)]
  Bessel step.
- JLW's Steps II–III (Hermitian dilation, finite-rank approximation) mirror candidate §5
  (end) and §7.

**Bi-Lipschitz consequence.** JLW Corollary 6.1 gives the sharp-scaling inequality with
m ≈ sqrt(n) and constant 32. Putting that in place of MN Theorem 4.1 in the proof of MN
Theorem 1.12 gives torus distortion >= sqrt(n)/64. The third assertion of MN Lemma 6.12
places Z_{2m}^n with distortion 1+6ε inside a sup-grid of dimension O(n). Together these
give, by the reviewer's inference, N-point sup-grids with S_1 bi-Lipschitz distortion at
least c sqrt(log N / log log N). GMN §1.3 states that these proofs need only the sharp
inequality, and JLW say closing the gap is what is needed to apply them. JLW do not
themselves state the grid corollary. This exceeds T117Q's bi-Lipschitz corollary
c sqrt(log n)/(log log n)^(9/2) for general metrics. Hence R2-C.

## RQ2 and RQ4

Both are addressed at response level.

- The response uses "new to this project, with no antecedent found in a bounded search".
  It disclaims "first", the Heisenberg question and Escudero Gutiérrez–Muguruza Question 2.
- It states that the 9/2 exponent and chart count were selected by the method before the
  freeze.
- It states that the diagonal l_1 consequence has exponent 9/2, weaker than source117's 3,
  and does not supersede the source.

I re-checked the diagonal argument. Finite subsets of L_1 embed isometrically into l_1^K,
and the diagonal copy of l_1^K in S_1 is isometric. So the theorem implies the L_1
statement with the same exponent, and nothing more.

## Does SUBSTANTIAL survive?

Yes, on operation-level grounds. The unpaid step remains candidate §3: a dimension-free
spectral selection among noncommuting chart projections, using a positive Gaussian dual
pairing and a scalar-moment design that makes (2.1) uniform in matrix dimension. It is
what supplies the sqrt(m) Gaussian cancellation that S_1, having no nontrivial type,
otherwise lacks. Every added antecedent was checked at the level of operations:

- CEE+LWW: logarithmic influence gain, symmetric between L_1 and S_1, with no supplied
  family.
- JLW sharp cotype: wrong quantity, and lower-bound type.
- JLW smoothing: an l_2 gradient with a sqrt(m) conversion loss.
- NPS Theorem 12: the S_q transfer loses the gain.
- KNT and quantum expansion: as in round 1.

None of them performs or replaces this step. For calibration only (not novelty
evidence): JLW is itself a recent L_1-to-S_1 transfer that replaces a cut-based step by a
new matrix operation, which is the same kind of contribution.

Caveats carried forward:

- The bridge is short, and is built from standard operator tools.
- The exponent is method-shaped.
- The literature search is bounded (reading-and-search-limits.md).

An expert reader could still locate an antecedent for Lemma 2 in operator-space or
noncommutative-Khintchine literature I did not read (Lust-Piquard–Pisier duality,
Haagerup–Pisier; not read).

## Required objections (manuscript must implement; response-level text alone is insufficient)

- **R2-A (RQ1, CEE+LWW).**
  - State the corrected reading: the proof of CEE Theorem 13 bounds the pushforward pair
    average for 1-Lipschitz maps.
  - Do NOT repeat round 1's "O(log log N)" cap. Give the cap
    2 tau^-1 max_i log(e + 1/sigma_i), or an equivalent.
  - Note that the route has the same constants for L_1 (CEE Theorem 42) and S_1 (LWW).
  - Explain that on the source family the needed gain is polynomial (Gaussian cancellation),
    while the route gives at most an influence-logarithmic gain, and that no negative-type,
    uniformizable, small-influence quotient family is supplied.
- **R2-B (RQ3, cotype and smoothing).** Replace the response's "would require a new
  compatibility argument" with an operation-level reason, for example:
  - (3.1) is an upper Gaussian-average bound, which cotype cannot give.
  - JLW smoothing yields an l_2 gradient, which in S_1 converts to a Gaussian average only
    with up to a sqrt(m) loss (diagonal example).
  - Using the cotype inequality for uniform pair averages needs a torus map whose
    antipodal-coordinate pair law dominates the uniform pair law of a negative-type family,
    and none is supplied.
  - Keep the parent's caveat that this is not an impossibility theorem.
- **R2-C (RQ2/RQ3, bi-Lipschitz corollary).**
  - Any statement of the bi-Lipschitz consequence must say that, for general N-point
    metrics, sharp scaling (JLW Corollary 6.1) with the MN Theorem 1.12 argument and MN
    Lemma 6.12 gives sup-grids with S_1 distortion at least c sqrt(log N/log log N). That is
    stronger than T117Q's bi-Lipschitz corollary.
  - Any novelty of the bi-Lipschitz consequence may be claimed, if at all, only within
    negative-type metrics, and only under the bounded-search wording.
  - The manuscript must either verify this grid inference itself or attribute it as a
    consequence of the cited statements.
- **R2-D (implementation).** Implement in the manuscript itself, not only in the response:
  - the response's RQ1 to RQ4 statements;
  - round-1 KNT point 3 and quantum-expansion point 6;
  - the RQ4 statement that the exponent is method-shaped and that the l_1 consequence is
    weaker than the source;
  - full credit to JLW 2610.21445v1 (posted 2026-10-15, three days before the candidate)
    as the sharp S_1 cotype antecedent.

## Optional editorial improvements

- **E1.** Strengthen or replace the six-point remark. A sup-grid [m]^n with
  m >= C log n contains, by the Fréchet map, an isometric copy of an n-vertex
  bounded-degree expander (independent_checks.py illustrates the Fréchet isometry on the
  Petersen graph). By Linial–London–Rabinovich and Arora–Lee–Naor (stipulated standard
  theorems, not read here), any negative-type metric on such a grid is at distance
  ≳ sqrt(log n)/log log n from d_inf. This shows that grids are not even boundedly
  equivalent to negative-type metrics.
- **E2.** Credit JLW (4.5) and Steps II–III as parallel standard devices for the Bessel,
  dilation and compression steps.
- **E3.** Optionally record the NPS Theorem 12 non-reduction remark from RQ1.
- **E4.** Round-1 editorial items E1–E5 remain optional.

## Diagnostics (not proof dependencies)

- independent_checks.py, run with /tmp/agvenv/bin/python (Python 3.14.7, NumPy 2.5.3
  available but unused), exit 0. Its output is independent-checks.json. It contains:
  - the six-point form;
  - the closed-form grid average for k <= 200, plus five full-grid cases;
  - the Petersen Fréchet isometry;
  - floating samples of the psi^-1 inequality (proved above);
  - the diagonal type-gap numbers.
- These finite checks do not bear on the arbitrary-dimension or all-size theorem.

## Package

- Members: review.md, reading-and-search-limits.md, replay-record.json,
  independent_checks.py, independent-checks.json, verify_review.py, review_controls.py,
  controls-result.json, .gitignore, and the Git-ignored private/ directory (one retrieved
  third-party body, pdf and txt).
- All of them are sealed, private files included, by MANIFEST.json with exact full
  inventory. Never stage or release private/.
- Verify with `python3 verify_review.py verify <dir> --anchor <SHA256 of MANIFEST.json>`,
  taking the anchor from the parent record, never from this package.
- controls-result.json records review_controls.py run on /var/tmp copies of the pre-final
  seal. The final seal adds only that file. Final positive, wrong-anchor and copied
  controls are reported outside the package.
