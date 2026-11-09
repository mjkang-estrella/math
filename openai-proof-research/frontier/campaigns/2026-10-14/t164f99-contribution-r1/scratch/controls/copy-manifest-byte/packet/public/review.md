# T164F99 contribution review, round 1 (conditional on correctness)

Reviewer: Factory Droid / claude-opus-5-5 / high. Independent SUBSTANTIAL-CONTRIBUTION
review of the frozen r99 author proof (family 164, fields of arbitrary characteristic).
This review assigns a contribution verdict only. It is not a correctness gate, assigns no
acceptance and no count, and claims no worldwide priority.

## 1. Candidate and scope reviewed (entire frozen scope, unchanged)

Immutable author root `frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r99/`,
frozen scope `packet/public/scope-freeze.md`
SHA-256 `2a39e2a3410a79812e3e48478fa892d507e163fcd739fd409173219c7c5a23b7`
(byte-identical sealed copy and original verified), proof
SHA-256 `14d9cd60f44d0bbb8867159b013e7e3026b09cc73208cdce8d3f628dc7175847`.

**Theorem F.** For EVERY infinite field K of any characteristic, every r, n >= 1 and
every chi: K^x -> [r], there exist pairwise distinct nonzero x_1,...,x_n with every
nonempty subset sum FS_J != 0 and chi constant on the union of all nonempty subset
sums and all nonempty subset products.

**Corollary G.** For every prime p and r, n >= 1 there is d >= 1 such that the
conclusion of Theorem F holds in F_{p^m} for every positive m divisible by d.

Both parts are assessed. Nothing is dropped: distinctness, nonvanishing of sums,
small and fixed characteristic, uncountable K, and Corollary G's exact
divisibility-only scope (no bounds, no all-large-m, no density/IP/read-once
strengthening) are all retained.

## 2. Verdict

**TECHNICAL** (conditional on correctness), for the entire frozen scope.

The complete proof is a transport of Alweiss's rational-field argument
(arXiv:2307.08901v6, Sections 3-5) in which every genuinely characteristic-zero
device is replaced by a strictly stronger published input or by a classical
compactness device that the pinned source itself already uses in a harder setting.
After the strongest known reduction (Section 4), the remaining operation is careful
but routine bookkeeping; there is no identifiable nonroutine operation. The
statement itself (FS union FP partition regularity with distinctness and
nonvanishing, in fixed small positive characteristic, plus the divisibility
corollary for finite fields) was found in no prior source within the bounded
searches recorded in `reading-limits.md`; that is project-level novelty at minimum,
but under the unchanged campaign criteria a new statement obtained by routine
transport and classical/source composition does not count as substantial.

## 3. What the strongest prior methods actually say (body reads, not titles)

- **Alweiss, arXiv:2307.08901v6 (read in full).** Theorem 1.3 proves the FS union
  FP pattern over Q (nonzero variables; distinctness not required). The proof
  (Proposition 4.1, Sections 3-4) is an update algorithm using only (i) field
  algebra: shifts x_n <- x_n + u . x^S/x^T and compensating scalings
  x_j <- k^{2^j} x_j, x_n <- k^{-s_T} x_n, requiring division, hence a field, any
  characteristic; (ii) multidimensional polynomial van der Waerden for monomials
  (Theorem 2.4), stated over Q via integer polynomial vdW plus scaling; (iii) the
  size function s(a/b) = max(|a|,|b|) to keep coefficients, shifts u and dilation
  k inside finite sets independent of the variables ("u and n bounded by a function
  of the number of colors", line 164, "by compactness"); (iv) Section 5 Steps II-IV
  (Ramsey by cardinality, Folkman, block/pivot construction), which are
  characteristic-free combinatorics. The introduction (lines 89-92) asserts that
  "by a standard compactness argument (see [8]), the partition regularity of a
  polynomial pattern over arbitrary fields follows from its partition regularity
  over Q". The cited argument does not prove that; see Section 6.
- **Bergelson-Leibman, Annals 150 (1999), arXiv:math/9907201v1** (Sections
  7.9-7.15 and 8.7-8.8 read; PHJ proof not read, per author and reviewer alike).
  Corollary 7.11: for ANY infinite ring G, any polynomial mapping P: G^n -> G^t
  over G with P(0) = 0 and any finite configuration F, every finite coloring of
  G^t admits h and nonzero x with h + P(xF) monochromatic. No characteristic
  restriction. Section 8.7 notes conventional polynomial maps over a ring are
  polynomial mappings. The author's instance (P(w_0,w)_e = w_e w_0^{d_e - 1},
  F = {(1, l) : l in L^E}) is a monomial special case. Corollary 7.12 even adds
  one-to-oneness on F over integral domains; Proposition 7.13 is a finitary
  version over all sufficiently large integral domains. The characteristic-free
  recurrence the author needs was therefore published, in greater generality than
  needed, in 1999.
- **Hunter, arXiv:2308.10749v1** (introduction and Remark 1.1, Lemma 6.1 sketch
  region read). Remark 1.1: distinctness is obtained for free by refining the
  coloring so that C(q) != C(2q). The finiteness step in the Lemma 6.1 sketch
  ("D is finite (since N subset Z has characteristic zero)") is a convenience, not
  an essential characteristic-zero input: for finitely many nonconstant
  polynomials p and a finite target set S, {d : x + p(d) in S} is finite in any
  infinite field because each p(d) = s has finitely many roots.
- **Bowen-Sabok, arXiv:2210.12290v1** (introduction, Claim 4.1 region, Section
  4.3 read). Corollary 1.2 transfers their {x, y, xy, x+y} theorem from Q only to
  characteristic zero and characteristic greater than some p0(n), by first-order
  compactness over the theory of fields. The actual written compactness argument
  cannot reach fixed small characteristic. Their Section 4.1 also uses Moreira's
  theorem "in the general form that holds for any field".
- **Moreira, Annals 185 (2017), arXiv:1605.01469v1** (Sections 1.2 and 7 read).
  Section 7 extends the {x, x+y, xy}-type theorem (Theorem 7.5) to every large
  ideal domain, hence to ALL fields of ANY characteristic and to F_q[x], and
  states explicitly: "The only new ingredient needed to run the proof ... is a
  suitable version of the polynomial van der Waerden theorem; such a version
  follows from [Bergelson-Leibman 1999, Proposition 7.5]." This is a published
  precedent for exactly the operation the author performs: take a
  vdW-recurrence-driven sum-product proof and make it characteristic-free by
  substituting the general Bergelson-Leibman ring recurrence. Bergelson-Moreira
  (arXiv:1307.6242v3, 1509.07574v1; abstracts/introductions read) established
  {x, x+y, xy} over every infinite field by affine ergodic methods.
- **Pinned source 164** (`preprints/Monochromatic-finite-sums-and-products-in-
  the-positive-integers-September-23-2026/` at pin fd4aeeb2..., blobs verified
  against the pinned tree): Theorem thm:main over N with separation; Sections
  03-08 build the nilsequence Prediction/Alignment machinery for the INTEGER
  problem and do not transfer to characteristic p. But two ingredients the author
  re-derives are already in the source in stronger form:
  (a) `02_framework.tex` `lem:chain-selection` is Alweiss's Section 5 Steps II-IV
      selection, characteristic-free;
  (b) `08_alignment.tex`, `lem:finite-word-plan`, is Alweiss's compensating-scale
      mechanism (equation alignment-scale-update is the author's Upd map,
      k^{p_l} on earlier coordinates and k^{-p_{T_0}} on the pivot, with
      lambda_e > 0) run with FINITE RATIONAL SCALE LISTS chosen BACKWARD and
      word-requirement budgets protecting earlier targets, in a strictly harder
      nilpotent noncommuting setting; and the paragraph after the recurrence
      statement performs exactly the author's Lemma 3 uniformity step: "On the
      compact space of its colorings with a fixed finite palette, each successful
      pair defines an open cylinder set. The preceding recurrence statement shows
      that these cylinders cover the space. A finite subcover gives finitely many
      pairs... The finite alternatives depend ... on no numerical values assigned
      to the generators."
- **Characteristic-p / finite-field antecedents** (scopes checked): Green-Sanders
  (four-term {x,y,x+y,xy}, sufficiently large prime fields, quantitative);
  Shkredov/Cilleruelo (density analogues); Kousek arXiv:2407.03304v1 (countable
  fields char-0 density patterns; finite-field {x, p(x)+y, xy} for large enough
  characteristic relative to degree; its sentence that Bowen-Sabok "solved the
  analogue of this question for all finite fields" overstates the actual
  Bowen-Sabok Corollary 1.2); Ackelsberg-Bergelson arXiv:2303.00100v4
  (Furstenberg-Sarkozy-type density results and equation partition regularity in
  finite fields, not coloring FS union FP patterns). None states Theorem F or
  Corollary G.

## 4. Strongest integrated known reduction, and the exact remaining operation

Strongest reduction, assembled entirely from published/source ingredients:

1. Reduce to countable K (author Lemma 1: subfield generated by a countably
   infinite subset; elementary).
2. Recurrence: Bergelson-Leibman Corollary 7.11 over the infinite ring K with
   the monomial map and configuration above (author Lemma 3, first paragraph).
   This replaces Alweiss's Theorem 2.4 outright; it is a strictly stronger,
   characteristic-free, published theorem, and the required instance is a
   monomial special case with P one-to-one checkable.
3. Uniform finite choice sets Phi(E, d, L, R): Tychonoff compactness of
   [R]^{K^E}, open cylinders, finite subcover (author Lemma 3, second
   paragraph). This is the classical compactness move, and it is already
   written out in the pinned source's Section 8 for a harder nilpotent
   recurrence; it replaces both Alweiss's height bounds and Hunter's
   characteristic-zero finiteness remark (which is itself replaceable by the
   polynomial-root argument of Section 3).
4. Update identities and backward budgets (author Lemmas 4-6, Proposition 7):
   the exponent vectors 2^j, s_J, sigma_e >= 2 are integer data; the map
   Upd_{U,u,k} and the preservation budgets Lambda^sharp, L^sharp are a
   coordinate-free re-derivation of Alweiss's Proposition 4.1 proof with finite
   sets in place of s(.) <= M, and a strictly simpler special case of the pinned
   source's `lem:finite-word-plan` backward recursion (abelian, no words, no
   palettes beyond product colorings). The author's random-evaluation identity
   check is corroboration, not part of the proof.
5. Selection (author Section 5, Steps 3-5): finite Ramsey by cardinality and
   Folkman, then the block/pivot construction; identical in content to Alweiss
   Section 5 Steps II-IV and the source's `lem:chain-selection`;
   characteristic-free as written there.
6. Nondegeneracy (author Step 0 and Step 6): isolate 0 as its own color (so
   subset sums are nonzero and, in characteristic 2, X + X = 0 forbids equal
   outputs); in other characteristics a 3-coloring psi of the doubling orbits of
   the fixed-point-free permutation z |-> 2z of K^x gives psi(2z) != psi(z),
   which is Hunter's Remark 1.1 device with an elementary orbit parity/3-coloring.
   Both decorations are routine.
7. Corollary G: Konig-style compactness along the tower F_{p^{j!}} inside the
   algebraic closure of F_p; a textbook limiting argument from Theorem F,
   assessed at its exact divisibility-only scope.

Every actual compatibility operation needed to make the simultaneous
stabilization/selection mechanism transport has been enumerated above (the
brief's central question). Each is one of: direct substitution of a strictly
stronger published theorem; a compactness argument already instantiated in the
operative pinned source; or characteristic-free combinatorics already present in
Alweiss Section 5 / the source Section 2. The remaining operation after this
reduction is the careful, correct-looking bookkeeping of the transport
(finite-set budgets propagated through 2^{n-1} tails), which the author executed
and documented, but which requires no new idea beyond recognizing that the two
inputs are characteristic-free. That is precisely "routine transport" and
"classical/source composition" in the unchanged campaign criteria.

## 5. Why not REDISCOVERED

REDISCOVERED requires an actual prior statement. Within the bounded searches of
`reading-limits.md`, no prior statement of Theorem F or Corollary G was found:

- Alweiss v6's sentence "partition regularity ... over arbitrary fields follows
  from ... over Q" cites the Bowen-Sabok compactness argument, which as written
  (their Section 4.3) proves only characteristic 0 and characteristic > p0.
  The sentence does not state the FS union FP pattern over small positive
  characteristic, does not include distinctness or nonvanishing, and its cited
  justification does not cover those cases. An overgenerality remark with an
  insufficient cited proof is not an actual prior statement of the candidate.
- Bergelson-Moreira and Moreira cover {x, x+y, xy}-type patterns (two-variable,
  one product and one sum) over all infinite fields, not FS union FP for
  arbitrary n; Green-Sanders/Shkredov/Cilleruelo/Kousek/Ackelsberg-Bergelson
  cover large-characteristic or density variants of two-variable patterns.
- The pinned source proves the theorem over N (hence every ring containing N,
  i.e. characteristic 0) and its companions stay in characteristic 0.

So the fixed-small-characteristic case appears genuinely unaddressed in the
literature seen; this is asserted only within the recorded bounded searches, with
no worldwide-exhaustive or priority claim.

## 6. Why not SUBSTANTIAL

Under the unchanged criteria, substantiality requires an identifiable nonroutine
operation after the strongest known reduction. Here:

- The one input that must change (recurrence) has a published, strictly stronger,
  characteristic-free replacement (BL Corollary 7.11), and substituting BL's
  general-ring recurrence to characteristic-free a vdW-driven sum-product proof
  is already published practice (Moreira Theorem 7.5, "the only new ingredient").
- The one device that must be re-engineered (finite budgets replacing heights)
  is already present in the operative pinned source in a strictly harder form
  (`lem:finite-word-plan`, with the same update map, backward requirement lists,
  and the same cylinder-set compactness for uniform finite alternatives).
- Distinctness and nonvanishing are Hunter's trick plus elementary orbit
  coloring and an isolated zero color.
- Corollary G is a standard compactness corollary at a deliberately modest
  scope.
- The history does not rescue nonroutineness: structural r130's judgment that
  positive characteristic "would need the whole nilsequence apparatus over
  function fields" was a screen conditional on the SOURCE's nilsequence route,
  not evidence that Alweiss's elementary route fails; the route taken here never
  touches nilsequences.

The result is a clean, well-documented, full-scope transport that settles cases
the published record leaves open (e.g. the algebraic closure of F_2), and the
author's own report says exactly this and assigns itself nothing. The statement
is new to this project and, within bounded search, apparently new to the
literature; the proof operation is nonetheless routine after BL 1999 and the
pinned source's own machinery. Verdict: TECHNICAL.

## 7. Why not UNRESOLVED

UNRESOLVED is for a genuinely unresolved contribution comparison. The comparison
here is resolvable: every component of the proof has an identified strongest
antecedent, and the gap left by the antecedents (fixed small characteristic) is
closed by substitution and compactness steps that are demonstrably standard, as
evidenced by the pinned source's Section 8 and Moreira's Section 7. Absence of a
worldwide-exhaustive novelty search does not make the contribution comparison
unresolved.

## 8. Scope honesty and non-claims

- Corollary G is assessed exactly as frozen: d | m only, no bound on d, nothing
  for F_{p^m} with m not divisible by d (e.g. F_{2^m}, m prime), no
  all-large-m statement. At that scope it is a routine corollary of Theorem F.
- Theorem F's characteristic-0 content is known (Alweiss over Q plus Hunter's
  distinctness remark, restriction to the prime field); the uniform proof is
  included in the transport and adds no separate operation there.
- T164F99 does not resolve the structural r35 full read-once positive-integer
  question (mixed164.md), which remains untouched.
- No correctness verdict is given or implied; this review is conditional on
  correctness. No acceptance, count, or priority is assigned.

## 9. Limits

See `reading-limits.md` for exact read extents, versions, access failures, the
bounded search record (2 reviewer web searches, 8 arXiv API queries, 3 OpenAlex
and 3 Semantic Scholar citation queries, plus the author's six recorded web
queries), and the deliberate corpus exclusions. Bergelson-Leibman-McCutcheon
(2005) was not obtained; MathSciNet/ZBMath were not accessible; Kousek's journal
version was not obtained. These bounds limit novelty assurance, not the
contribution comparison, which rests on body reads of the strongest actual
methods.
