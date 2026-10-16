# Source contracts and actual reading extent

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.
Third-party copies in inputs/private retain their rights and stay private.

The authoritative corpus pin is openai/math
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. The complete preprints subtree is
df0564b2deaab87e07854b6344d8c2f037682e77, with truncated=false.
retrievals.json lists every retained text blob separately: exact preprints
path, immutable raw GitHub URL, Git blob SHA1, SHA256 and byte size.
Every retrieval was matched to the complete preprint tree before storage.
The verifier repeats that authentication. No third-party code was run.

Semantic reading is narrower than retrieval. All unmentioned retained
sections, bibliography bodies and figure sources are retrieval-only.

* **Parabolic intersections in Artin groups**, family 254: introduction's
  group definition, thm:main, cor:arbitrary-intersections, cor:membership
  and construction overview; category section's frame/label/algebra,
  cat:classical, cat:cartan, cat:frobenius, elementary twists,
  cat:action and cat:family with their displayed proofs. The unfolding
  proof was inspected as background, not used for a new assertion.
  Layer section's definitions, lay:structure and adjacent-layer
  statements/proofs, positive and inverse amplitude, exterior invariance,
  label compatibility, top-divisor and reduced-word interfaces/proofs were
  read. Caps section: cap:hull and proof, two:uniqueness statement and
  its final proof; intervening right-simple tensor estimates were only
  searched, not fully read. Null section read in full, including
  null:hom, null:injection, null:separation, null:obstruction and proofs.
  Height section and stabilizer section read in full. Spherical section:
  introductory contract, path-bound setup and ending, and cochain-drop
  through sph:containment proofs; the entire interior path-projection
  induction is not claimed as a fresh complete reading. No implementation
  or upstream theorem audit is claimed.
* **Harmonic heights and the Artin K(pi,1) conjecture**, same family:
  complete introduction and consequences.tex; topology section's first
  6000 characters for its precise complex, parabolic embedding and
  finite-type monoid conventions. thm:main and cor:artin-structural are
  dependencies. No full asphericity proof body was read or re-proved.
* **An Artin group with no geometric CAT(0) action**, same family:
  complete introduction, including thm:main, definition of geometric
  action and obstruction outline. Later proof bodies were retained but
  not read. Used only for the companion/interface screen.
* **Tensor saturation for even spin groups**, family 204: complete
  introduction, particularly thm:main's three-weight/root-lattice
  quantifiers and outline. No tensor schedule proof was relied upon.
* **Sixth symmetric power**, family 210: complete introduction. No
  certificate code was executed or relied upon. This is a rejected
  selection, not a mathematical dependency of R.
* **Quadratic stabilization**, same family: complete paper.tex body,
  including thm:main, annihilator criterion, lem:shift, all four steps
  of prop:vanishing and cor:comparison. Included references.tex was not
  separately read in full. Existing Foulkes literature records I198,
  I199, I202 and I206 were read completely to reject overlap. Their
  archived mathematical/checking code was not executed, and their
  original reports were not re-audited or used as proof premises.
* **Rational homology and Quillen's conjecture**, family 310: complete
  introduction. Its existing all-field consequence was screened out.
  Later retained proof sections were not read.

Primary literature actually inspected:

1. Cumplido--Martin--Vaskou, *Parabolic subgroups of large-type Artin
   groups*, published Cambridge HTML, [DOI 10.1017/S0305004122000342](https://doi.org/10.1017/S0305004122000342).
   Section 6: definition of closure, Lemma 36, Proposition 37, Lemma 38,
   full proof of Proposition 37 and Corollary 39. Earlier sections were
   searched for the geometry interface but not read in full. The full
   HTML reading copy is bound by literature-retrievals.json; presence of
   its bytes does not imply a full article reading. No page graphics were
   used as evidence.
2. Hagen--Martin--Sartori, *Combination theorems for Wise's power
   alternative*, [arXiv:2503.20620v1](https://arxiv.org/html/2503.20620v1).
   Section 5.1, Definition 5.9, Theorem 5.10, Lemma 5.11 and its proof,
   plus the cited reference [38]. The theorem credits Godelle's
   Corollary 3.8 for two-dimensional root closure. Godelle's publisher
   page/introduction was also inspected, but missing formulas and the
   absence of a complete original-proof reading prevent any claim to
   have independently reconstructed that result here. HMS normalizer
   and visual-splitting hypotheses were also checked at their statements.
3. Garnier--Heng--Licata--Yacobi, *Normalisers of parabolic subgroups of
   Artin--Tits groups and Tits cone intersections*,
   [author-hosted PDF](https://ogarnier.github.io/pub/norm_artin_tits_cone.pdf).
   PDF textual extraction pages 1--4 and Section 2.3 / Lemma 2.8: exact
   definitions, Theorems 1.3/1.4/1.8 and Conjecture 1.10. Theorem 1.8's
   ambient spherical hypothesis was decisive. The full later proof was
   not read; no page-image/layout audit or version/priority claim is made.
   Both original PDF and pdftotext -layout extraction are retained.

The first two primary files were retrieved by exact listed URLs; the
third URL may evolve, so its recorded SHA256 bytes control this reading.
Two guessed arXiv HTML URLs (2210.06369v3 and 2012.02693v3) returned 404;
neither is treated as a read source or a theorem dependency.

Read in full for continuity: applicable AGENTS.md; sources/upstream.json;
current campaign ledger; mandatory 119315-character historical brief
(supplied SHA256 matched); r10 candidate; relative-CI-r2 candidate; both
relative-CI parent dispositions; the specified F corrections/disposition
and G proof/contribution parent dispositions; r4/r6 selection records.
Historical directory permissions are superseded. No archived code was
executed. external-inputs.json records exact read-only references and
the entire two frozen continuity trees. The live ledger and catalogue
metadata have private snapshots to avoid dependence on later parent edits.

The working checkout HEAD was a1e51ac1ea8c90395bad1265dd138824e5bc5d71
when inspected; this is a project identity, not the upstream mathematical
pin. The pre-existing modification to frontier/iterations/i31-nonconical-no-mcm.md
was left untouched. Git inspection used rev-parse and status; no staging,
commit or intentional index mutation was performed. No index-identity audit
is claimed.
