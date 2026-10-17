# Contracts, provenance and actual reading extent

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

All ten downloaded pinned text blobs match the complete
`sources/preprints-tree.json` Git identities. Exact paths, raw URLs,
sizes, Git SHA1 blobs and SHA256 values are in `source-receipt.json`.
The revision is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` throughout.
Upstream truth is stipulated; this work does not audit upstream validity.

## Mathematical inputs actually read

Family231 has one manuscript in the catalogue. Its `paper.tex` imports
six section files, all present locally. Read the complete introduction,
decoder, implementation and strongly-Rayleigh sections. In `response.tex`
read the finite-tilt definition, finite-response and limsup-drift
interfaces; in `observation.tex` read the posterior lemma and its full
proof and the innovation statement/proof setup. The proof of the
Brownian sampling proposition, including its use of these observations,
was read completely. The forest determinant proof is not a new
dependency of CS and was not independently audited. Bibliography entries
were used to locate the cited primary bodies and family236 companion.

The load-bearing source labels are `lem:sr-response` (all finite tilted
strongly Rayleigh laws, uniform 1/2 bound), `lem:inverse` (every path
input, arbitrary countable set), `prop:brownian-sampler` (finite sets
exhaust the ENTIRE index set), and the scalar Brownian converter inside
`lem:edge-noise`. CS preserves the entire-exhaustion assumption by
applying the proposition on each independent covariance component.

Read the actual family236 introduction/main theorem and its observation
motivation: only regular-tree free Ising laws in its specified sharp
range are asserted. This is a scope/duplication comparison, not a
mathematical premise or a complete reading of that companion's proofs.

Read family098 main theorem, set construction/doubling proof, and the
entire compact Banach-space corollary proof. Its derivative-energy
argument was not independently audited. It was screened and rejected
before a target freeze; it is not a premise of CS.

## Closest primary literature

* Borcea–Brändén–Liggett, arXiv:0707.2340v2, PDF in `private/bbl.pdf`:
  Definition 2.13; Proposition 3.1(3), Proposition 3.5 and proof;
  Theorems 4.8–4.9 and their proof discussion. Theorem 4.9 supplies NA;
  Proposition 3.5 supplies determinantal strong Rayleighness. Closure
  under stable limits supplies the optional closedness assertion for
  SR(I). Other sections are not claimed read in full.
* Alishahi–Barzegar–Zamani, arXiv:2203.03935v2, PDF in `private/tail.pdf`:
  introduction and complete sections 2.1–2.2, including the full proofs
  of Proposition 2.2, Lemma 2.5 and Theorem 1.1. This already contains
  the four-sign indicator covariance inequality and summable rows.
  Those facts and the zero-cross-covariance independence consequence
  are fully credited. Gaussian threshold sections are not used.
* Lyons–Thom, arXiv:1402.0969v2, PDF in `private/lyons-thom.pdf`:
  section 7 from the relatively independent joining construction through
  Lemmas 7.2, 7.8, 7.9 and their proofs, Corollary 7.4, Questions
  7.5–7.7, and proof of Theorem 7.3 by Kaplansky density. Their coupling
  and spectral approximation operations are distinguished from CS;
  their earlier sofic coupling theorem is not a premise here.
* Seo, arXiv:1105.2529v1, PDF in `private/seo.pdf`: introduction,
  Theorem 3.1, Proposition 3.2, the proof outline and Lemma 3.4 proof
  through its first large-scale case. This only supports rejecting an
  unsubstantiated novelty claim for the 098 thickening screen.
* Björn–Björn–Shanmugalingam, arXiv:2008.00588, PDF/text in
  `private/filling.*`: retrieved as a possible 098 comparison. Only
  the web-exposed construction/theorem overview was inspected; its
  proof body was NOT read and is NOT a premise or novelty verdict.

All primary PDFs and extracted text remain private third-party material.
The search was bounded, and no absence-of-hit priority claim is made.

## History and eligibility limits

The parent assignment, actual AGENTS.md, upstream pin, complete catalogue
paths, next-discovery brief and inherited r15/r17 exclusion passages were
consulted. Current and old ledger entries were screened at their exact
titles and family-specific body hits. The historical brief files are
large nested records; unrelated appended proof audits were not all read
line by line. This is not claimed as a complete audit of all old work.

In addition to the searches described in screening-before-freeze.md,
searched every current-campaign `candidate.md` and `analysis.md` outside
input/private trees for family231, strongly Rayleigh, FUSF, covariance
components and Lyons–Thom. The only resulting candidate hits were this
round itself. Root iteration-body hits identified I77 as a finite
matroid-sampling comparison, not an infinite-law coding project. Existing
SR-related citations do not by themselves establish a developed target.

The independent reviewer should check this bounded eligibility finding;
it is not replaced by an absence of an accepted title. The original full
history paths supplied by the parent remain authoritative and have not
been edited or copied wholesale.

## Validation boundary

`check_controls.py` verifies 90 exact permutation/threshold-ball identities,
a determinantal example with zero unconditional pair covariance but
nonzero conditional covariance inside one component, and the non-NA
even-parity countercontrol. These detect misuse of pairwise independence
or threshold boundaries. They do not implement Brownian sampling, prove
the all-law theorem, or establish contribution. The general proof is in
candidate.md; independent gates remain pending.
