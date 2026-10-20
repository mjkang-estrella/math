# Reading limits and search disclosures (r134)

## Briefs and project rules (full)
AGENTS.md; expanded-target-2026-10-17/research-brief-2026-10-20.txt; expanded-target-2026-10-17/fresh-structural-r134-brief.txt;
sources/upstream.json; frontier/NEW-TEN-2026-10-14.md lines 1-60 only; sources/CONTENTS.md family titles plus
full entries for 162, 184, 248 and the screened families named in working-notes.md.

## T106O133 disposition (full)
discovery-structural-r133-parent/{assessment.md, intake.json, proof-r1-adoption.json, contribution-r1-adoption.json};
t106o133-contribution-r1/packet/public/{review.md, reading-limits.md}. The r133 proof.md and frozen-statement.md bodies
were not read: no mechanism overlap with the counting direction.

## Pinned source bodies (Git-blob authenticated; private copies under packet/private/source, receipts.json)
- Independence manuscript (family 184): introduction.tex, optimizer.tex, closure.tex read in full; coupling.tex lines
  270-319 (end of the triangle theorem proof and `eq:optimizer-triangle`); invariant.tex lines 1-45 (definition of the
  cross-mass bound and statement of `thm:weighted-triangles`); main.tex; references.bib entries for Davies2026, DMS2012,
  DKPS2020, DhawanLocallySparse2026, DJM2025. entropy.tex and the remainder of coupling.tex/invariant.tex were NOT read;
  the proof uses only the stated results (S1)-(S3), which are stipulated true under the pin.
- Correspondence-colouring companion: introduction read earlier in the round; adjustment/rounds/completion/triangles/
  history not read in full (not used).
- Family 192 (all nine TeX files fetched; introductions and observations read), 248 and 185 introductions, and about
  136 introduction/conclusion files of ~45 structural families (screen only; scratch/intro-paths.txt).

## Primary literature (private copies under packet/private/primary)
| file | version / URL | sha256 prefix | extent read |
|---|---|---|---|
| davies-2609.04654v1 | arXiv:2609.04654v1, https://arxiv.org/pdf/2609.04654v1 | 82940b92 | text lines 1-449 (Sections 1-2.2: Theorems 1-7, Lemma 8) |
| cdm-1310.6672v1 | arXiv:1310.6672v1 | a866ea9b | text lines 80-204 (Theorems 1-4, Remark 5); proofs not read |
| cooper-mubayi-indsetfinal | http://homepages.math.uic.edu/~mubayi/papers/indsetfinal.pdf (author final, Nov 2011) | 0d81eb88 | text lines 1-180 |
| fewest-2503.10002v1 | arXiv:2503.10002v1 | ae3aadcd | text lines 1-140 (introduction, Theorem 1 redux) |
| fhkl-1404.3396v3 | arXiv:1404.3396v3 | (see MANIFEST) | lines 600-720 (family 192 screen only) |

Not obtained or not read: DMS2012 (SIAM J. Discrete Math. 26), DKPS2020 body, Dhawan locally-sparse papers,
Davies-Dhawan-Gallardo-Methuku-Nguyen-Seo-Spiro (Davies ref. [11], local demands for K_r-free graphs), Shearer 1995,
Davies-Sandhu-Seo-Tan degree-sequence occupancy papers. A worldwide search for prior degree-sequence counting bounds for
K_r-free graphs was limited to two web searches; no priority claim is made.

## Project history
- First pass: keyword counts over authored files excluding 595 catalogue copies (scratch/catalogue-copies.txt), the
  active roots arithmetic r98 and analytic r132, and this root.
- Late widened alias search (local demand, degree-sequence version, local Shearer, Martinsson, AEKS, clique-free
  independence): found r114 packet/public/screen-184.md (read in full), r121 (repeat, not read), r124/r125
  packing-feasibility and reading-limits (grep lines only), I22 combinatorial discovery (grep lines only). None treats
  counting independent sets or degree-sequence bounds; this was established before freezing.
- After freezing (late, disclosed): a counting-alias search ("number of independent sets", "counting independent sets",
  "independence polynomial", "hard-core model", "i(G) >=") over authored history with the same exclusions, also excluding
  copied primary/upstream/source directories and venvs. Matching lines were inspected: r50 analytic (exact hard-core
  model in a different, analytic target), r133 (an unrelated "i(G) >=" pattern in the odd-cycle packet), and pinned-copy
  history.tex lines on local occupancy. No overlap with the frozen claim was found.
- Hidden/ignored files were included (rg --hidden --no-ignore); venv files appeared as noise and were excluded later.

## Isolation
One temporary file /tmp/r134_titles.txt was written and removed early in the round (outside the root). The harness stores
command output under /tmp/droid-terminal-*. No other writes outside the root. No nested agents.
