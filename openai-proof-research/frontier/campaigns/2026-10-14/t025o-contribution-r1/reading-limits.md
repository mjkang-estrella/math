# T025O54 contribution review r1: exact reading and search limits

Original prose CC BY 4.0. Nothing third-party is copied here.

## Author packet (frozen, read in full)

scope-status.md, chronology.md, checkpoint.md, selection.md, candidate-proof.md, constrained-descent.md, alternative-route.md, contribution-comparison.md, reading-limits.md and verify.py were read in full. primary-identities.json and source025-receipts.json were read and checked. exact-checks.json and source-family-inventory.json were used only through the verifier and my own recomputation; I did not read them line by line. The parallel proof review and any other pending review directory were not opened.

## Source025 at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (stipulated true)

Read in full from the author packet's authenticated copies: introduction.tex (242 lines), main.tex, elementary.tex (170), divisors.tex (273, the whole file), residues.tex (408), random.tex (256), descent.tex (262), counting.tex (132), prescribed.tex (579). README.md was read. references.bib was only searched (Breusch, Stewart, odd, Elsholtz, Sierpiński, Chen); only Elsholtz2016 and ElsholtzPlanitzer2021 matched. unicode-mappings.tex and the PDF were not read. Source truth was not audited.

## Primary bodies retained by the author

* Elsholtz, arXiv:1606.02117v1 (elsholtz.txt): the whole retained text, lines 1–401, including Theorem 1.1, Lemmas 2.1–2.5, the proof, the parity discussion, Remark 2.6 and the references.
* Webb 1965 (webb.txt): lines 1–130 (introduction, Theorem 1 and its proof, Theorem 2 statement and the first part of its proof). Lines 131–290 were not read.
* Graham 1964 (graham-page14.png, graham-page15.png): printed pages 206–207 were read visually (end of the proof of the 1/2 assertion, concluding remarks (1)–(5), references). Earlier pages and the proof of the general criterion were not read.

## Not read (bodies)

Breusch 1954, Stewart 1954, Sierpiński 1956, van Albada–van Lint 1963, Chen–Elsholtz–Jiang 2012, Konyagin 2014, Vose 1985, Tenenbaum–Yokota 1990, Takenouchi 1921, Pihko 2001/2010, Louwsma–Martino 2023/2025, van Doorn–Tang 2026, and van Doorn–GPT-6 "Practical numbers and Egyptian fractions" 2026. Attributions to Breusch/Stewart of the odd-base remainder method rest only on the secondary annotation below.

## Bounded web navigation (2026-10-18)

Search queries (WebSearch):
1. "Egyptian fractions odd denominators number of terms log log b uniform bound every fraction a/b odd b"
2. "short Egyptian fractions with odd denominators length bound Erdős problem odd unit fractions a/b"
3. "erdosproblems.com Egyptian fractions odd denominators distinct number of terms N(a,b) loglog"
4. "\"odd\" Egyptian fraction expansion length O(log log b) OR \"sqrt(log b)\" distinct odd denominators every rational odd denominator few terms"

Pages opened: https://en.wikipedia.org/wiki/Egyptian_fraction (odd-greedy and odd-existence passages only); https://erdosproblems.ai/wiki/library/unit_fractions (library index summaries); https://erdosproblems.ai/wiki/library/divisors/doorn_2026_practical_numbers_egyptian_fractions (card only); https://ics.uci.edu/~eppstein/numth/egypt/refs.html (entries [Bre54] and [Ste54]; fetched to /var/tmp scratch, not retained). No result stated an odd-denominator uniform length bound of order log log b, or any uniform length bound for odd denominators. This is navigation, not a worldwide novelty certificate. Results after September 2026 are excluded only to the extent of these searches.

## Project history read

frontier/NEW-TEN-2026-10-14.md (acceptance section and the T025O54 entry), AGENTS.md, t025o-parent/{contribution-r1-brief.txt, intake.json, dispatch-r1.json}, i205-bounded-egyptian-parent-disposition.md (full), and grep hits in i205-bounded-egyptian-denominators.md and i204-arithmetic-structures-discovery.md. A repository-wide grep of non-private files for odd-denominator Egyptian language found no earlier T025O development. The t024w-contribution-r1 verifier was read as the helper template.

## What the finite checks do and do not show

diagnostics.py verifies three things by exact rational arithmetic on random small instances: the four terminal templates; the equivalence between the constrained residue condition and the shifted interval at modulus 2ℓu; and the entrywise ℓ-scaling of one residue step. These checks guard the bookkeeping claims in review.md §3–§4. They prove nothing asymptotic and give no proof verdict.
