# Analytic r129 report: PREFREEZE, no nominee

Author: Myeongjin Kang; no affiliation. Original prose CC BY 4.0; code MIT. Runner: Factory Droid, model Opus 5.5 (claude-opus-5-5), high. Pin `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. All pinned theorem statements and operative proof operations are stipulated true.

## Outcome

PREFREEZE. No scope was frozen, there is no nominee, and no author proof was written. This report assigns no correctness or contribution verdict, gate or count.

## Main finding: the r128 "open operation" is already paid

r128 isolated one gap: a per-potential sharp auxiliary (the Cohn–Kumar quantifier, explicitly unclaimed by source090 and by its atomic companion) for singular Epstein potentials t^{-p}, p > 1. It said this needed Gaussian pairs with f_alpha(0) <= C S(alpha) and a new boundary-layer sign certificate. Neither is needed.

- Source090 Proposition `prop:exact-interpolation` gives, for every k >= 2.36, unique coefficient lists with ||l_1||_1 + ||l_2||_1 < 5.
- Combined with the source's spectral bounds `eq:uniform-derivative-bounds`, this gives |H_1|, |H_2| < 540 on [0, infinity).
- Hence f_alpha(0) = k e^{-k} H_1(0) = O(alpha S(alpha)) for alpha >= 1. The extra factor alpha is harmless because S decays exponentially.

Uniqueness gives continuity in alpha, so no measurable selection is needed. Bernstein's theorem, the source duality lemma and Fubini/Tonelli then build a sharp auxiliary f_g for every completely monotone g with finite triangular-lattice energy, including all t^{-p}, p > 1. It is Cohn–Kumar admissible whenever g(t) = O(t^{-1-delta/2}).

Every step is a paid source operation or classical. This is hypothesis removal through a known reduction, which the brief's lesson classes as technical. So it is recorded as a resolved screen, not frozen or nominated. Details are in screens.md, Section 1.

## Second family

I screened source191 in higher dimensions (Heilbronn tetrahedra). A direct dense analogue of the source cap lemma fails by counting: |S| = O(q^2) against a required order of q^3. The no-size-cutoff alias search then found the existing frozen, unresolved arithmetic r56/r57 archive T191V56 on exactly this target. Its recorded gaps are the DE moment, lower-rank strata and the exceptional-normal loss. I had no work closing its entire scope, so I did not reopen it. Credit goes to arithmetic r56/r57 and structural r24. Details are in screens.md, Section 2.

## Screens

| Screen | Question | Strongest reduction | Disposition |
|---|---|---|---|
| S3 (r128 focus) | Per-potential CK sharp auxiliary, singular t^{-p}, p>1, and all completely monotone g with finite lattice energy | Source uniform list bound (<5) + spectral bounds + duality + Bernstein + Fubini | Closes at full scope by routine composition; not nominated |
| source090 adjacent | Periodic uniqueness, defects, Schwartz/unique auxiliary | r128 S2, I134/I137, Sardari as cited | Classical or old; not reopened |
| source191 | Power improvement for tetrahedra in [0,1]^3 | Source two-congruence design | Direct cap fails by counting; existing open archive T191V56; not reopened |

## Timing

Brief and required r128 files were read first. Then, in order: source090 sections 01–06 (resolution at Prop. `prop:exact-interpolation`), the atomic companion introduction and energy section, source191 introduction and lemma statements, my own cap-count calculation, and the alias searches. The r56/r57 and structural r24 history were read last, before sealing and before any freeze (none occurred). Nothing is backdated.

## Scope of writes

Only the owned root was written. There was no git, shared-index, publication, upload, contact, browser UI, nested-agent, formal or manuscript work. Upstream and history bodies are under packet/private under their original rights; the public files here are original.
