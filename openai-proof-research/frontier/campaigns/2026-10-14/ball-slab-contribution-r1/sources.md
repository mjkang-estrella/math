# Ball–slab second-order contribution review: sources and access

2026-10-14. Companion to `review.md`. Frozen input hashes are in `input-hashes.json`. Output hashes are in `outputs.json`. Pinned mathematical truth is stipulated at commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` and is not audited. This review does not certify the candidate proof, does not accept it, and does not change a count. A bounded negative search is not a novelty certificate.

## Candidate and internal record

| Item | What was read | Role |
|---|---|---|
| `frontier/campaigns/2026-10-14/ball-slab-second-order/candidate.md`, SHA-256 `30bb73d2601754dcc6aa9eb26537e083256849acd3b5cf94a710970dfe067e54`, 24763 bytes | complete | proposed statements (A)–(D) and §§1–8 |
| same directory, `README.md`, `literature.md`, `reading-and-failures.md`, `provenance.json`, `remote-authentication.json` | complete | scope, author reading limits, recorded remote hashes |
| same directory, `checks.py` and `checks.json` | inspected; `checks.py` was not rerun | exact rational identities supporting the kernel difference and the Taylor expansion of \(g\); not used as a proof |
| `frontier/findings/R018-ball-slab-logarithmic-contact.md` | complete | credited fixed-radius leading law |
| `frontier/iterations/i275-logarithmic-contact-full-proof.md` | complete | credited mechanism: charts, cutoff, annulus, drift |
| `frontier/reviews/i277-logarithmic-contact-proof.md` | complete | PASS record for the fixed-radius leading law; not a contribution decision |
| `frontier/reviews/i278-logarithmic-contact-contribution.md` | complete | SUBSTANTIAL record for the first all-BV log passage |
| `frontier/iterations/i346-ball-slab-crossover-research.md` | complete | moving-radius statement and exact \(g(R)\) |
| `frontier/experiments/i346_ball_slab_crossover_research/analysis.md` | complete | author’s own TECHNICAL assessment of I346 |
| `frontier/experiments/i346_ball_slab_crossover_research/reading-and-failures.md` | complete | I346 reading record |
| `frontier/sources/i346_ball_slab_crossover_research/literature.md` | complete | prior literature note; LGL was abstract-only there |
| `frontier/iterations/i283-ball-slab-endpoint-obstruction.md` | complete | fixed-radius substitution fails at the endpoint |
| `AGENTS.md`, `sources/upstream.json` | complete | pin and agent rules |
| `frontier/reviews/i272-global-fixed-profile-contribution.md` | complete | calibration of a TECHNICAL verdict |
| `frontier/reviews/i64-entropy-coefficient-extraction-novelty.md` | complete | calibration of a SUBSTANTIAL verdict |

`frontier/experiments` reconstruction text behind the I277 PASS was not re-read. I275 was read as the credited mechanism. Its validity was not re-audited. I346’s TECHNICAL label is the author’s research assessment. This review does not reopen that assessment and does not treat it as an independent gate.

## Retained primary pages

- `frontier/sources/i277_logarithmic_contact_proof/afm-2013-page-7.txt`, SHA-256 `c1419d76fc08ed7e94fc4bb9d98657c66afee123f0a8050f4ab2099163cc7d73`, 3553 bytes. Read complete. Acerbi–Fusco–Morini Definition 2.5, the \(\omega r^N\) comparison.
- `frontier/sources/i277_logarithmic_contact_proof/afm-2013-page-22.txt`, SHA-256 `50ae9faa12dffe367fc5845718ae85262458f26af151ad6baea4bbfc00ca1382`, 3405 bytes. Read complete. Theorem 4.2: \(\omega\)-minimizers converging in \(L^1\) to a \(C^2\) limit are \(C^{1,1/2}\) graphs, and the graph functions tend to zero in \(C^{1,\alpha}\) for every \(\alpha\in(0,1/2)\).
- The AFM PDF was not re-downloaded. The candidate records `https://cvgmt.sns.it/media/doc/paper/540/Acerbi-Fusco-Morini.FINAL.pdf`, 440786 bytes, SHA-256 `7805d5a0b9daf3873a199bbfe23d4064964fc2e72701be6d45303549028d4c72`. This review did not recompute that hash. The regularity proof between the retained pages was not read.
- `frontier/sources/i269_nonlinear_contact_proof/354-paper.tex`, SHA-256 `ab75095f542adf4073a41a26a3c3ae97be7b55fa19674ec4fb4c288f7145a813`, 8941 bytes. Read Theorem `intro:main` and the attribution through the start of the proof. The proof body was not audited. The profile is \(I(V)=\min\{(36\pi)^{1/3}v^{2/3},\,2\sqrt{\pi v},\,2\}\) with \(v=\min(V,1-V)\).

## Primary literature read in this review

### Lacasse–Grest–Levine

M.-D. Lacasse, G. S. Grest, and D. Levine, arXiv:mtrl-th/9603005v1. HTML opened at <https://ar5iv.labs.arxiv.org/html/mtrl-th/9603005>, the same v1 text as <https://arxiv.org/html/mtrl-th/9603005v1>.

Read: abstract; introduction through the start of Section III; Section III from the boundary conditions through equations (14)–(32) and the force comparison through the Fig. 6 discussion. Displays used in `review.md` are (27) \(\varepsilon\approx -4X^2(\ln X+1/2)\), (28) \(X=(\rho_f/2)^2\), (29) \(\xi\approx -2X\ln X\), (30) \(f\approx 4X\), and (31) \(\varepsilon\approx\frac14 f^2[k-\ln f]\). The rest of the paper was not read. Physical Review E 54 (1996), 5436, was not opened. No citation crawl of that article was performed.

The candidate records the v1 HTML as 229338 bytes, SHA-256 `0cf74f15d1c848c5c57014af739a0cff4dc3f904d6020a4fd67fed547ea368de`, with `body_retained` false. This review did not recompute that hash.

### Lv

Cunjing Lv, arXiv:1704.05830v2. HTML opened at <https://ar5iv.labs.arxiv.org/html/1704.05830v2>, the same v2 text as <https://arxiv.org/html/1704.05830v2>.

Read: abstract and opening; exact elliptic expressions (5)–(7); highly compressed series (17)–(19) and (23)–(25); liquid-Hertzian section (28)–(32) at fixed plate distance and (35)–(39) together with (43) at fixed volume. Equation (29) is \(\xi=-\sigma^2\ln(\sigma/(2e^{1/2}))+\cdots\), and the text inverts it by \(\ln\xi\approx 2\ln\sigma+\ln\ln(1/\sigma)\). Fixed-volume display (38) is the surface-energy expansion quoted in `review.md`. The appendix was not re-derived. The 2020 Langmuir version was not opened.

The candidate records the v2 HTML as 473454 bytes, SHA-256 `ee4280c8d7e6ed70301be1fcdf082b571f8a45cbe4648f3ea034030a51c8d40a`, with `body_retained` false. This review did not recompute that hash.

### Milman

Emanuel Milman, arXiv:2403.06602v3, HTML <https://arxiv.org/html/2403.06602v3>. Read the introduction through Theorem 1.2, Theorem 1.3, and Corollary 1.4. These are scalar isoperimetric ranges for spheres, cylinders, and planes, and a reduction of the profile conjecture to two transition volumes. The unduloid and numerical arguments were not read.

### Displays used only to exclude a different problem

- arXiv:2303.05460, Theorem 6.15 as displayed in the HTML search excerpt: a unique minimizer of a Coulomb-perturbed perimeter whose energy contains \(\gamma^2\varepsilon^6\log(\gamma\varepsilon^4)/(64\pi)\). The proof was not read.
- Barnard–Pearce–Solynin, logarithmic capacity bounded by diameter and area, at abstract or displayed-statement level.
- Solynin–Zalgaller, the regular \(n\)-gon minimizes logarithmic capacity among \(n\)-gons of given area, at abstract level.
- The second-order expansion of fractional perimeter as \(s\to 1\), and Alberti–Cozzi–Massaccesi–Mirmina, arXiv:2605.07543, at abstract or displayed-statement level.

## Identified and not read as theorems

Original Morse–Witten, EPL 22 (1993) 549, and Höhler–Weaire were not opened. I278’s abstract record of them was not adopted as a theorem comparison. Ginot, arXiv:1910.10029, and Alama–Bronsard–Lamy–Topaloglu–Wecht, arXiv:2212.06381, Theorem 4.5, were not re-opened. The TIB/WIAS PDF that the candidate failed to open was not retried, and no theorem is attributed to it.

Search snippets that were not promoted to theorem evidence include Xiao’s geometrical logarithmic capacitance, balls minimizing capacity moments, charged-capillarity Young-law notes around arXiv:2603.24483, Bonacini–Topaloglu, De Rosa–Kolasiński–Santilli, Alama–Bronsard–Topaloglu–Zuniga, Wulff and Cayley problems, logarithmic Sobolev inequalities, minimal surfaces in \(S^4\), Pasqualetto’s isoperimetric notes, solid-torus tubes, large-mass liquid drops, and double-phase logarithmic functionals.

## Search bounds

Searches issued on 2026-10-14, in addition to the papers named above:

- Lacasse–Grest–Levine by title, and the relation \(\xi\approx -2X\log X\);
- small-contact droplet perimeter deficit, logarithmic capacity, second order, and ball–slab or parallel-plate compression;
- Morse–Witten \(f^2\log(1/f)\) as a next-order correction;
- Acerbi–Fusco–Morini Theorem 4.2 and \(C^{1,\alpha}\) convergence of \(\omega\)-minimizers;
- Lv, arXiv:1704.05830, logarithmic contact energy;
- Milman, Theorems 1.2 and 1.3;
- ball or slab, parallel plates, perimeter deficit, finite perimeter or quasiminimizer, and a second-order contact asymptotic;
- nested finite-perimeter pairs, ball and slab, torus, logarithmic contact deficit, and a lower bound in \(\varepsilon\) and \(\log\varepsilon\).

No read theorem states (A) or (D) for all finite-perimeter nested pairs on the unit cubic flat torus. That sentence records the coverage of this screen. It does not establish priority, and it does not turn the silence of these searches into evidence that the all-BV refinement is a new frontier mechanism.
