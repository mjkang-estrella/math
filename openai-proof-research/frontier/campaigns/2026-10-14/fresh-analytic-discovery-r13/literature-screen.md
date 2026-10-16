# Screening and primary operation-level comparison (r13)

Author: Myeongjin Kang (no affiliation). Original prose: CC BY 4.0.
Screen date: 2026-10-16.

## 1. Family screening (before the scope freeze)

Read `sources/CONTENTS.md` (372 families) and the complete
`sources/preprints-tree.json` (13,223 entries, `truncated: false`). The
campaign ledger `NEW-TEN-2026-10-14.md` and the brief's exclusion list
were applied. Candidate analytic families were checked against campaign
use (grep counts in `frontier/`) and against their actual source text.

| Family | Read | Decision |
|---|---|---|
| 350 nodal (three papers) | [P] all sections; [Q] introduction, s3-profiles 1–330, s4-envelopes; [S] introduction | **selected**: no prior campaign use; [P] names an explicit unpaid dimension step |
| 350, boundary variant (Dirichlet/Neumann) | [S] introduction and source structure | rejected: reflection is routine; the source uses only $p,\nabla p$ bounds |
| 360 | catalogue entry and front matter | rejected: transport-adjacent (Brenier exclusion) |
| 148 | catalogue entry | rejected: adjacent to the Salem/Bernoulli family |
| 239, 230 | catalogue entry and front matter | rejected: machinery beyond a bounded round |
| 085, 093, 097, 143, 354 | catalogue entry | rejected: no substantial unpaid operation identified |

Reading extents for the rejected families were catalogue-level and
front-matter-level. They were not logged line by line at the time, so
they are stated here only at that granularity.

## 2. Primary pinned comparison (operation level)

* **[P] `lem:corrugation` vs candidate Lemma 5.1.** Lemma 5.1 is [P]'s
  pattern and estimates with three transverse variables replaced by two
  and $E=\ker\mathrm dh$. The retention step changes from
  $\dim(RE\cap\mathcal F)\ge2+2-3$ to $\mathcal F\subset R\ker\mathrm dh$.
  This is a port, not a new operation. Alone it cannot be iterated,
  because its repeat region gives only one favorable direction.
* **[Q] `lem:profile-preparation` vs candidate Lemma 6.1.** The idea is
  shared: oscillate along a function whose kernel contains a strict
  direction, which makes the orthogonal direction favorable. The
  differences are as follows.
  1. [Q] uses a flow-box first integral and an $N\to\infty$ limit, with
     $C$ depending on the profile through a Schur complement. Lemma 6.1
     uses a frozen linear coordinate, a fixed amplitude $b(C_B,c_B)$, and
     a fixed period ratio $\ell_A/S=\nu^2$.
  2. [Q] makes the profile full on a fraction $p_h/8$ of the mass, and its
     cycle gains only through total mass with all regions reprocessed.
     Lemma 6.1 makes it full on a fraction $1-2\kappa$ with $\kappa$
     arbitrary. This lets the selected children of one parent outweigh
     the whole parent, which is the mechanism behind [P]'s fixed power.
  3. Lemma 6.1 controls every derivative ($\|D^jw_A\|\le C_jbs\nu^{4-2j}S^{1-j}$)
     and the third derivatives needed to transport the strict direction.
     [Q] has no derivative control.
* **[Q] `prop:profile-amplification`.** The source states that its patch
  sizes and frequency thresholds depend on the incoming profile. So it
  cannot give a fixed exponent. The candidate's Section 7 removes this by
  ordering the constants: pattern, then $(C_B,c_B)$, then $\kappa$, then
  $b$ and $C_A$, then $\nu$.
* **[P] remaining sections.** Rerun at base dimension three (candidate
  Section 9). This is a technical transfer. Its counts only decrease.

**Honest contribution assessment (not a verdict).** The theorem T4 is not
in the pinned sources; [P] explicitly disclaims dimensions three and
four. The new mathematical operation is the fixed-ratio fullification
(Lemma 6.1) interleaved with the ported corrugation (Sections 7–8). A
reviewer may judge this a quantitative combination of [P] and [Q]
techniques. That judgment belongs to the parent and independent review.

## 3. External primary-literature screen

Queries (web search, 2026-10-16):

1. "counterexample Yau nodal conjecture upper bound smooth metric power law nodal volume eigenfunctions dimension four"
2. "arXiv 2026 nodal set Laplace eigenfunctions smooth metric Yau upper bound fails dimension three four"
3. "\"power-law\" violations Yau nodal upper bound smooth metric S^4 x S^1 eigenfunctions"

Reading extents:

* ProofAtlas, "Yau's Nodal-Set Upper Bound" (status checked 2026-08-14):
  full page read. It lists the sharp smooth upper bound as open and
  records no counterexample.
* Search listings only, abstract level: Logunov, Ann. of Math. 187 (2018)
  221–239 (polynomial upper bound, $n\ge3$); Logunov, Ann. of Math. 187
  (2018) (sharp lower bound); Logunov–Malinnikova review (CDM 2018);
  Zelditch survey (arXiv 1205.2812).
* Known only through [P]/[Q] citations, not opened: Donnelly–Fefferman
  (1988, analytic case); Hezari (2023, Gevrey and quasianalytic);
  Enciso–Peralta-Salas (2015) and Enciso–Peralta-Salas–Torres de Lizaur
  (2018) (prescribed nodal sets); Dencker–Sjöstrand–Zworski (2004,
  complex-phase WKB).

None of these gives a fixed power-law failure in dimension four. Logunov's
polynomial upper bound $\lambda^{C_n}$ is consistent with T4. This
bounded, dated screen is not a worldwide priority claim.

## 4. Project-internal check

`frontier/` contains no prior proposal, review, or experiment on family
350 other than copies of `CONTENTS.md` in context snapshots (searched for
"nodal" in `*.md`).
