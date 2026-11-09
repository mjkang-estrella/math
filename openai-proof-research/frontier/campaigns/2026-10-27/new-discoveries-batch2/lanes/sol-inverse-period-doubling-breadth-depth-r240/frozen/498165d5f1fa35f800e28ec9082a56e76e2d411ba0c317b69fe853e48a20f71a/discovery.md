# Research handback: chord quadrilaterals; full conjecture unresolved

Credit requested **0**. Counts remain **3/30 additional, 33/60 total**. No acceptance authority, Lean endpoint, or full source proof is claimed.

## Exact selected source and scope

Viktor Vígh, *A note on Kuperberg's quadrilateral conjecture*, arXiv:2610.08168v1, submitted **6 October 2026, 11:23:48 UTC**, manuscript dated 3 October. Actual primary HTML read: https://arxiv.org/html/2610.08168v1 . Definition 2.1 and Conjecture 2.2 ask:

For **every** planar convex polygon P with nonempty interior, let q_ch(P) be the minimum area of a containing convex polygon with **at most four sides**, each parallel to a segment between two vertices of P. Then

    q_ch(P) <= (3/sqrt(5)) area(P),

with equality only for affine images of a regular pentagon. The statement allows arbitrary vertex count and arbitrary real coordinates. A five-/six-vertex example, a rational-input algorithm, or the known sqrt(2) bound does not resolve it. The inequality would imply Kuperberg's all-convex-body inequality via source Proposition 2.3; the equality classification for general bodies does not follow automatically.

This target did not occur in the ledger/prior-context screen or earlier matrix/geometry summaries read. None of the expressly prohibited families was revisited mathematically.

## Registry and closest-body screen before deeper work

The complete registry trees in sol-fresh-analysis-discovery-r7 were reused with **2026-10-29 04:39:40–04:39:44 UTC** coverage, not described as a new HEAD traversal. OpenAI preprints, omega D5 and Problems, and count-ex-machina root/registry were screened for author, subject, and wording. Exact hashes, heads and hit lists are in registry-screen.json and provenance.json. The broad chord term produced 3 omega and 47 OpenAI path hits (qubit, honeycomb/FK interfaces, chord pairings and CAT(0) fillings); these were inspected as path names and did not identify the selected question. This is not proof of novelty or full-text coverage. No GitHub API requests were made, given the existing rate-limit warning.

A live public OpenProblemsInNLA index/RESOLVED read at **06:15 UTC** and targeted public searches were additional bounded screens, not acceptance evidence. No MathDB request was made. A worldwide or comprehensive Palomar/formal-conjectures audit was not performed.

Actual nearby theorem bodies read:

* Vígh §§2–5: the finite support-line candidates, Proposition 2.3, pentagon Theorem 3.1/Corollary 3.2, mixed-area Lemma 4.2 and Theorem 4.1, Remarks 4.3/4.4 and concluding obstructions. These already prove the pentagon case and the all-polygon sqrt(2) estimate. They already warn about discontinuity, the regular-hexagon deletion failure, and the regular-octagon obstruction to the two-quadrilateral method.
* Hong–Ismailescu–Kwak–Park, https://arxiv.org/pdf/2108.00326v1 , actual Theorem 3.1, Observation 3.2, supporting construction and nonnegative decomposition (14)–(19). The pentagon construction uses three edge directions and one diagonal direction. It is prior mathematics, not a discovery here. Theorem 4.1 concerns a containing **pentagon** for a hexagon; chaining its factor 7/6 with 3/sqrt(5) loses the target constant and may introduce directions that are not original chords.
* Fodor–Grundbacher, actual published body, https://publicatio.bibl.u-szeged.hu/39648/1/1-s2.0-S0012365X26001111.pdf , DOI 10.1016/j.disc.2026.115087, Theorem 1.1 and §4 proof: an ordinary containing quadrangle with factor (1-2.6*10^-7)sqrt(2). Its §5 explicitly retains the large gap to 3/sqrt(5). It does not assert the chord restriction. Neither this theorem nor continuity of the unrestricted optimum supplies the selected full statement.

Initial matrix lead excluded: Shi–Wei–Wang's reverse Liu–Cheng question has already-public sharp resolution/refutation in https://arxiv.org/html/2607.01263v1 , actual Theorem 5.1 and Corollary 5.2. For 0<p<=q and r>=0 the universal log-majorization holds iff p<=q<=2p or q>2p and r<=pq/(q-2p); outside, even trace fails in dimension three. This is positive prior-result evidence, not a fresh witness. Direct ScienceDirect access returned 403 and stopped; no source-body clearance of the original journal was inferred from garbled search extraction.

## Attempt and exact obstruction retained

The attempted full strategy was reduction in vertex count, using a continuous deformation toward a lower-vertex polygon together with the already proved pentagon case. It needs control of the *minimum over admissible directions* throughout deformation, not just an unrestricted quadrilateral at the limiting polygon. The following exact certificate shows why replacing that control by continuity is invalid.

Use the **source's own** Remark 4.3 pentagon

    P = conv((0,5),(-5,1),(-3,-4),(3,-4),(5,2)),  S=123/2.

The exact finite enumeration in check.py gives

    q_ch(P) = 2781/35,     q_ch(P)/S = 1854/1435.

Its unique minimal support-normal set is

    3x+5y<=25, -4x+5y<=25, -3x-5y<=29, 3x-y<=13.

There are 18 distinct oriented chord-normal directions and 1716 feasible three-/four-line candidate subsets in the enumerator. Its exact minimum is a finite arithmetic certificate, not floating-point evidence.

An ordinary containing quadrilateral Q is given by

    3x+5y<=25, -4x+5y<=25, 3x-y<=13, -9x-19y<=103.

Its vertices, in cyclic order, are

    (0,5), (-90/11,-17/11), (24/11,-71/11), (5,2).

Every vertex of P satisfies the four inequalities, and shoelace gives area(Q)=873/11. Thus

    q_ch(P) - area(Q) = 36/385 > 0.

No optimality theorem for ordinary Q is needed here. The source already states the corresponding ordinary optimum ratio 582/451; this certificate merely verifies a witness at that ratio.

For **every real 0<e<1**, truncate v=(-3,-4) by

    -9x-19y <= 103-e.

The new vertices replacing v are

    X_e = (-3,-4) + (e/77)(-2,5),
    Y_e = (-3,-4) + (e/54)(6,0).

The other four vertices stay fixed. The denominators 77 and 54 are the exact support deficits of the two adjacent vertices. For this range the points lie strictly inside those edges; P_e is a genuine convex hexagon and converges to P. The removed triangular area is

    15 e^2/(77*54) = 5 e^2/1386.

The first three directions of Q are still polygon-edge directions of P_e. Its fourth direction is now the direction of the new edge X_e Y_e. Since P_e is contained in P, **the same Q** is a chord quadrilateral of every P_e. Consequently

    q_ch(P_e) <= 873/11,
    limsup(e -> 0+) q_ch(P_e) <= 873/11 < 2781/35 = q_ch(P).

Normalized ratios have a strict gap of at least 24/15785 in the limit. This proves a failure of **lower semicontinuity** under a vertex-disappearance degeneration. It does not refute upper semicontinuity or rule out every compactness argument. In particular, claiming that no normalized finite-vertex maximum exists would be unjustified. It does prevent silently treating q_ch as continuous when passing between five and six vertices.

The checker certifies the e=1/100 instance and the area formula's rational identity; the universal e proof is the explicit support-deficit argument above. No grid of e-values is offered as proof of that universal statement.

## Why the enumeration covers the exact finite obstruction

For each pair of vertices form a perpendicular primitive normal and both orientations. For each normal n use h=max n.v. Any containing polygon in these directions can be tightened to these support lines without increasing area. After redundant sides are removed, it has three or four normals in cyclic order with each angular gap strictly less than pi (it is bounded and contains an interior disc). The checker enumerates both sizes. Adjacent determinant positivity tests the angular gaps, Cramer's rule computes the vertices, and all half-plane constraints are checked. Exact rational shoelace areas are compared. Thus none of the admissible containing polygons with at most four sides can improve the returned minimum. This is the source's finite-candidate principle, instantiated independently with exact arithmetic.

## Precise remaining gap and strongest objection

There is **no proof or refutation of Conjecture 2.2** here. What is needed is an all-n inequality controlling the minimum of the support-line rational area functions, or a genuine polygon for which every feasible candidate exceeds 3/sqrt(5) times its area. The retained pentagon has 5*(1854/1435)^2<9 and hence is strictly below that bound. Its truncated hexagons do not refute the conjecture either.

A proposed extremum proof must handle changing active supports, newly appearing chord directions, and nonsmooth minima. No argument excluding all non-pentagonal maxima or proving their value <=3/sqrt(5) was found. The source itself defeats naive deletion and its two-candidate sqrt(2) argument; repeating these would not close the gap.

**Strongest eligibility objection:** the obstruction, polygon and qualitative noncontinuity are already in the source. The new work is a reproducible exact arithmetic elaboration of prior mathematics, not an eligible research outcome. Even a new finite witness or a fixed-n positive case would earn no credit under this assignment. No PROOF.md or formalization was started.

## Reproduction and limits

Run `python check.py` in this lane. It uses only the Python standard library, fixes BLAS/OMP threads to one, enforces 512 MiB address space and 50 CPU seconds, and writes checks.json. Current replay PASS. An initial text extraction attempt failed because bs4 was unavailable; this failure is preserved in progress.md and a standard-library HTML parser was used instead. No limit was raised.

All file writes were restricted to this lane. No children, git commands, browser tabs, posts, contacts, uploads, accounts, or shared ledger changes.
