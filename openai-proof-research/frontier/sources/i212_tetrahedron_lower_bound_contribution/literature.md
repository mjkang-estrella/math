# I212 literature and comparison record

2026-10-12. Contribution verdict: **CONTRIBUTION SUPPORTS NOMINATION**, limited to one exact regular-tetrahedron absolute lower-bound theorem and its quadratic-certificate optimum. This does not establish worldwide priority or complete the proof gate. The stronger old insphere consequence described below should be acknowledged in the nomination.

## Primary statements actually read

**Bezdek–Litvak, Covering convex bodies by cylinders and lattice points by flats (2009).** Existing `../i201_elliptic_covering/bezdek-litvak-2009v1.pdf`, read in place: all 14 pages, including Theorem 2.1, Section 3, Theorem 3.1, its proof and both subsequent remarks. The theorem gives sum crv >=1/d and >=1 for ellipsoids; crv divides each base by the projection in its own direction. The ball proof uses a density with constant line integrals. The general proof uses the section/projection inequality. These are old methods. The introduction directly identifies the half-minimum-shadow problem and the regular tetrahedron's two-cylinder example. [Primary v1](https://arxiv.org/abs/0903.4842v1), [published DOI](https://doi.org/10.1007/s12220-008-9063-6).

**Bezdek–Litvak, Packing convex bodies by cylinders (2016), arXiv v2 of 21 November 2015.** Retained [PDF](bezdek-litvak-packing-2016-v2.pdf), all 14 pages read. Theorem 3.1 extends the covering inequalities to multiplicity r; for dimension three, line axes and r=1 its general conclusion is still 1/3. Theorems 4.2, 4.4, 4.6 and 5.1 are packing statements. Section 6 treats sectional-integral optimization and planar plank packing; reversing those inequalities does not yield a tetrahedral cover lower bound. This follow-up contains no stated weighted tetrahedral chord envelope or optimal quadratic certificate. [Primary v2](https://arxiv.org/abs/1507.05115v2), [published DOI](https://doi.org/10.1007/s00454-016-9760-z).

**Falconer, Function space topologies defined by sectional integrals and applications to an extremal problem (1980), pp. 81–96.** Retained [PDF](falconer-1980-sectional-integrals.pdf), all 16 pages read through text extraction. Sections 1 and 3 set up mass maximization under bounded hyperplane integrals. Theorems 5.1–5.3 address general-body estimates; Corollary 5.4 explicitly uses averaging over regular-simplex symmetries. Theorem 6.1 connects the extremal problem to nonnegative ridge functions and multiple plank covers. Thus the optimization perspective and symmetry device are old. Its dimension-three sections are planes, not lines. This paper does not state I209's line-integral maximum or constant. Some formula glyphs in this old PDF extract poorly; no independent numerical-formula audit is claimed. [Primary publisher source](https://doi.org/10.1017/S0305004100056553).

**Akopyan–Karasev–Petrov, Bang's problem and symplectic invariants, arXiv:1404.0871v1 (2014).** Retained [PDF](akopyan-karasev-petrov-2014v1.pdf), all 15 pages read. Section 7.1 explicitly describes probability-measure duality for fractional covers, then treats Euclidean balls. Theorem 7.1 extends the ball result from one-dimensional to two-dimensional cylinder axes. Section 3 includes simplex-related billiard discussion, not the present weighted chord estimate. Sections 4 and 8 distinguish symplectic cylinders and capacity conjectures. Neither conjectural subadditivity nor ball results are a proved stronger lower bound for a regular tetrahedron with arbitrary line-axis cylinders. [Primary v1](https://arxiv.org/abs/1404.0871v1). Later versions/the 2019 published edition were not read.

**Verreault, Plank theorems and their applications: a survey.** The arXiv abstract page identifies v2, revised 22 October 2025. Directly read HTML lines 550–560, Question 4.14 and surrounding discussion, plus the broader returned excerpts around lines 471–589 and bibliography lines 1088–1123. The question is the absolute half-minimum-shadow bound; the adjacent text reports the universal 1/3 result. This is corroboration of the problem's recognized status, not a complete or current-priority survey. Its pre-corpus open-status statement is superseded in this task by stipulated pinned results. No local survey copy was created and no whole-survey read is claimed. [HTML v2](https://arxiv.org/html/2203.05540v2), [published DOI](https://doi.org/10.1112/blms.70230).

**Bang (1951).** A direct AMS PDF request failed with HTTP 403; the web open also failed. No file was retained and no reading of the original is claimed. Attribution of the cylinder question and tetrahedron example comes from the directly read Bezdek–Litvak primary accounts, not a fabricated Bang quotation.

## Stronger consequence of old literature

For the edge-two regular tetrahedron, the insphere has radius 1/sqrt(6). A cylinder cover of the tetrahedron covers that ball, so the 2009 ball theorem implies

    sum |B_i| >= pi/6,
    sum |B_i| / A_min(T) >= pi/(6sqrt(2)).

This improves on 1/3 and must be included in a fair comparison. It remains below I209's sqrt(15)/9: the ratio is 2sqrt(30)/(3pi)>1. This is an explicit deduction from the primary theorem, not a claim of a separately published best-tetrahedron constant. No stronger applicable result appeared in the primary statements actually read.

## Pinned corpus comparison, read in place

All are at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb; exact source hashes appear in the authentication record.

- Ruled-set approximation: full retained `introduction.tex`, `comparison.tex`, and `references.bib`. Labels `b:projection` and `b:approximation` give upper-cover cost and finite approximation. The bibliography locates old literature; it is not evidence of novelty. I did not read the complete finite-approximation proof or all its input files for this contribution review.
- Angular covers: full retained `introduction.tex` and `angular-cubic-buffer.tex`. Labels `thm:counterexample`, `cor:normalized-covering`, and `prop:angular-cubic` are upper-cover statements. The last gives an actual finite cover with normalized cost 1/2-tau^2/240+(25/2)tau^3 and error at most 2tau^4. It supplies a strict upper endpoint and is not new I209 content. The separate `sections/history` input was not read.
- Slope fields: full retained introduction and I209 copies of `rational.tex`, `singular.tex`, `projection.tex`. Labels `c:main`, `c:affine-tetrahedra`, `c:rat-rational-proposition`, `c:sing-theorem`, `c:normal-frame`, and `c:nil-projection`. The projection appendix gives the ordinary simplex identity A(u)L(u)=3V, not the quadratic weighted envelope. The rational and singular sections construct upper covers, not I209's lower certificate. Other source sections and input figure files were not read.
- Radial sweeps: full retained introduction and I209 `radial-projections.tex`. Labels `thm:radial`, `cor:tetrahedron`, `prop:simplex`, and `eq:regular-normalization`. The simplex identity A(u)L(u)=dV and minimum area e^2/(2sqrt(2)) are already paid. The main theorem concerns finite upper approximation; it does not optimize nonnegative quadratic line densities. The rest of the manuscript was not read.

The original weighted envelope controls chord offset as well as length. The scalar endpoint inequality is elementary, and the final choice a=19/10 is ordinary differentiation. Neither alone merits a separate nomination. The substantial claim is the quantitative lower theorem obtained by combining a sharp offset-sensitive envelope with the old density principle, and the exact scope of its quadratic optimum.

## Executed search families and exclusions

Searches were conducted on 2026-10-12, without research code or numerical scans. The following are literal queries or groups of literal queries actually used; results were used as leads to primary statements, not as novelty certificates:

- `"tetrahedron" "cylinders" "lower bound" covering`; `"cylinder covering" tetrahedron lower`; `"Bang" "tetrahedron" "lower bound"`; `tetrahedron "covering" "base areas"`.
- `"Bezdek" "Litvak" covering cylinders 2014 2015 2020`; `"covering" "cylinders" "Litvak" "2016"`; `"Packing Convex Bodies by Cylinders" pdf`.
- `"tetrahedron" "sqrt" "15" "covering" cylinders`; `"tetrahedron" "sqrt(15)" covering`; `"tetrahedron" "sqrt(30)" cylinders`; `"cylinders" "sqrt(15)"`; `"cylinders" "0.430"`; `"cylinder" "sqrt{15}" "9" covering`; `"sqrt(15)/9" geometry`; `"square root of 15" "cylinders"`; `"tetrahedron" "cylinder" "19/10"`; `"tetrahedron" "cylinders" "two fifths"`.
- `"tetrahedron" "cylinders" "quadratic"`; `"tetrahedron" "quadratic density"`; `"tetrahedron" "sectional integrals"`; `"simplex" "sectional integrals"`; `"tetrahedron" "X-ray" "density"`; `"tetrahedron" "line integrals" covering`; `"tetrahedron" "line integrals" "maximum" density`; `"tetrahedron" "weighted chord"`; `"simplex" "quadratic" "cylinder" covering bound`.
- `"simplex" "cylinder covering" lower bound`; `"tetrahedron" "cylindrical" "covering"`; `"cylinder coverings" lower bounds density`; `"Bang" "cylinders" "lower bound" tetrahedron density`.
- `"cylinder" "Verreault" survey plank`; `"Plank theorems and their applications" arxiv`; `"Function space topologies defined by sectional integrals"`; `"Falconer" "Croft" extremal problem integrals`; `"Falconer" "sectional integrals" filetype:pdf`; `"Bang’s problem and symplectic invariants" pdf`; `"On the covering index of convex bodies" "cylinder"`.

Searches also excluded corpus mirrors in one later query. Corpus mirrors were not independent evidence. Unrelated hits concerned a single circular enclosing/circumscribing cylinder, translative or lattice covering of space by tetrahedra, tetrahedron packing density, tomography algorithms, or finite-element integration. These have different objects or quantifiers. For example, the 25/18 simplex lattice-covering-density hit concerns translates of a tetrahedron covering space, not sums of arbitrary cylinder base areas covering one tetrahedron. It was not treated as a competing theorem and no full-source read is claimed. Exact-constant hits outside geometry likewise do not establish prior art.

The relevant results actually opened and read are enumerated above. Other search hits, including the covering-index paper, were not used to assert the absence of a hidden theorem. The direct arXiv HTML request for survey v4 returned 404; v2 was then used. The initial publisher abstract open for Falconer timed out; its primary full PDF was subsequently obtained and read.

## Priority boundary

The literature establishes that the method and symmetrization predate I209, and that the specific primary cylinder theorems reviewed do not supply its stated weighted envelope or constant. The nomination is supported by that positive comparison and the size of the exact improvement, not by empty search results. This is not an exhaustive best-bound survey, and unrestricted “first” or “best known” claims remain unsupported. The lower bound is absolute and regular-tetrahedral; no directionwise affine-invariant improvement is inferred.
