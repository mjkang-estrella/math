# Progress (r271)

## Completed
1. Administrative snapshots (batch AGENTS.md, ancestor AGENTS.md, ledger.json, prior-campaign-context.json, root r268 STATUS). Scientific freeze of the r268 SCOUTING/discovery/SUMMARY/FAILURES/check.py and the 1801.07238v1 PDF/text, then a fresh arXiv refetch that is byte-identical (sha256 93ac70a7…88553). arXiv abs page gives v1 only, journal ref Period. Math. Hung. 79 (2019) 78–85, DOI 10.1007/s10998-018-0263-y.
2. Early follow-up/current-prior screen: OpenAlex work W2785073105 (0 citing works); Semantic Scholar 429 (stopped); arXiv exact-phrase, Helly+central symmetry, "admissible centers" and author queries (only the source, plus Bárány–Jerónimo-Castro 1310.0910, a different question, answered in-source). Project-wide identifier grep and the 876-reference history index (verified in place, contents screened) found no alias.
3. Literal-scope analysis: parabola refutes the literal unbounded statement for every k; vacuity; Theorem T reduces bounded sets to finite sets (discovery.md §2).
4. Lemma A exact criterion and Lemma B geometric form; exact checkers `csc.py`/`csc2.py`.
5. Mechanism (a) near symmetry: first-order model reduces to ordered line transversals (Hadwiger); model searches (`search_model.py`, `search4.py`) and exact validation (`validate_model.py`, 392/392; `run_checks.py`, 112/112).
6. Mechanism (b) and the triangle route: topology of M_T intersections (`t_topo.py`, `t_topo2.py`); exact refutation of three-triangle Helly (`t_six.py`).
7. Far-from-symmetric adversarial search: `search_odd.py`, `reduce_search.py`, `climb.py`, `climb_insert.py` (logs in `logs/`). No minimal obstruction above 9 points.
8. Scouting of 13 families with primary PDFs (SCOUTING.md).

## Climb tallies (exact; best = number of one-point deletions that are c.s.c. while X itself is not)
Ten guarded runs of 100 s each, all guard_exit 0 (`logs/climb*.txt`):
* random restarts, n = 10, seeds 1–4: best 9/10 each;
* random restarts, n = 11, seeds 2–4: best 9/11 each;
* insertion into the nine-point minimal obstruction (t = [1,1,3,0,0,3,0,0,3]): n = 10, seeds 1–2, best 9/10; n = 11, seed 3, best 9/11.

No 10- or 11-point minimal obstruction was found. This is a bounded local search, not evidence of nonexistence.

## Sign-pattern ("odd function") formulation, recorded for the next solver
For t = 2O, define ψ_t(n) = h(n) − h(−n) − n·t, an odd function on the circle, piecewise sinusoidal with breakpoints at ±edge normals. t is admissible iff no vertex arc N_x (between consecutive edge normals) has ψ_t < 0 at all of its breakpoints. Equivalently, every maximal negative run of ψ_t contains at most one edge normal. With L_i(t) = 2μ(e_i) − e_i·t this becomes a sign-vector condition on an arrangement of n lines. In the near-symmetric case the runs decouple into the pair constraints D_j (Hadwiger). In general one vertex run involves several opposite edges, and the decoupling fails. A positive proof needs a bounded certificate per run.

## Not completed
Full finite source question; lead-2 (Bergman Q6) and lead-3 (Konyagin–Łaba) mathematics; current public proof-registry heads; worldwide novelty clearance.

## Reproduction
From this lane:
`OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python3 ../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python3 run_checks.py` (≈ 8 s; writes exact-checks.json). Same guard for `finalize.py`, then `verify.py`. Fixed caps: AS/group RSS 512 MiB, CPU 210 s, wall 230 s; no cap raises.
