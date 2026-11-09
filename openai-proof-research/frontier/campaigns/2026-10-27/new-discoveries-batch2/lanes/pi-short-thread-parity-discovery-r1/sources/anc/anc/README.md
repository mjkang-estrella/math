# Ancillary files for "Nim heaps in the Game of Cycles: the parity conjecture fails on trees"

Programs and data behind every computational statement in the paper.

**Requirements.** Python 3 with `networkx`, and a C++17 compiler (`g++ -O2`).

**Quick start.** `bash quick_checks.sh` compiles the C++ programs and runs twelve fast checks of the main claims. It takes about one minute and should end with `passed: 12   failed: 0`.

Notation follows the paper: `S(x,y,z)` is the spider whose legs have `x, y, z` *markable* edges. Some programs take *original* leg lengths instead, which are the markable counts plus 1; this is noted below where it applies.

## Directory overview

| directory | contents |
|---|---|
| `core/` | (P1) raw-rules solver `brute.py`, which uses no theory at all; (P2) normal-form solver `decomp.py` for arbitrary trees (Prop. 3.7); (P3) spider solvers `spider.py`, `spider3.cpp`, `spiderk.cpp`, `periodic.py`; scripts for the census, Table 3, Prop. 7.2, the H-trees, and random tests of Thms 5.1 and 5.6 |
| `raw_cpp/` | an independently written raw-rules solver `raw.cpp`, plus `census.py` and `gen_trees.py`, which produced the census up to n = 20 (Table 2); an independent spider solver `spider.cpp`; a fixed-leg family solver `fam.cpp` |
| `families/` | Section 8: `verify23.py` (Table 6, Thm 8.5, Thm 8.1) and `certify_gen.py` (the certificate of Section 8.4 for one pair); `run_all.sh` re-runs all 99 certificates of Thm 8.12; `famstates.cpp` with the cross-checks; `forms/` holds the closed forms of every blocked family; `logs/` holds the output |
| `onetwoj/` | Section 9: `fsolve.cpp` (fixed-short-leg solver), `lemmas.py` (the closed forms of Lemmas 9.3–9.7 and Thm 9.1), `verify_lemmas.py`, `window_check2.py` (Remark 9.8), and `data/summary.json` (periods and patterns for y ≤ 64) |
| `threads/` | Section 10: `arrows*` (normal-form solver with canonical hashing), `genpieces.cpp` (enumeration of twin-free pieces), `parsolve2.cpp`, `rawarr.cpp`, `rulecheck.cpp` / `kcheck.cpp` (the strategy of Lemma 10.9 and the closure of class C), and `data/` with T21, T23, the 25-vertex trees and the exhaustive search logs |
| `large/` | H-tree solvers `hsolve.cpp` and `hverify.cpp` (independent of each other); `cube3.cpp` (all spiders with legs ≤ 300); `gen.cpp` (general trees); `data/` with the records and verification outputs (Section 11) |
| `independent_checks/` | independent re-implementations, each written by a separate instance of an AI system from the paper's text alone (the source comments call the author of these programs "the referee"; see the section "Use of AI tools" in the paper): `v1/` covers Section 8, `v2/` covers Section 9 and Prop. 11.2, `v3/` covers Section 10, including `pc3.cpp`, the exhaustive enumeration behind the minimality in Thm 10.11 |
| `data/` | census outputs; spider values for all legs ≤ 120 (`spider3_values_legs_le_120.txt`, columns `x y z g`); hand-checkable certificates `certificate_S1_3_7.txt` and `certificate_S1_4_6.txt` |

## Claims and how to check them

| claim in the paper | how to check | time |
|---|---|---|
| Thm 4.3 (run values) | `cd core && python3 runs.py` | seconds |
| Thm 7.1(a, b), Table 2, n ≤ 20 | `cd raw_cpp && g++ -O2 -o raw raw.cpp && python3 census.py N` (raw rules); `cd core && python3 survey2.py N` (P2); outputs in `data/` | seconds to about 4 h (n = 20) |
| Thm 7.1(b): S(1,3,7), S(1,4,6) | `python3 core/brute.py 2 4 8` and `... 2 5 7` (original leg lengths) | seconds |
| Thm 7.1(c): the H-trees | `cd core && python3 htree.py` | about 1 min |
| Table 3 (first moves on S(1,3,7)) | `cd core && python3 firstmoves.py 1 3 7` | seconds |
| hand-checkable certificate for S(1,3,7) | `data/certificate_S1_3_7.txt` (205 states with all option values); regenerate with `core/certificate.py 1 3 7` | seconds |
| Prop. 7.2 (Zandee) | `cd core && python3 zandee_brute.py` (raw rules) and `python3 zandee.py 12` | seconds |
| Table 4, Thm 7.3 | `core/spider3.cpp` (`./spider3 120`), `core/spiderk.cpp` (`./spiderk 18 91 96` gives 32), `raw_cpp/spider.cpp` | 2 min / 30 s |
| Table 5 (families, z ≤ 600) | `core/eventual2.py`, `raw_cpp/fam.cpp`, `data/fam_all.log` | minutes per pair |
| Thm 8.1, Thm 8.5, Table 6 | `cd families && python3 verify23.py 100 160` | seconds |
| Thm 8.12, Table 7 | `cd families && bash run_all.sh`; per pair: `python3 certify_gen.py x y 160` (use 200 for (2,33)) | 20–40 min in total |
| Thm 9.1, Cor. 9.2 (proved by hand) | numerical confirmation: `cd onetwoj && g++ -O2 -o fsolve fsolve.cpp && python3 verify_lemmas.py 2000 4 6 8 ...` | minutes |
| Thm 10.3, Cor. 10.4 (proved by hand) | the strategy check `independent_checks/v3/ctest.cpp`; `independent_checks/v3/pc3 tree 2 4 N` (all trees with threads ≤ 2) | minutes |
| Thm 10.11 (T21, T23, minimality) | `threads/rawarr.cpp` on `threads/data/L3_cex23.txt`; `independent_checks/v3/pc3 tree 3 4 23` (exhaustive; hours); outputs in `independent_checks/v3/tree3_*.out` | hours |
| Section 11 (H-tree values up to 62, spiders up to 44) | `large/hsolve.cpp` and `large/hverify.cpp`; `large/data/verify_*.txt` | minutes |

The two raw-rules solvers (`core/brute.py`, `raw_cpp/raw.cpp`) implement only the rules of the game: an arrow may not create a vertex whose edges are all marked and all point in, or all point out, and the last player to move wins. They use none of the theory in the paper.
