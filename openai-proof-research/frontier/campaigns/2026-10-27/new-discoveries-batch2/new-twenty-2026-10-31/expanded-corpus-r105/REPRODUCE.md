# Reproduction

Run from this lane. Set PYTHONDONTWRITEBYTECODE=1 and TMPDIR=$PWD/tmp on Python/search calls. No installation is required. Sources and raw records are frozen locally with receipts. Do not repeat registry fetches on another branch route or retry a denied route.

The general runner is `python scripts/limited.py LOGNAME COMMAND ARGS...`. Each child is monitored for sampled RSS, affinity, CPU and wall caps; stdout goes to logs/LOGNAME.log and the exit/cap receipt beside it. A nonzero return or missing completed row is not successful coverage.

The main search scripts are search_graphs.py (small/random), graph_structured.py, search_chip_multinomial.py (chip/multinomial), finite_batch.py (colour/digraph/goldbach), permutations.py, permutations_deep.py, cnsf_search.py, tree_band.py, atlas_degree.py, linkage.py, rooted.py and pythagorean.py. The atlas script reads the preexisting sibling vendor/networkx tree without mutation; see its exact import path.

The native helpers have no missing system-header dependency: clang was available in the existing Lean distribution but the system had no C/C++ headers/compiler. Compile each *.c with that clang using `-O3 -shared -fPIC -nostdlib`, outputting the correspondingly named lane-local *.so. run_c.py uses lengyel.so; run_chip_c.py uses chip_fast.so; run_pyth_deep.py uses pyth_deep.so. The .cpp and failed executable-link route are exploratory remnants, not authoritative implementations.

For the principal exact lead, rerun kirchhoff_certificate.py under the cap and then verify_kirchhoff.py. The second uses only fractions.Fraction for all matrix, coefficient and sign checks; it reconstructs the graph and verifies the explicit certificate independently of SymPy. It establishes the ordinary exact calculation, not the unresolved source interpretation or a Lean endpoint.

`report.py` assembles exactly20 ID-keyed entries. `validate.py` checks IDs, raw and source bindings, local artifact existence, solver lower witnesses and the relevant source-coefficient signature equivalence. SHA256SUMS.json is the final artifact inventory; historical reports and dependencies remain untouched.
