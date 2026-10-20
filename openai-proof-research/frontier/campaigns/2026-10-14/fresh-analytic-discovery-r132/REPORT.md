# Analytic r132 handoff: PREFREEZE, no nominee

Runner: Factory Droid / claude-opus-5-5 / high. Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Tree
eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b (13223 entries). This handoff assigns no gate,
verdict or count; those belong to the parent.

- Status: no scope was frozen and nothing is nominated.
- Family 088 (Brannen, open for 4 <= n <= 8) was resumed with a new route, not a rerun of r131. Maximizing FHLX
  Prop. 4.1 over lambda makes it exact. For every facet count m, P_n/c_n = sup_t Psi(A - 1t^T), where
  Psi = sum_J |det[1 A]_J| f_{A^T E}(0)/(n+1). For n+2 facets this is D(a)||B-spline||_inf/(n+1)^2. The whole
  (n+2)-facet problem is equivalent to one expectation inequality (★) in n+1 parameters. These are author derivations
  and equivalent formulations, not results.
- First-order threshold (float): optimizing direction and cluster position off the whole simplex curve gives ratios
  .953 (n=8) and 1.0195 (n=9). The threshold of the (n+2)-facet class is therefore exactly n = 9 at first order.
  Triangle merges show no improvement (Monte Carlo). No counterexample was found for n <= 8.
- Unpaid: (G1) (★) for n = 4..8, which would give the sharp theorem "Brannen holds for every polytope with at most
  n+2 facets iff n <= 8"; (G2) the linearized inequality alone; (G3) any counterexample for n <= 8.
- Late reads: source P (authenticated, main.tex lines 38-237) and an arXiv metadata/web check (2610.13953 is v1 only),
  both after exploration and before the decision. The FHLX body was read from the I43-retained text.
- Resources: pure Python, one process, `ulimit -v` 1 GB; about 5 GB of system memory was free. r131 was left untouched.
- Public: packet/public/report.md, reading-limits.md, verify.py, controls.py; scratch/ code and outputs. Private:
  upstream source P and registers.
- FINAL.json sha256 44b08b8e400fa6477d1ab1e1f918e3d23098d60beb19b02112f29a2d8a12a366; packet/MANIFEST.json sha256
  594c1cad6d394b851b9468c7b002b84a1469753a033633a6a44445587798a44f.
- Integrity: run `python3 -B packet/public/verify.py --root ROOT --manifest-sha256 <M> --final-sha256 <F>
  --report-sha256 <R> [--project-root PROJECT]` with the detached anchors. These are byte and inventory checks
  only. Copied-control results are in CONTROL-RESULTS.json, which is outside the manifest.
