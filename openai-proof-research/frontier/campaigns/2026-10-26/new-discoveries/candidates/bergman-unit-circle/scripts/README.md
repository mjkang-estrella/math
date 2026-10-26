# Independent arithmetic cross-checks

`python3 check_bijection.py` uses only the Python standard library and reconstructs71 complete source-to-SOS coefficient bijections. It regenerates independent-bijection-check.json next to the script.

`python3 check_source_five_piece.py` additionally uses the optional python-flint package and compares the source q0,…,q4 ceiling formulas with the SOS for1965 coprime pairs through m80. Its original result is source-five-piece-check.json. This optional numerical-library check is exact integer polynomial arithmetic, not floating-point evidence.

Neither finite check is needed by the Lean certificate, which proves the full conjecture for all source parameters with no computation/bridge assumptions.
