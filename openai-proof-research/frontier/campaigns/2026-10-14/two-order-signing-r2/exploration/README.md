# Exploratory numerics (not verified, not proofs)

Author: Myeongjin Kang, no affiliation. Code MIT, prose CC BY 4.0.

These scripts were run in a scratch virtual environment outside this
directory (numpy 2.5.4, scipy 1.18.1 with HiGHS, cvxpy 1.9.3 with CLARABEL),
under Python 3.14.7. They use floating point and MILP/SDP solvers. They are
hashed in `output-manifest.json` for provenance only. `verify.py` does not run
them, and no statement in `candidate.md` depends on them. The only exploration
result that enters the verified replay is the 5/3 instance, which check E
re-verifies exactly in rational arithmetic.

| Script | Purpose |
| --- | --- |
| `milp.py` | `wdisc(rho, w)`: exact-by-MILP two-order value of scalar weights w (first order identity). |
| `search.py` | Random search over orders and weights, all signings enumerated, N <= 9. |
| `climb.py` | Weight and order hill-climbing using `milp.wdisc`. Output in `climb-logs.txt`. |
| `minimax.py` | Cutting-plane max over weights / min over signings for a fixed pair of orders. |
| `family.py` | Test of a guessed extension of the minimax optimum to larger k. |
| `vecdisc.py` | SDP (vector-coloring) relaxation value of two-order prefix rows. |
| `vecclimb.py` | Weight climbing on the SDP value. Output in `vecclimb-logs.txt`. |

Results recorded during the session:

* `search.py`: maximum observed value about 1.65 for N <= 9.
* `climb.py` (`climb-logs.txt`, 14 restarts at N = 13 and N = 21): best
  observed 1.7067 at N = 13. No observed value reached 2.
* `minimax.py` on Reis's Theorem 142 orders: k = 2 gives 3/2, and k = 3 gives
  5/3 at weights (1, 5/6, 1, 5/6, 1, 2/3, 1). Check E in `checks.py` confirms
  the k = 3 value exactly. Reis's own weights give (2k+2)/(k+2), which is
  8/5 at k = 3.
* `family.py`: the guessed extension of the k = 3 weights did not beat Reis's
  values for larger k. It was abandoned.
* `vecdisc.py` and `vecclimb.py`: the SDP value never exceeded 1 (up to solver
  tolerance) on random and bit-reversal instances with N <= 128, nor in the
  climbs at N = 12 and 24 (`vecclimb-logs.txt`).

The minimax, family and vecdisc runs printed to the terminal and were not
saved as logs. Their results are transcribed above from the session, and
the k = 3 minimax value is the only one re-checked exactly.

These observations say nothing about large N. They are not evidence for or
against T2 in any rigorous sense.
