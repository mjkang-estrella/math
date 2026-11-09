# Heuristic calibration (Monte Carlo)

Random L-digit integers; `0-free start` = random digits from {1..9}.

| L | N | max P (all) | max P (0-free start) | P(P>=11 \| 0-free) |
|---|---|---|---|---|
| 10 | 200000 | 10 | 10 | 0.00e+00 |
| 15 | 200000 | 10 | 10 | 0.00e+00 |
| 20 | 200000 | 9 | 10 | 0.00e+00 |
| 30 | 200000 | 3 | 5 | 0.00e+00 |
| 45 | 200000 | 2 | 3 | 0.00e+00 |
| 65 | 200000 | 2 | 2 | 0.00e+00 |
| 95 | 50000 | 2 | 2 | 0.00e+00 |
| 140 | 50000 | 1 | 2 | 0.00e+00 |
| 200 | 50000 | 1 | 2 | 0.00e+00 |
| 300 | 50000 | 1 | 2 | 0.00e+00 |

Interpretation: see notes/theory.md section 7. The conditional
probability of reaching persistence >= 11 from a random 0-free start
should collapse super-exponentially in L; extrapolation gives the
expected total count of persistence-12 integers.
