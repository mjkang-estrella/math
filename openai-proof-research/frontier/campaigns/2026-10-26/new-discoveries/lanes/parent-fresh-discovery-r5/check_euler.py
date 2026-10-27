"""Independent exact sign check using the defining Euler recurrence."""
from math import comb, factorial
from pathlib import Path
import json

N = 150
E = [1, 1]
for n in range(1, N):
    t = sum(comb(n, k) * E[k] * E[n-k] for k in range(n+1))
    assert t % 2 == 0
    E.append(t // 2)
F = [factorial(n) for n in range(N+1)]
cases = [0]*8
for n in range(51):
    for j in range(1, 51):
        for k in range(1, 51):
            v = E[n]*E[n+j+k]*F[n+j]*F[n+k] - E[n+j]*E[n+k]*F[n]*F[n+j+k]
            assert v > 0 if n % 2 else v < 0, (n,j,k,v)
            cases[4*(n%2)+2*(j%2)+(k%2)] += 1
report = dict(method="defining Euler recurrence; exact integer cross multiplication", n_max=50,
              j_max=50, k_max=50, total=sum(cases), failures=0, parity_counts=cases,
              discovery_credit=0, note="Checks only; the proof is in EULER-PROOF.md")
Path(__file__).with_name("euler-check.json").write_text(json.dumps(report,indent=2)+"\n")
print(json.dumps(report))
