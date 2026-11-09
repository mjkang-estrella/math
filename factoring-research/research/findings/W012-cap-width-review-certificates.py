"""Three frozen exact arithmetic certificates; no search or candidate run."""

from fractions import Fraction as F
from math import gcd
from pathlib import Path
import hashlib
import json


def rational(value):
    value = F(value)
    return {"numerator": value.numerator, "denominator": value.denominator}


# Fixed geometric obstruction, chosen explicitly in the written audit.
N, R, m, j, u, v, x = 899, 4, 2, 1, 4, 8, 5
assert gcd(N, m) == gcd(x, m*m) == 1
assert m*m <= R and N >= R*R and R <= u < v <= 2*R
assert (x-j) % m == 0 and abs(F(x)-F(u+v, 2)) <= F(m, 2)
arc = F(N, x)
chord = F(N*(u+v-x), u*v)
height = F(N*(x-u)*(v-x), u*v*x)
assert chord-arc == height
width_lower = F(N*((v-u)**2-m*m), 32*R**3)
assert height >= width_lower >= m*m
assert F((v-u)**2) >= m*m*(1+F(32*R**3, N))
residue = (N*pow(x, -1, m*m)) % (m*m)
offset = (arc-residue)/(m*m)
rounded_steps = -((-offset.numerator)//offset.denominator)
y = residue + m*m*rounded_steps
assert y == 183
assert (x*y-N) % (m*m) == 0
assert (y-N*pow(j, -1, m)) % m == 0
assert 1 <= arc <= y < arc+m*m <= chord <= N
geometry = {
    "N": N, "R": R, "m": m, "j": j,
    "u": u, "v": v, "x": x, "y": y,
    "arc": rational(arc), "chord": rational(chord),
    "height": rational(height), "width_lower": rational(width_lower),
    "ordinate_residue_mod_m_squared": residue,
    "result": "The hull contains the displayed allowed lattice point."
}


# Fixed optimizer-domain warning; the optimum follows by direct ceiling.
N, x, a, b = 35, 2, 1, 1
min_y = (N+x-1)//x
s = a*x+b*min_y
assert min_y == 18 and s == 20
assert x*(min_y-1) < N <= x*min_y
P = 5
poly_at_factor = a*P*P-s*P+b*N
assert N % P == 0 and P != x and poly_at_factor == -40
clipping = {
    "N": N, "L": x, "U": x, "a": a, "b": b,
    "minimum_y": min_y, "minimum_s": s,
    "factor_outside_query": P, "quadratic_at_factor": poly_at_factor,
    "result": "The strict polynomial exclusion must be clipped to [L,U]."
}


# Fixed empty-population counterexample. These are three stated abscissas,
# not a prime/modulus/parameter scan.
R, N, m = 2, 35, 12
assert gcd(N, m) == 1 and N >= R*R and m*m > R
fixed_abscissas = (2, 3, 4)
fixed_gcds = tuple(gcd(t, m) for t in fixed_abscissas)
assert fixed_gcds == (2, 3, 4)
assert (1, 5, 7, 11) == tuple(t for t in (1, 5, 7, 11) if gcd(t, m) == 1)
assert m == 2**2*3 and m*(1-F(1, 2))*(1-F(1, 3)) == 4
empty_population = {
    "R": R, "N": N, "m": m,
    "central_abscissas": fixed_abscissas, "gcds_with_m": fixed_gcds,
    "phi_m": 4, "retained_candidate_count": 0, "occupied_chart_count": 0,
    "result": "No chart query is required to cover this empty retained set."
}


output = {
    "scope": "Three fixed exact algebraic certificates only; no parameter sweep, optimizer or factoring candidate.",
    "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    "certificates": [geometry, clipping, empty_population],
    "all_assertions_passed": True,
    "limitation": "Finite arithmetic corroboration; the general proofs are in the review."
}
destination = Path(__file__).with_name("W012-cap-width-review-certificates.json")
destination.write_text(json.dumps(output, indent=2)+"\n")
print(json.dumps(output, indent=2))
