#!/usr/bin/env python3
"""Exact finite coefficient regression, not a universal proof."""
from math import comb
from pathlib import Path
import json

def coefficients(n):
    # Coefficients of 4^n phi_n((1+t)/2), directly from its defining sum.
    c = [0] * (2*n+1)
    for k in range(n+1):
        for a in range(2*k+1):
            for b in range(2*(n-k)+1):
                c[a+b] += comb(n,k)**2 * comb(2*k,a) * comb(2*(n-k),b) * (-1)**b
    return c

checked = []
for n in range(33):
    actual = coefficients(n)
    expected = [0 if d % 2 else comb(d,d//2)*comb(2*n-d,n-d//2) for d in range(2*n+1)]
    assert actual == expected, (n, actual, expected)
    checked.append(n)
report = {'status':'PASS','method':'exact integer polynomial coefficients',
          'degrees_n_checked':checked,'n2_scaled_coefficients':coefficients(2),
          'qualification':'Finite regression only; the universal derivation is in paper/main.tex. The Lean convexity proof uses the fully proved finite Fourier identity instead.'}
Path('build/identity-check.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
