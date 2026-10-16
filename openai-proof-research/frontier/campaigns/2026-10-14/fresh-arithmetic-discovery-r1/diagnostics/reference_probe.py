#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. MIT License; see ../RIGHTS.md.
"""Exploration only: float recursion, fixed w=2, no asymptotic certification."""
import json

primes = [p for p in range(2, 398)
          if all(p % d for d in range(2, int(p ** .5) + 1))]
rows = []
for z in [13, 19, 31, 43, 61, 97, 151, 251, 397]:
    w, height = 2, z ** 4
    available = [p for p in primes if w < p <= z]
    nodes = [0]

    def reference(d, j, parity):
        nodes[0] += 1
        value = 1.0
        for i in range(j):
            p = available[i]
            if parity == 0 or height * w ** (2 - .01) >= d * max(p ** 3, p * p * w * w):
                value -= 2 / p * reference(d * p, i, 1 - parity)
        return value

    value = reference(1, len(available), 0)
    rows.append({"z": z, "w": w, "height": height,
                 "reference_float": value, "nodes": nodes[0]})
print(json.dumps({"scope": "Float exploration only; no comparison to actual sieves or limit theorem.",
                  "rows": rows}, indent=2))
