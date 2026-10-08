#!/usr/bin/env python3
"""Finite regression for an UNVERIFIED historical prototype, not a repaired solver.
Proves no general formal-group theorem. It exhibits two valid projective points
whose prototype additions disagree under operand reversal, contradicting the
commutativity required of elliptic-curve addition.
"""
import contextlib
import importlib.util
import io
import json
from pathlib import Path

source = Path(__file__).with_name('W019-smart-original-unverified.py')
spec = importlib.util.spec_from_file_location('historical_smart', source)
prototype = importlib.util.module_from_spec(spec)
with contextlib.redirect_stdout(io.StringIO()):
    spec.loader.exec_module(prototype)
import_demo_counter = prototype.OPS['point_add']
prototype.OPS['point_add'] = 0

p, a, b = 43, 4, 2
modulus = p * p
left, right = (1, 1, p), (1, 1, 2*p)
assert (4*a**3+27*b**2) % p != 0

def normalized_projective(point):
    X, Y, Z = point
    assert (Y*Y-X**3-a*X*Z**4-b*Z**6) % modulus == 0
    assert Y % p != 0
    # Jacobian to ordinary projective (XZ:Y:Z^3), then normalize unit Y to1.
    yinverse = pow(Y, -1, modulus)
    x, z = X*Z*yinverse % modulus, Z**3*yinverse % modulus
    assert (z-x**3-a*x*z*z-b*z**3) % modulus == 0
    return (x, 1, z)

inputs = [normalized_projective(left), normalized_projective(right)]
assert inputs == [(43, 1, 0), (86, 1, 0)]
lr = prototype.jac_add(left, right, a, modulus)
rl = prototype.jac_add(right, left, a, modulus)
outputs = [normalized_projective(lr), normalized_projective(rl)]
assert outputs == [(86, 1, 0), (172, 1, 0)]
assert outputs[0] != outputs[1]
print(json.dumps({
    'scope': 'Finite noncommutativity counterexample for historical jac_add over Z/43^2',
    'curve_a_b': [a, b], 'modulus': modulus,
    'input_normalized_projective': inputs,
    'output_lr_rl_normalized_projective': outputs,
    'prototype_counter_for_four_add_double_calls': prototype.OPS['point_add'],
    'separate_import_demo_mixed_counter': import_demo_counter,
    'verdict': 'FAIL as general elliptic-curve addition: distinct results on swapped inputs',
}, indent=2))
