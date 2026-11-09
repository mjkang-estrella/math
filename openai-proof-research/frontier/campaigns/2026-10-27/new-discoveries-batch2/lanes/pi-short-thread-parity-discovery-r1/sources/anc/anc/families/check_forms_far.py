#!/usr/bin/env python3
"""
Sanity check (not part of any proof): compare the closed forms written by certify_gen.py
(forms/forms_x_y.txt, valid for all r by Lemmas 9.8/9.9) with the independent positional
C++ solver famstates.cpp far beyond the certified range, r <= R (default 600).
Usage: python3 check_forms_far.py R x1 y1 x2 y2 ...
"""
import re, subprocess, sys, ast

R = int(sys.argv[1])
pairs = [(int(sys.argv[i]), int(sys.argv[i + 1])) for i in range(2, len(sys.argv), 2)]
FS = {'F': '*', 'T': 'I', 'A': 'O'}


def parse_forms(fn):
    forms = {}
    for L in open(fn):
        if L.startswith('#'):
            continue
        m = re.match(r'(\w)\{([^}]*)\}\s+phi=(\w) type=(\w) slope=(\d) r0=(\d+)\s+q=(\[[^\]]*\]) init=(\[[^\]]*\])', L)
        s, legs, phi, typ, slope, r0, q, init = m.groups()
        K = tuple(sorted((int(t[:-1]), t[-1]) for t in legs.split(',') if t))
        forms[((s, K), phi)] = (int(slope), int(r0), ast.literal_eval(q), ast.literal_eval(init))
    return forms


def closed(f, r):
    slope, r0, q, init = f
    if r < r0:
        return init[r - 1]
    return slope * r + q[r % len(q)]


for (x, y) in pairs:
    forms = parse_forms('forms/forms_%d_%d.txt' % (x, y))
    out = subprocess.run(['./famstates', str(x), str(y), str(R)], capture_output=True, text=True).stdout
    n = bad = 0
    for L in out.strip().split('\n'):
        head, vals = L.split(':')
        lab, a, b, f = head.split()
        if f == 'F':
            continue
        K = tuple(sorted((int(t[:-1]), FS[t[-1]]) for t in (a, b) if t != '-'))
        key = (({'N': 'n', 'I': 'i', 'O': 'o'}[lab], K), FS[f])
        for r, v in enumerate(map(int, vals.split()), 1):
            n += 1
            if closed(forms[key], r) != v:
                bad += 1
    print((x, y), 'blocked values compared up to r=%d:' % R, n, 'mismatches:', bad, flush=True)
