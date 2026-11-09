#!/usr/bin/env python3
"""Read-only: unified diff of the section starting at a marker up to the next \\section, between two files.
Usage: secdiff.py FILE1 FILE2 MARKER"""
import difflib, sys

def sec(p, marker):
    L = open(p, encoding='utf-8', errors='replace').read().split('\n')
    i = next(k for k, l in enumerate(L) if marker in l)
    j = next(k for k in range(i + 1, len(L)) if L[k].startswith('\\section'))
    return [l.rstrip() for l in L[i:j]], i + 1, j

a, ia, ja = sec(sys.argv[1], sys.argv[3])
b, ib, jb = sec(sys.argv[2], sys.argv[3])
print(f'{sys.argv[1]} lines {ia}-{ja}; {sys.argv[2]} lines {ib}-{jb}')
d = list(difflib.unified_diff(a, b, lineterm='', n=1))
print('\n'.join(d) if d else 'IDENTICAL (modulo trailing whitespace)')
