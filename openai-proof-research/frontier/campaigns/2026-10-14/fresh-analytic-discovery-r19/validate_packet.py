"""RF receipt, exact-exponent, and local-detour diagnostics; not a proof checker.
Myeongjin Kang, no affiliation. SPDX-License-Identifier: MIT
"""
from fractions import Fraction as F
from hashlib import sha1, sha256
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent

def digest(path):
    return sha256(path.read_bytes()).hexdigest()

assert digest(ROOT / 'original-scope.md') == 'e40f0169ee9c301474c7f255ea129e311f001990786c338862e884dddf756e8f'
assert digest(ROOT / 'screening-before-freeze.md') == '4e0e395169df4c0ab8b6c4cfe3643a1fb26e1068bd9a8c1498b476baa0c3cc12'
receipts = json.loads((ROOT / 'source-receipt.json').read_text())
receipts += [json.loads((ROOT / 'companion-check-receipt.json').read_text())]
for row in receipts:
    b = (ROOT / row['local']).read_bytes()
    assert len(b) == row['bytes']
    assert sha256(b).hexdigest() == row['sha256']
    assert sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest() == row['git_blob']
print(f'Pinned receipts: {len(receipts)} exact byte/SHA256/Git-blob matches.')
for row in json.loads((ROOT / 'primary-receipt.json').read_text()):
    for item in row['local_files']:
        p = ROOT / item['path']
        assert p.stat().st_size == item['bytes'] and digest(p) == item['sha256']
print('Primary PDF/text receipts: 6 exact matches.')

lo, hi, tiny = F(501, 1000), F(51, 100), F(1, 20)
exponents = {
    'M lower': 3*lo-F(3,2),
    'M upper': 3*hi-F(3,2),
    'E0 L^2 lower': 5*lo-F(5,2),
    'upper interaction': 22*hi-F(23,2)+2*tiny,
    'tiny-field deficit': 3*hi-F(3,2)-tiny,
    'tiny-field free shift': hi-F(1,2)-tiny,
    'local density upper': -1+tiny-lo,
    'projection loss upper': 3*hi+2*(-1+tiny-lo),
    'trial interaction upper': 1+3*hi+2*(-1+tiny-lo),
    'zero occupation upper': 2*hi-1+tiny,
}
expected = [F(3,1000), F(3,100), F(5,1000), F(-18,100), F(-2,100), F(-4,100), F(-1451,1000), F(-1372,1000), F(-372,1000), F(7,100)]
assert list(exponents.values()) == expected
print('Exact exponent diagnostics:', {k: str(v) for k,v in exponents.items()})

unit = [tuple(s if i == j else 0 for i in range(3)) for j in range(3) for s in (-1, 1)]
z = (0,0,0)

def add(x, y): return tuple(a+b for a,b in zip(x,y))
def neg(x): return tuple(-a for a in x)
def dot(x, y): return sum(a*b for a,b in zip(x,y))
def path_A(e, f):
    if e == f: return [(z,e)]
    if f == neg(e):
        q = next(q for q in unit if dot(q,e) == 0)
        return path_A(e,q) + path_A(q,f)[1:]
    return [(z,e), (z,add(e,f)), (z,f)]
def path_AB(e):
    q = next(q for q in unit if dot(q,e) == 0)
    return [(z,e), (q,e), (q,z), (add(q,e),z), (e,z)]
def path_between(a, b):
    # Nodes are ('A' or 'B', direction).
    ta,e = a; tb,f = b
    p = list(reversed(path_AB(e))) if ta == 'B' else [(z,e)]
    p += path_A(e,f)[1:]
    if tb == 'B': p += path_AB(f)[1:]
    return p
nodes = [(t,e) for t in ('A','B') for e in unit]
count = 0
for L in (4,6,8):
    for x in nodes:
        for y in nodes:
            path = [tuple(tuple(c % L for c in v) for v in pair) for pair in path_between(x,y)]
            assert all(a != b for a,b in path)
            for p,q in zip(path,path[1:]):
                diffs = [(v-u) % L for a,b in zip(p,q) for u,v in zip(a,b)]
                assert sum(d != 0 for d in diffs) == 1
                assert next(d for d in diffs if d) in (1,L-1)
            assert len(path)-1 <= 12
            count += 1
print(f'Local detour diagnostics: {count} ordered paths, no collisions, valid edges, length <=12.')

manifest = ROOT / 'sealed-manifest.json'
if manifest.exists():
    rows = json.loads(manifest.read_text())['files']
    for row in rows:
        p = ROOT / row['path']
        assert p.stat().st_size == row['bytes'] and digest(p) == row['sha256'], row['path']
    print(f'Sealed manifest: {len(rows)} file hashes match.')
print('Diagnostics complete. Mathematical proof and contribution verdicts remain independent.')
