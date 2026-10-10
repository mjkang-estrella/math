"""Record only ranges displayed by this helper; UTF-8 splitlines, LF join/no final LF hash."""
from pathlib import Path
import json,hashlib,sys
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i130_spectral_harmonic_discovery'
p=sys.argv[1]
if p.startswith('F:'): p='frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/build/sections/'+p[2:]+'.tex'
if p.startswith('L:'): p='frontier/sources/i124_fractal_incidence_discovery/literature/'+p[2:]+'.txt'
aliases={'H:': 'A-Three-Dimensional-Counterexample-to-Integer-Degree-Harmonic-Dimension-Comparison-September-26-2026/build/sections/', 'H0:': 'A-counterexample-to-integer-degree-harmonic-dimension-comparison-September-25-2026/build/sections/', 'N:': 'Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/build/sections/', 'P:': 'Power-law-violations-of-Yaus-nodal-upper-bound-September-23-2026/build/sections/', 'I:': 'Uniform-Interior-C1alpha-Estimates-for-Infinity-Harmonic-Functions-October-4-2026/build/manuscript/sections/', 'S:': 'Sharp-nodal-length-on-smooth-surfaces-September-23-2026/build/'}
for key,val in aliases.items():
 if p.startswith(key):p='frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints/'+val+p[len(key):]+'.tex';break
b=(ROOT/p).read_bytes();ls=b.decode().splitlines();a=int(sys.argv[2]) if len(sys.argv)>2 else 1;z=min(int(sys.argv[3]),len(ls)) if len(sys.argv)>3 else len(ls)
assert 1<=a<=z<=len(ls)
f=S/'read-manifest.json';d=json.loads(f.read_text()) if f.exists() else {'passages':[]}
h=lambda b:hashlib.sha256(b).hexdigest()
d['passages'].append(dict(local=p,file_sha256=h(b),start=a,end=z,line_count=len(ls),convention='splitlines',passage_sha256=h('\n'.join(ls[a-1:z]).encode())))
f.write_text(json.dumps(d,indent=2)+'\n')
print(p,a,z,'of',len(ls));print('\n'.join(f'{i}: {l}' for i,l in enumerate(ls[a-1:z],a)))
