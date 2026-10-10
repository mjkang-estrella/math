from pathlib import Path
import sys,json,hashlib
ROOT=Path.cwd(); S=ROOT/'frontier/sources/i133_fixed_metric_harmonic_growth'
p=sys.argv[1]
base='frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints/'
if p.startswith('h:'):p=base+'A-Three-Dimensional-Counterexample-to-Integer-Degree-Harmonic-Dimension-Comparison-September-26-2026/build/sections/'+p[2:]+'.tex'
if p.startswith('o:'):p=base+'A-counterexample-to-integer-degree-harmonic-dimension-comparison-September-25-2026/build/sections/'+p[2:]+'.tex'
b=(ROOT/p).read_bytes();ls=b.decode().splitlines();a=int(sys.argv[2]) if len(sys.argv)>2 else 1;z=min(int(sys.argv[3]),len(ls)) if len(sys.argv)>3 else len(ls)
assert 1<=a<=z<=len(ls)
f=S/'read-manifest.json';d=json.loads(f.read_text()) if f.exists() else {'passages':[]};sha=lambda b:hashlib.sha256(b).hexdigest()
d['passages'].append(dict(local=p,file_sha256=sha(b),start=a,end=z,line_count=len(ls),convention='splitlines',passage_sha256=sha('\n'.join(ls[a-1:z]).encode())))
f.write_text(json.dumps(d,indent=2)+'\n');print(p,a,z,'of',len(ls));print('\n'.join(f'{i}: {l}' for i,l in enumerate(ls[a-1:z],a)))
