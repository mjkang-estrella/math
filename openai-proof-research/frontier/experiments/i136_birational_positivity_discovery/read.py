from pathlib import Path
import sys,json,hashlib
R=Path.cwd();S=R/'frontier/sources/i136_birational_positivity_discovery';base='frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints/'
a={'f':'Fujitas-freeness-conjecture-September-23-2026/build/','n':'Nagatas-Conjecture-for-Plane-Curves-September-23-2026/build/','s':'Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/build/','h':'Maximal-Multipoint-Seshadri-Constants-in-Higher-Dimensions-October-5-2026/build/','p':'Maximal-multipoint-Seshadri-constants-in-positive-characteristic-October-5-2026/build/build/','c':'Bounded-klt-complements-for-Fano-contractions-September-25-2026/build/','u':'Uniform-Cartier-sections-for-Fano-type-contractions-September-25-2026/build/'}
p=sys.argv[1]
if ':' in p and p.split(':',1)[0] in a:
 k,rest=p.split(':',1);p=base+a[k]+rest
b=(R/p).read_bytes();lines=b.decode().splitlines();start=int(sys.argv[2]) if len(sys.argv)>2 else 1;end=min(int(sys.argv[3]),len(lines)) if len(sys.argv)>3 else len(lines)
sha=lambda b:hashlib.sha256(b).hexdigest();m=S/'read-manifest.json';d=json.loads(m.read_text()) if m.exists() else {'passages':[]}
d['passages'].append({'local':p,'start':start,'end':end,'line_count':len(lines),'file_sha256':sha(b),'convention':'splitlines','passage_sha256':sha('\n'.join(lines[start-1:end]).encode())});m.write_text(json.dumps(d,indent=2)+'\n');print(p,start,end,'/',len(lines));print('\n'.join(f'{i}: {l}' for i,l in enumerate(lines[start-1:end],start)))
