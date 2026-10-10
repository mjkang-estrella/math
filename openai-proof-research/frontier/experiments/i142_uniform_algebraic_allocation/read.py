from pathlib import Path
import sys,json,hashlib
R=Path.cwd(); S=R/'frontier/sources/i142_uniform_algebraic_allocation'
assert not (S/'seal.json').exists(), 'No postseal edits'
base='frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints/'
a={'h':'Maximal-Multipoint-Seshadri-Constants-in-Higher-Dimensions-October-5-2026/build/sections/','p':'Maximal-multipoint-Seshadri-constants-in-positive-characteristic-October-5-2026/build/build/sections/','u':'Uniform-Cartier-sections-for-Fano-type-contractions-September-25-2026/build/sections/'}
p=sys.argv[1]
if ':' in p and p.split(':')[0] in a:
 k,v=p.split(':',1);p=base+a[k]+v
b=(R/p).read_bytes();ls=b.decode().splitlines();lo=int(sys.argv[2]) if len(sys.argv)>2 else 1;hi=min(int(sys.argv[3]),len(ls)) if len(sys.argv)>3 else len(ls)
h=lambda b:hashlib.sha256(b).hexdigest();mp=S/'read-manifest.json';m=json.loads(mp.read_text()) if mp.exists() else {'passages':[]}
m['passages'].append(dict(local=p,start=lo,end=hi,line_count=len(ls),file_sha256=h(b),passage_sha256=h('\n'.join(ls[lo-1:hi]).encode()),ending=ls[hi-1],convention='splitlines; LF joined without appended LF'));mp.write_text(json.dumps(m,indent=2)+'\n')
print(p,lo,hi,'/',len(ls));print('\n'.join(f'{i}: {l}' for i,l in enumerate(ls[lo-1:hi],lo)))
