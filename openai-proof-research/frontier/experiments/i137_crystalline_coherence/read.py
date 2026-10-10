"""Development reader. Records requested complete displays, not proof certification."""
from pathlib import Path
import sys,json,hashlib
ROOT=Path(__file__).resolve().parents[3];S=ROOT/'frontier/sources/i137_crystalline_coherence'
base='frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints/'
alias={'U':base+'Universal-optimality-of-the-triangular-lattice-September-23-2026/build/sections/','A':base+'An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/build/','C':base+'Triangular-minimality-for-planar-Coulomb-renormalized-energy-September-23-2026/build/sections/','K':base+'A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/build/sections/'}
p=sys.argv[1]
if ':' in p and p.split(':')[0] in alias:k,p=p.split(':',1);p=alias[k]+p
b=(ROOT/p).read_bytes();ls=b.decode().splitlines();st=int(sys.argv[2]) if len(sys.argv)>2 else 1;en=int(sys.argv[3]) if len(sys.argv)>3 else len(ls);assert 1<=st<=en<=len(ls)
t='\n'.join(ls[st-1:en]);assert len(t)<33000,('split read',len(t))
r={'path':p,'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b),'start':st,'end':en,'total_lines':len(ls),'passage_sha256':hashlib.sha256(t.encode()).hexdigest(),'ending':ls[en-1],'convention':'UTF-8 splitlines; joined LF; no appended LF'}
with (S/'reads.jsonl').open('a') as f:f.write(json.dumps(r,ensure_ascii=False)+'\n')
print(p,st,en,len(ls));print(t)
