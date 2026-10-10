"""One-time reading/capture index, not invoked during verification."""
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i89_geometric_group_discovery'
D=json.loads((R/'frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/search-domain.json').read_text())
records=[]
def add(prefix,suffix,start=1,end=None,note='complete indicated body'):
 matches=[d for d in D if d['path'].split('/')[1].startswith(prefix) and d['path'].endswith(suffix) and d['kind']=='corpus']
 assert len(matches)==1,(prefix,suffix,len(matches));d=matches[0];p=d['local'];b=(R/p).read_bytes();ls=b.decode().splitlines(keepends=True);end=end or len(ls);assert 1<=start<=end<=len(ls),(prefix,suffix,start,end,len(ls));txt=''.join(ls[start-1:end])
 records.append({'label':prefix+':'+suffix+':'+str(start)+'-'+str(end),'path':d['path'],'local':p,'start':start,'end':end,'source_sha256':hashlib.sha256(b).hexdigest(),'sha256':hashlib.sha256(txt.encode()).hexdigest(),'text':txt,'scope':note})
for name in ['01-introduction','02-model','03-diagrams','04-sampling','05-energy','06-obstruction','07-completion']:
 add('A-hyperbolic-group-with-no','/sections/'+name+'.tex')
add('a-torsion-free-hyperbolic','/build/paper.tex')
add('a-torsion-free-hyperbolic','/sections/construction.tex')
add('a-torsion-free-hyperbolic','/sections/geometry-foundations.tex')
add('Baumslag-Solitar-free','/introduction.tex')
add('Baumslag-Solitar-free','/preliminaries.tex',1,137)
add('Baumslag-Solitar-free','/annuli.tex',1,299)
add('Baumslag-Solitar-free','/carriers.tex',1,350)
add('Baumslag-Solitar-free','/rays.tex')
add('Virtual-compact-specialness','/sections/00-introduction.tex')
add('Virtual-compact-specialness','/sections/11-free-by-cyclic.tex')
add('Virtual-compact-specialness','/sections/01-filling.tex',1,124,'theorem, setup and selective-hyperbolicity statement; remainder not claimed read')
add('Virtual-compact-specialness','/sections/07-transfer.tex',364,713,'finite tests, induced fillings, exact intersection, complete finite-path transfer and projection consequences')
add('Finite-algebraic-envelopes','/introduction.tex')
add('Finite-algebraic-envelopes','/reduction.tex')
add('Finite-algebraic-envelopes','/action.tex')
add('Finite-algebraic-envelopes','/compiler.tex',1,145,'compiler interface and initial syntactic operation, not complete appendix')
add('Simple-F-infinity','/sections/introduction.tex',1,180)
add('An-Artin-group-with-no','/sections/introduction.tex')
add('A-universal-group-of-type','/build/main.tex',note='complete main file (abstract/outline and section inclusion directives); included proof files not claimed read')
for name,lo,hi in [('kondo',348,442),('gromov',2030,2150),('ikn',270,303),('ikn',660,698),('lcm',278,366),('vcs-growth',30,77),('vcs-growth',107,180)]:
 p='frontier/sources/i89_geometric_group_discovery/primary/'+name+'.txt';b=(R/p).read_bytes();ls=b.decode().splitlines(keepends=True);txt=''.join(ls[lo-1:hi]);records.append({'label':'primary:'+name+':'+str(lo)+'-'+str(hi),'local':p,'start':lo,'end':hi,'source_sha256':hashlib.sha256(b).hexdigest(),'sha256':hashlib.sha256(txt.encode()).hexdigest(),'text':txt,'scope':'actual indicated primary passage; full PDF retained'})
(S/'passages.json').write_text(json.dumps(records,indent=2,ensure_ascii=False)+'\n')
# Broaden binding of selected source representations; no new copying or fetch.
sel=json.loads((S/'selected-domain.json').read_text());paths={d['path'] for d in sel}
sel += [d for d in D if d['path'].split('/')[1].startswith('A-universal-group-of-type') and d['path'] not in paths]
(S/'selected-domain.json').write_text(json.dumps(sel,indent=2)+'\n')
print(json.dumps({'passages':len(records),'selected_records':len(sel)}))
