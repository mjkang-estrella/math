"""Historical evidence capture; not a verifier and never called by one."""
from pathlib import Path
import json,hashlib,re
R=Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i96_finite_cat0_obstruction_novelty_r3'
assert not (S/'seal-v1.json').exists()
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,x):(S/n).write_text(json.dumps(x,sort_keys=True,indent=2)+'\n')
refs=set();passages=[]
def add(n,start=1,end=None,scope='complete operative body'):
 p=R/n;b=p.read_bytes();ls=b.decode().splitlines(keepends=True);end=end or len(ls)
 assert 1<=start<=end<=len(ls),(n,start,end,len(ls))
 s=''.join(ls[start-1:end]);refs.add(n)
 passages.append({'path':n,'start':start,'end':end,'source_sha256':sha(b),'passage_sha256':sha(s.encode()),'line_convention':'str.splitlines(keepends=True)','scope':scope,'labels':re.findall(r'\\label\{([^}]+)\}',s)})
C='frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints/'
A=C+'A-hyperbolic-group-with-no-geometric-CAT0-action-September-25-2026/build/sections/'
for f in ['01-introduction.tex','02-model.tex','04-sampling.tex','05-energy.tex','06-obstruction.tex','07-completion.tex']:add(A+f)
ART=C+'An-Artin-group-with-no-geometric-CAT-0-action-September-23-2026/build/sections/'
for f in ['introduction.tex','lengths.tex','sectors.tex','assembly.tex']:add(ART+f)
FIL=C+'Sharp-integral-fillings-in-CAT(0)-spaces-September-23-2026/build/sections/'
add(FIL+'01-introduction.tex',1,110,'main theorem and hypotheses')
add(FIL+'07-conclusion.tex')
CH=C+'Generalized-Cartan-Hadamard-isoperimetry-and-Euclidean-equality-rigidity-September-23-2026/build/sections/'
add(CH+'01-introduction.tex',1,110,'main and equality theorem hypotheses')
add(CH+'08-rigidity.tex')
TH=C+'A-Three-Manifold-Without-Conjugate-Points-and-Without-a-Nonpositively-Curved-Metric-September-24-2026/build/sections/topology.tex'
add(TH)
for n in ['frontier/iterations/i89-geometric-group-discovery.md','frontier/iterations/i91-finite-cat0-obstruction.md','frontier/experiments/i91_finite_cat0_obstruction/algebraic.py','frontier/experiments/i91_finite_cat0_obstruction/checks.py','frontier/experiments/i91_finite_cat0_obstruction/template.py','frontier/experiments/i91_finite_cat0_obstruction/verify.py']:add(n,scope='complete original report/code; integrity and contribution review, not I95 proof verdict')
P='frontier/sources/i96_finite_cat0_obstruction_novelty_r3/primary/'
for f,rs in {'ann.txt':[(300,360),(1457,1630),(2022,2325)],'kn.txt':[(1,359)],'sturm.txt':[(374,478),(1026,1230),(1250,1357)],'bridson.txt':[(1060,1145)],'toyoda-six.txt':[(1,461)],'toyoda-ann.txt':[(1,963)],'proximal.txt':[(260,634)],'toyoda-fixed.txt':[(1,180),(409,582)]}.items():
 for a,b in rs:add(P+f,a,b,'full used statement/proof operation within stated range; not entire paper unless range covers it')
OLD='frontier/sources/i89_geometric_group_discovery/primary/'
for f,rs in {'gromov.txt':[(1970,2180)],'kondo.txt':[(348,445)],'ikn.txt':[(258,360),(605,741)]}.items():
 for a,b in rs:add(OLD+f,a,b,'used energy/scaling operation and its displayed proof')
add('frontier/sources/i91_finite_cat0_obstruction/primary/berg-nikolaev.txt',26,90,'K=0 formula; not an assertion of full 2008 article reading')
for n in ['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json','frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/search-domain.json','frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/outside-requests.jsonl','frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/seal-v1.json','frontier/experiments/i89-parent-verification.json','frontier/experiments/i91-parent-verification.json']:refs.add(n)
# Bind every original I89/I91 owned byte by their immutable original manifests;
# historical verdicts remain unchanged. No active review or working output is used.
for lane in ['i89_geometric_group_discovery','i91_finite_cat0_obstruction']:
 q='frontier/sources/'+lane+'/seal-v1.json';refs.add(q);refs.add(q.replace('.json','.sha256'))
 seal=json.loads((R/q).read_text());refs.update(seal['files'] if isinstance(seal['files'],dict) else (d['path'] for d in seal['files']))
D=json.loads((R/'frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/search-domain.json').read_text())
families={n[len(C):].split('/')[0] for n in refs if n.startswith(C)}
selected=[d for d in D if d['path'].split('/')[1] in families]
refs.update(d['local'] for d in selected)
pdfs=[]
for d in selected:
 if d['kind']=='outside_pdf':
  # I79 retains extraction beside the original PDF.
  p=d['local'][:-4] if d['local'].endswith('.pdf.txt') else None
  assert p and (R/p).read_bytes().startswith(b'%PDF'),d
  refs.add(p);pdfs.append({'pdf':p,'text':d['local']})
save('selected-representatives.json',sorted(selected,key=lambda x:x['path']))
save('selected-pdf-replays.json',sorted(pdfs,key=lambda x:x['pdf']))
save('passages.json',sorted(passages,key=lambda x:(x['path'],x['start'],x['end'])))
save('immutable-references.json',[{'path':n,'sha256':sha((R/n).read_bytes()),'bytes':(R/n).stat().st_size} for n in sorted(refs) if not n.startswith('frontier/sources/i96_')])
versions=[]
for p in sorted((S/'primary').glob('*.html')):
 t=p.read_text();versions.append({'path':p.relative_to(R).as_posix(),'submitted_line':re.findall(r'\[Submitted on[^\n]+',t),'history':re.findall(r'.{0,40}\[v\d+\].{0,100}',t)})
save('primary/versions.json',versions)
print(json.dumps({'passages':len(passages),'references':len(refs),'selected':len(selected),'pdfs':len(pdfs)}))
