"""One-time pre-seal evidence indexing. Does not seal. Not invoked by verification."""
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i83_catalan_finite_measure'
def sha(b):return hashlib.sha256(b).hexdigest()
def dump(name,v):(S/name).write_text(json.dumps(v,indent=2,sort_keys=True)+'\n')
refs=set(['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json','frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/search-domain.json','frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/outside-requests.jsonl','frontier/iterations/i81-diophantine-approximation-discovery.md','frontier/experiments/i81-parent-verification.json'])
for base in ['frontier/sources/i81_diophantine_approximation_discovery','frontier/experiments/i81_diophantine_approximation_discovery']:
 refs.update(str(p.relative_to(R)) for p in (R/base).rglob('*') if p.is_file())
hist=json.loads((S/'history-search-definition.json').read_text())
refs.update(p for p in hist['files'] if not p.startswith(str(S.relative_to(R))))
rows=json.loads((R/'frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/search-domain.json').read_text())
families=['Catalans-constant-is-irrational-September-24-2026','The-irrationality-exponent-of-pi-is-2-September-24-2026','Elliptic-Squares-and-Zilber-Pink-for-Curves-in-A2-September-24-2026','Quaternionic-Division-Points-on-Curves-in-the-Siegel-Threefold-September-24-2026','The-E-times-CM-Component-of-Zilber-Pink-for-Curves-in-A2-September-24-2026']
selected=[r for r in rows if r['path'].split('/')[1] in families];dump('selected-full-companions.json',{'families':families,'files':selected});refs.update(x['local'] for x in selected)
C='frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints/'+families[0]+'/build/sections/'
P='frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints/'+families[1]+'/build/sections/'
I='frontier/sources/i81_diophantine_approximation_discovery/primary/'
N=str(S.relative_to(R))+'/primary/'
passages=[]
def passage(label,path,first,last):
 b=(R/path).read_bytes();lines=b.split(b'\n');assert 1<=first<=last<=len(lines),(path,len(lines),last)
 data=b'\n'.join(lines[first-1:last]);passages.append({'label':label,'path':path,'first':first,'last':last,'line_convention':'split on LF; join selected records with LF, no added final LF','sha256':sha(data)})
 if not path.startswith(str(S.relative_to(R))):refs.add(path)
for label,f,a,b in [('rows and affine entries','foundations.tex',1,268),('uniform two-adic dependence','foundations.tex',279,434),('large primes parameter integrality','odd-primes.tex',1,67),('two layers and local elimination','odd-primes.tex',245,509),('coarse bad-prime budget and weighted PNT','odd-primes.tex',509,620),('prime nonvanishing assumptions','nonvanishing.tex',1,80),('Frobenius and vanished rational parameter','nonvanishing.tex',98,245),('fixed determinant and prime completion','nonvanishing.tex',250,413),('real sheets and signed matrix','real-place.tex',1,117),('real interpolation and Hadamard scope','real-place.tex',240,358),('energy statement and order of limits','energy.tex',1, 60),('energy uniform limiting step','energy.tex',245,296),('certified gap','certificate.tex',1,17),('qualitative scope and companions','introduction.tex',1,216),('printed consequences','conclusion.tex',1,56)]:
 passage('C: '+label,C+f,a,b)
for label,f,a,b in [('separated-weight exact hypotheses','interpolation.tex',1,60),('logarithmic centers','determinant.tex',1,95),('final fixed-center degree limit','conclusion.tex',68,200),('already printed series corollary','series.tex',90,166)]:passage('P: '+label,P+f,a,b)
for label,f,a,b in [('determinant criterion','zudilin-v2.pdf.txt',25,155),('Catalan denominator obstruction','zudilin-v2.pdf.txt',332,430),('Eskandari construction','eskandari-v1.pdf.txt',67,303),('Eskandari rates and final interpretation','eskandari-v1.pdf.txt',305,578),('ICM real extra period','cdt-icm.pdf.txt',1220,1255)]:passage(label,I+f,a,b)
for label,f,a,b in [('CDT exact main theorem','cdt-v2.pdf.txt',850,926),('CDT functional zero prerequisite','cdt-v2.pdf.txt',3045,3129),('CDT conductor-three and Catalan interfaces','cdt-v2.pdf.txt',10190,10340),('CDT quantitative work still required','cdt-v2.pdf.txt',12082,12102),('Brown numerator scope','brown.pdf.txt',315,335),('Brown genuine integer-form extraction','brown.pdf.txt',1410,1565),('Sun fixed rational denominator comparison','catalan-new.pdf.txt',1030,1112),('2002 recurrence normalization lead only','zudilin-rec.pdf.txt',83,160)]:passage(label,N+f,a,b)
for family,a,b,label in [(families[2],320,510,'elliptic-square exact interpolation interface'),(families[3],535,630,'quaternionic exact interpolation interface'),(families[4],1,105,'E times CM exact target')]:
 x=next(x for x in selected if x['path'].split('/')[1]==family and x['kind']=='outside_pdf');passage(label,x['local'],a,b)
dump('passages.json',passages)
dump('immutable-references.json',[{'path':p,'sha256':sha((R/p).read_bytes()),'bytes':(R/p).stat().st_size} for p in sorted(refs)])
versions=[]
for p in sorted((S/'primary').glob('*record.html')):
 txt=p.read_text();found=sorted(set(re.findall(r'(?:2408\.15403|2609\.26354|1507\.05697|2604\.20741|2609\.04176|math/0201024)v\d+',txt)))
 versions.append({'path':str(p.relative_to(R)),'versions':found})
dump('versions.json',versions)
dump('read-scope.json',{'primary_scope':'Actual relevant pages and prerequisites in passages.json; not all 218 CDT pages. Full Eskandari construction and Zudilin determinant criterion. Full primary bodies retained. No source sign correction asserted.','visual_checks':[{'pdf':N+'cdt-v2.pdf','page':164,'png':N+'cdt-p164.png'},{'pdf':N+'brown.pdf','page':21,'png':N+'brown-p21.png'},{'pdf':I+'eskandari-v1.pdf','page':6,'png':N+'eskandari-p6.png'},{'pdf':I+'cdt-icm.pdf','page':17,'png':I+'cdt-catalan.png'}],'reused_complete_domain':'I79 search-domain.json; full coverage and original outside Git hashes replayed via bound I81 verifier','mutable_ledgers':['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']})
print(json.dumps({'references':len(refs),'passages':len(passages),'full_companion_files':len(selected),'versions':versions},indent=2))
