"""Pre-seal evidence capture; never run by verifier."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[3]; S=R/'frontier/sources/i81_diophantine_approximation_discovery'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(name,x):(S/name).write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
mapfile=R/'frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/search-domain.json';rows=json.loads(mapfile.read_text())
families=['Catalans-constant-is-irrational-September-24-2026','The-irrationality-exponent-of-pi-is-2-September-24-2026','Single-fold-Diophantine-representations-September-24-2026','The-weak-inhomogeneous-Duffin-Schaeffer-conjecture-September-25-2026','Hilberts-tenth-problem-over-the-rational-numbers-September-24-2026','Hilberts-tenth-problem-over-the-rational-numbers-October-6-2026']
relevant=[r for r in rows if r['path'].split('/')[1] in families];save('relevant-source-files.json',relevant)
root='frontier/sources/i14_spectral_width_novelty_r3/corpus'
r=subprocess.run(['rg','--files','--no-ignore',root],cwd=R,capture_output=True,text=True,check=True);(S/'corpus-inventory.txt').write_text('\n'.join(sorted(r.stdout.splitlines()))+'\n')
# Full exact lower-operation passage bindings, with line-based hashes.
C=f'{root}/preprints/{families[0]}/build/';P=f'{root}/preprints/{families[1]}/build/';F=f'{root}/preprints/{families[2]}/build/';D=f'{root}/preprints/{families[3]}/build/'
spans=[('C rows and entry',C+'sections/foundations.tex',1,277),('C two-adic dependence',C+'sections/foundations.tex',278,434),('C digit and two-layer operations',C+'sections/odd-primes.tex',1,508),('C finite-prime summation',C+'sections/odd-primes.tex',509,672),('C uniform rational nonvanishing',C+'sections/nonvanishing.tex',209,413),('C real-bound contract',C+'sections/certificate.tex',1,17),('C real supremum',C+'sections/real-place.tex',354,420),('C energy order of limits',C+'sections/energy.tex',240,288),('P interpolation quantifiers',P+'sections/interpolation.tex',1,57),('P eventual sheaf operations',P+'sections/interpolation.tex',475,580),('P order of parameters',P+'sections/conclusion.tex',1,203),('S representation and fixed constants',F+'main.tex',42,157),('S elliptic heights and square window',F+'elliptic.tex',159,410),('S first halt and unique base',F+'computation.tex',282,343),('S complete witness ledger',F+'witness-ledger.tex',1,160),('S undecidability scope',F+'consequences.tex',1,43),('D theorem quantifiers',D+'sections/introduction.tex',1,65),('D weighted variance',D+'sections/tables.tex',478,534),('D virtual marginal scope',D+'sections/tables.tex',690,727),('D finite-block transfer',D+'sections/tables.tex',911,1047),('Eskandari actual theorem','frontier/sources/i81_diophantine_approximation_discovery/primary/eskandari-v1.pdf.txt',52,146),('Zudilin determinant criterion','frontier/sources/i81_diophantine_approximation_discovery/primary/zudilin-v2.pdf.txt',20,119),('CDT holonomy prerequisites','frontier/sources/i81_diophantine_approximation_discovery/primary/cdt-icm.pdf.txt',280,363),('CDT conductor three','frontier/sources/i81_diophantine_approximation_discovery/primary/cdt-icm.pdf.txt',1026,1054),('CDT real Catalan extra period','frontier/sources/i81_diophantine_approximation_discovery/primary/cdt-icm.pdf.txt',1210,1258)]
passages=[]
for label,path,lo,hi in spans:
 lines=(R/path).read_bytes().splitlines(keepends=True)
 # Bound to existing lines, record actual endpoint rather than fabricate text.
 hi=min(hi,len(lines));assert 0<lo<=hi
 data=b''.join(lines[lo-1:hi]);passages.append(dict(label=label,path=path,first=lo,last=hi,sha256=hashlib.sha256(data).hexdigest()))
save('passages.json',passages)
# Immutable references: manifests plus the fixed historical search domain; complete blob bodies checked via those manifests.
refs={str(mapfile.relative_to(R)),'frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/outside-requests.jsonl','sources/preprints-tree.json','sources/upstream.json','sources/CONTENTS.md','AGENTS.md'}
for j in ['history-search-domain.json','history-search-v2.json']:
 for p in json.loads((S/j).read_text())['files']:
  if p not in ['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'] and not p.startswith(str(S.relative_to(R))):refs.add(p)
save('immutable-references.json',[dict(path=p,sha256=digest(R/p),bytes=(R/p).stat().st_size) for p in sorted(refs)])
save('discovery-scope.json',{'pinned_commit':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','tree_counts':{'entries':13223,'manuscripts':749,'blobs':10373},'title_pattern':r'Catalan|irrationality|Diophantine|approximation|transcenden|effective|Baker|abc-|ABC-|Pell|Roth|Littlewood|Schmidt|Schanuel|zeta|Zeta','title_flags':'case insensitive','relevant_families':families,'external_search_queries':['Catalan constant irrationality measure determinant rational approximations Zudilin 2017','Catalan constant irrationality linear independence 2026 Calegari Dimitrov Tang'],'external_search_limit':'Two discovery queries; primary response bodies and version records retained. Nonprimary hits were leads only; no exhaustiveness or priority claim.','pdf_visual_checks':[{'path':'primary/eskandari-v1.pdf','page':2,'render':'primary/eskandari-theorem.png'},{'path':'primary/cdt-icm.pdf','page':17,'render':'primary/cdt-catalan.png'}]})
print(json.dumps({'relevant_files':len(relevant),'passages':len(passages),'immutable_references':len(refs),'corpus_files':len(r.stdout.splitlines())}))
