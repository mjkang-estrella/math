"""Author-only flat evidence assembly. No ancestor execution, extraction, or corpus copy."""
from pathlib import Path
import json,hashlib,re,bisect
S=Path('frontier/sources/i153_many_body_spectral_discovery');X=Path('frontier/experiments/i153_many_body_spectral_discovery');OLD=Path('frontier/sources/i150_near_critical_crossing_circuit_bounds')
MUTABLE={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
assert not (S/'seal.json').exists()
def load(p):return json.loads(Path(p).read_bytes())
def save(n,z):(S/n).write_text(json.dumps(z,ensure_ascii=False,indent=2)+'\n')
def row(p):
 b=Path(p).read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
refs={r['path']:r for r in load(OLD/'references.json')}
def add(p):
 p=str(p);assert not re.search(r'(?:^|/)(?:i|iteration)(?:151|152)(?:[-_/])',p),p
 if p.startswith(str(S)+'/') or p.startswith(str(X)+'/'):return
 assert p not in MUTABLE
 r=row(p)
 if p in refs:assert refs[p]['sha256']==r['sha256'],p
 refs[p]=r
packs=load(OLD/'inherited-packages.json')+[dict(source=str(OLD),experiment='frontier/experiments/i150_near_critical_crossing_circuit_bounds',report='frontier/iterations/i150-near-critical-crossing-circuit-bounds.md',seal=row(OLD/'seal.json'))]
for pack in packs:
 add(pack['seal']['path'])
 for r in load(pack['seal']['path'])['files']:add(r['path'])
for c in load(S/'contexts.json'):add(c['raw']);add(c['snapshot'])
for r in load(S/'snapshots.json'):
 if r['path'] not in MUTABLE:add(r['path'])
reads=load(S/'read-manifest.json')
coverage={}
for r in reads:
 add(r['path']);t=Path(r['path']).read_text();a,b=r['char_start'],r['char_end'];starts=[];pos=0
 for line in t.splitlines(keepends=True):starts.append(pos);pos+=len(line)
 r.update(start_line=t[:a].count('\n')+1,end_line=t[:b].count('\n')+1,splitlines_start=bisect.bisect_right(starts,a),splitlines_end=bisect.bisect_right(starts,max(a,b-1)))
 if r['display_status']=='supplied':coverage.setdefault(r['path'],[]).append((a,b))
save('read-manifest.json',reads)
cv=[]
for p,intervals in sorted(coverage.items()):
 merged=[]
 for a,b in sorted(intervals):
  if merged and a<=merged[-1][1]:merged[-1][1]=max(b,merged[-1][1])
  else:merged.append([a,b])
 n=len(Path(p).read_text());cv.append(dict(path=p,supplied_ranges=merged,characters=n,full_supplied=merged==[[0,n]],semantic_scope='Supplied displays; hash coverage alone is not reading'))
save('coverage.json',cv)
for n in ['overlap-query.json','overlap-query-2.json']:
 q=load(S/n)
 for p in q.get('paths',q.get('files',[])):add(p)
source=sorted({r['path'] for r in reads if r['path'].endswith('.tex') or r['path'].endswith('.txt') and ('/external/' in r['path'] or '/outside/preprints/' in r['path'])})
pattern=r'localization|Fourier|Dirichlet|Gaussian|conditional|noise|sensitivity|four.arm|mixing|boundary|critical|finite.energy|pivotal|reflection|Laughlin|Fock|adiabatic|gap|spectr\w*|count\w*|depletion|condens\w*|Palm|normaliz\w*|gauge|domain|channel|Spin\(9\)|supersymmetr\w*'
rx=re.compile(pattern,re.I);out=[]
for p in source:
 add(p);t=Path(p).read_text();offset=0
 for no,line in enumerate(t.splitlines(keepends=True),1):
  clean=line.splitlines()[0] if line.splitlines() else ''
  for m in rx.finditer(clean):out.append(dict(path=p,line=no,start=m.start(),end=m.end(),absolute_start=offset+m.start(),absolute_end=offset+m.end(),text=m.group(),line_text=clean))
  offset+=len(line)
save('source-query.json',dict(files=source,pattern=pattern,flags='IGNORECASE',convention='UTF-8 strict, no normalization, one-based splitlines; zero-based half-open Unicode character offsets; exact multiset, including repeated matches. Search coverage is not semantic reading.'))
save('source-results.json',out)
for p in ['frontier/sources/i114_quantum_information_discovery/search-domain.json','frontier/sources/i114_quantum_information_discovery/snapshots/sources/preprints-tree.json','frontier/sources/i114_quantum_information_discovery/corpus-rg-inventory.json']:add(p)
save('references.json',sorted(refs.values(),key=lambda r:r['path']));save('inherited-packages.json',packs)
bind=[]
for r in load(S/'http-log.json'):
 p=Path(r['path']);t=p.with_suffix('.txt');bind.append(dict(log=r,source_binding=row(p),text_binding=row(t),extraction_command=['pdftotext','-layout',str(p),str(t)],normalization='Retained Poppler layout UTF-8 bytes with LF and form feeds; no extra normalization. HTTP status was not retained in the original retrieval log; valid PDF response and exact bytes were retained.'))
save('new-bindings.json',bind)
versions=[]
for p in sorted((S/'external').glob('*.txt')):
 t=p.read_text()
 for m in re.finditer(r'arXiv:[^\n]{0,100}|September 5, 2026',t[:6000]):versions.append(dict(path=str(p),start=m.start(),end=m.end(),text=m.group(),sha256=hashlib.sha256(m.group().encode()).hexdigest()))
save('current-versions.json',versions)
save('failure-log.json',[
 {'kind':'truncated-display','detail':'Read records0 and4 are marked truncated and recovered: initial decoded-view 0:40000 and88000:148000. Complete supplied unions cover all decoded literal content and scalars. Broad initial ledger/inventory displays also truncated and are not full semantic claims.'},
 {'kind':'failed-path','detail':'A Fock text read used a filename missing the word the and failed with FileNotFoundError. The correct path was then read from56000 through its ending. Default rg --files ignored the corpus; --no-ignore recovered the actual inventory.'},
 {'kind':'retrieval','detail':'The web tool could not open the current Kintali PDF. A direct HTTP retrieval succeeded; its SHA-256 is identical to the immutable I150 PDF. Four new PDF responses/extractions were retained; original HTTP status codes were not separately logged, and are not fabricated now.'},
 {'kind':'coverage-limit','detail':'Full Fock/Laughlin stability, both BFSS manuscripts, BDF-long, TV, GGJ, Kintali; complete operative TV23 Section6 and crossing ending, JTVW exact-depth3 and Fourier Section5. Wu square-lattice interfaces do not pay triangular transfer. Arefeva only model/algebra beginning; its downstream spectral proof not invoked. BDF letter not read. Bose main/setup/concluding interfaces plus complete momentum energy, energy-consequences, assembly and momentum proofs read; remaining Palm/path/route and companion proofs not fully read. No complete Bose novelty certification.'},
 {'kind':'external-literal-failures','detail':'JTVW squared-norm lemma remains false separately from unsquared proof. TV same-uniform flip coupling is not monotone, no-ring probability and detailed balance have literal defects. GGJ expected-sign/Parseval and parameter normalization defects remain distinct from corrections. See report for exact scopes.'},
 {'kind':'critical-input','detail':'Original I150 repeated TV critical-stability remark as task-specified input. That repetition is not a user-stipulated axiom. Exact triangular finite-free input remains unresolved; K2 transfer is valid conditionally. No square-lattice Wu/FK transfer and no raw Dirichlet limit asserted.'},
 {'kind':'prevalidation','detail':'The first read-only preflight stopped before diagnostics because it incorrectly required tool-display coverage for the original I150 report, which was supplied in full in the user message. The conversation reading is now recorded separately, not converted into an invented tool receipt. Later author edits required a fresh final prevalidation before the single seal.'},
 {'kind':'scope','detail':'Original audit verdicts are separated. Fresh screen retains technical Q153/Agmon/FS153 partials and unpaid candidate estimates; Bose full-proof screen incomplete. No nomination, eight accepted. No ancestor diagnostic or verifier executed, no active I151/I152 dependencies, no corpus copy.'}
])
print(json.dumps(dict(flat_references=len(refs),inherited_packages=len(packs),read_records=len(reads),source_occurrences=len(out),contexts=len(load(S/'contexts.json')))))
