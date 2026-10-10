"""Author-side manifest assembly. Never executes inherited code or copies corpus bytes."""
from pathlib import Path
import json,hashlib,re,bisect
S=Path('frontier/sources/i150_near_critical_crossing_circuit_bounds');E=Path('frontier/experiments/i150_near_critical_crossing_circuit_bounds');OLD=Path('frontier/sources/i147_computational_lower_bound_discovery')
MUTABLE={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
assert not (S/'seal.json').exists()
def load(p):return json.loads(Path(p).read_bytes())
def save(n,z):(S/n).write_text(json.dumps(z,ensure_ascii=False,indent=2)+'\n')
def row(p):
 b=Path(p).read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
refs={r['path']:r for r in load(OLD/'references.json')}
def add(p):
 p=str(p);assert not re.search(r'(?:^|/)(?:i|iteration)(?:148|149)(?:[-_/])',p),p
 if p.startswith(str(S)+'/') or p.startswith(str(E)+'/'):return
 assert p not in MUTABLE
 r=row(p)
 if p in refs:assert refs[p]['sha256']==r['sha256'],p
 refs[p]=r
packs=load(OLD/'inherited-packages.json')+[dict(source=str(OLD),experiment='frontier/experiments/i147_computational_lower_bound_discovery',report='frontier/iterations/i147-computational-lower-bound-discovery.md',seal=row(OLD/'seal.json'))]
for pack in packs:
 add(pack['seal']['path'])
 for r in load(pack['seal']['path'])['files']:add(r['path'])
for c in load(S/'contexts.json'):add(c['raw']);add(c['snapshot'])
for r in load(S/'snapshots.json'):
 if r['path'] not in MUTABLE:add(r['path'])
reads=load(S/'read-manifest.json')
for i,r in enumerate(reads):
 if i in {0,2}:r['display_status']='truncated-attempt; complete intervals recovered by later supplied displays'
 add(r['path']);t=Path(r['path']).read_text();a,b=r['char_start'],r['char_end'];starts=[];pos=0
 for line in t.splitlines(keepends=True):starts.append(pos);pos+=len(line)
 r.update(start_line=t[:a].count('\n')+1,end_line=t[:b].count('\n')+1,splitlines_start=bisect.bisect_right(starts,a),splitlines_end=bisect.bisect_right(starts,max(a,b-1)))
save('read-manifest.json',reads)
source=sorted({r['path'] for r in reads if r['path'].endswith('.tex') or '/external/' in r['path'] and r['path'].endswith('.txt')})
overlap=[str(S/'snapshots/frontier/iterations/i147-computational-lower-bound-discovery.md')]
for label,files,pattern in [('source',source,r'localization|Fourier|parity|majority|ancilla\w*|Dirichlet|Gaussian|conditional|noise|sensitivity|four.arm|mixing|boundary|critical|finite.energy|pivotal|reflection|insertion|retention'),('overlap',overlap,r'QAC|quantum|circuit\w*|choiceless|counting|transitiv\w*|query|siphon|P138|PARK|FAIL|PASS')]:
 rx=re.compile(pattern,re.I);out=[]
 for p in files:
  add(p);t=Path(p).read_bytes().decode('utf-8');offset=0
  for no,line in enumerate(t.splitlines(keepends=True),1):
   # Strip exactly splitlines separators, preserving all other characters.
   clean=line.splitlines()[0] if line.splitlines() else ''
   for m in rx.finditer(clean):out.append(dict(path=p,line=no,start=m.start(),end=m.end(),absolute_start=offset+m.start(),absolute_end=offset+m.end(),text=m.group(),line_text=clean))
   offset+=len(line)
 save(label+'-query.json',dict(files=files,pattern=pattern,flags='IGNORECASE',convention='UTF-8 strict; no Unicode normalization; one-based splitlines, zero-based half-open Unicode character offsets within line and whole text; exact multiplicity'))
 save(label+'-results.json',out)
for p in ['frontier/sources/i114_quantum_information_discovery/search-domain.json','frontier/sources/i114_quantum_information_discovery/snapshots/sources/preprints-tree.json','frontier/sources/i114_quantum_information_discovery/corpus-rg-inventory.json']:add(p)
save('references.json',sorted(refs.values(),key=lambda r:r['path']));save('inherited-packages.json',packs)
bind=[]
for r in load(S/'http-log.json'):
 b=dict(r);b['text']=r.get('text',str(Path(r['path']).with_suffix('.txt')));b['text_binding']=row(b['text']);b['source_binding']=row(r['path'])
 b['extraction_command']=r.get('extraction',['pdftotext','-layout',r['path'],b['text']]);b['extraction_exit']=0
 b['normalization']='Poppler pdftotext -layout, retained UTF-8 bytes including LF/form feeds; no additional normalization';bind.append(b)
save('new-bindings.json',bind)
versions=[]
for p in sorted((S/'external').glob('*.txt')):
 t=p.read_text()
 for m in re.finditer(r'arXiv:\s*\d{4}\.\d{4,5}v\d[^\n]*|September 5, 2026',t[:5000]):versions.append(dict(path=str(p),start=m.start(),end=m.end(),text=m.group(),sha256=hashlib.sha256(m.group().encode()).hexdigest()))
for p in [S/'current-primary-web.json',S/'primary-pages.json']:
 t=p.read_text()
 for m in re.finditer(r'last revised[^\\\n]{0,100}',t):versions.append(dict(path=str(p),start=m.start(),end=m.end(),text=m.group(),sha256=hashlib.sha256(m.group().encode()).hexdigest()))
save('current-versions.json',versions)
save('failure-log.json',[
 {'kind':'display-truncation','detail':'Decoded-view attempt 0:42000 first returned functions truncation, then fully recovered by second display. Attempt 42000:100000 had shell middle truncation, recovered by 42000:61000,61000:69000,69000:85000,85000:100000. Read records 0 and 2 are marked. Other supplied ranges cover all decoded lines and scalar values.'},
 {'kind':'unclaimed-broad-displays','detail':'Initial broad file-name inventory and broad ledger grep were truncated. Later broad status display and serialized dependency-search display also truncated. Only separately bounded relevant ledger excerpts and the source readings in read-manifest are claimed semantic coverage. Active I148/I149 reports were not opened or bound. Full live ledger snapshots necessarily retain their literal mentions.'},
 {'kind':'retrieval-failure','detail':'A web click for the Kintali PDF used an invalid ref/id combination and returned invalid-arguments. The author homepage was retrieved by requests; an attempted bs4 import failed (ModuleNotFoundError), recovered by a regex of the actual href papers/QAC.pdf. The complete PDF was then retrieved directly and read through its ending.'},
 {'kind':'web-retention','detail':'The first current-version web response was displayed but not separately serialized; a fresh current-version retrieval is retained in current-primary-web.json. Search responses are tool observations, not fabricated raw HTTP HTML. Bounded searches are not exhaustive.'},
 {'kind':'external-literal-failure','detail':'JTVWv4 Lemma5.5 squared-L2 inequality remains literally false, separately from its proof\'s unsquared bound. GGJ expected-sign codomain/Parseval and intermediate normalization slips and TV no-ring/generator typographical slips remain in immutable sources. No such line is repaired into a premise.'},
 {'kind':'withdrawn-author-intermediate-claim','detail':'A progress update and draft proposed critical triangular Dirichlet energy tending to zero from TV\'s cited critical four-arm estimate. Checking Wu\'s primary hypotheses found square-lattice theorems only. That stronger assertion is not retained as independently paid. The final actual-model obstruction is independently proved using the task\'s fixed-time critical stability, a variational resolvent and bounded finite-volume density/conductance comparison. No triangular transfer of Wu is assumed.'},
 {'kind':'coverage-limit','detail':'Full TVv2, full GGJv2 and full Kintali manuscript; all fourteen family274 mathematical sections. JTVW strongest statements, model/preliminaries and complete Sections4/5 read; not claimed full-paper audit. TV23 complete operative Section6 and crossing ending read. FK near-critical and Wu read at full setup/theorem interfaces sufficient to reject direct hypothesis matching, not claimed full SLE/FK proof audits. Gaussian comparator scope remains inherited and no new Gaussian source theorem is invoked.'},
 {'kind':'prevalidation-display','detail':'The initial author preflight passed all byte checks and all new finite diagnostics, but its console inventory display was truncated. Further scoped CPT-source reading and proof review changed the unsealed package. The final complete prevalidation is therefore captured afresh before the single seal; the first console display is not called a complete saved receipt.'},
 {'kind':'inherited','detail':'All ancestor literal failures, failed/truncated retrievals, seals and receipts are preserved by a flat immutable union. No ancestor diagnostic, verifier, extraction or numerical search runs.'},
 {'kind':'research-limit','detail':'Fixed-beta consequence technical; no positive NC150 kappa paid. MA and conditional spectrum criteria are conditional theorems, not verification of the polynomial temperature window. Method obstruction is not a refutation of NC150. No nomination.'}
])
print(json.dumps(dict(flat_references=len(refs),inherited_packages=len(packs),reads=len(reads),new_bindings=len(bind),source_occurrences=len(load(S/'source-results.json')),overlap_occurrences=len(load(S/'overlap-results.json')))))
