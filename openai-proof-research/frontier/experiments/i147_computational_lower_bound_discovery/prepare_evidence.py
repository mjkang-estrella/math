"""Author-side assembly only. No inherited execution or corpus copying."""
from pathlib import Path
import json,hashlib,re,bisect
S=Path('frontier/sources/i147_computational_lower_bound_discovery');E=Path('frontier/experiments/i147_computational_lower_bound_discovery');OLD=Path('frontier/sources/i144_critical_siphon_window_repulsion')
MUTABLE={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
assert not (S/'seal.json').exists()
def load(p):return json.loads(Path(p).read_bytes())
def save(n,z):(S/n).write_text(json.dumps(z,ensure_ascii=False,indent=2)+'\n')
def row(p):
 b=Path(p).read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
refs={r['path']:r for r in load(OLD/'references.json')}
def add(p):
 p=str(p);assert not re.search(r'(?:^|/)(?:i|iteration)(?:145|146)(?:[-_/])',p),p
 if p.startswith(str(S)+'/') or p.startswith(str(E)+'/'):return
 assert p not in MUTABLE
 r=row(p)
 if p in refs:assert refs[p]['sha256']==r['sha256'],p
 refs[p]=r
packs=load(OLD/'inherited-packages.json')+[dict(source=str(OLD),experiment='frontier/experiments/i144_critical_siphon_window_repulsion',report='frontier/iterations/i144-critical-siphon-window-repulsion.md',seal=row(OLD/'seal.json'))]
for pack in packs:
 add(pack['seal']['path'])
 for r in load(pack['seal']['path'])['files']:add(r['path'])
for c in load(S/'contexts.json'):add(c['raw']);add(c['snapshot'])
for r in load(S/'snapshots.json'):
 if r['path'] not in MUTABLE:add(r['path'])
reads=load(S/'read-manifest.json')
for i,r in enumerate(reads):
 if i in {0,1,4,5}:r['display_status']='truncated-attempt; complete intervals recovered by later supplied displays'
 add(r['path']);t=Path(r['path']).read_text();a,b=r['char_start'],r['char_end'];starts=[];pos=0
 for line in t.splitlines(keepends=True):starts.append(pos);pos+=len(line)
 r.update(start_line=t[:a].count('\n')+1,end_line=t[:b].count('\n')+1,splitlines_start=bisect.bisect_right(starts,a),splitlines_end=bisect.bisect_right(starts,max(a,b-1)))
save('read-manifest.json',reads)
source=sorted({r['path'] for r in reads if r['path'].endswith('.tex') or '/external/' in r['path'] and r['path'].endswith('.txt')})
overlap=sorted({r['path'] for r in reads if r['path'].startswith(('frontier/iterations/','frontier/reviews/'))})
for label,files,pattern in [('source',source,r'choiceless|counting|witness\w*|support\w*|localization|Fourier|parity|majority|ancilla\w*|transitiv\w*|total|partial|query|Dirichlet|Gaussian|conditional|noise'),('overlap',overlap,r'QAC|quantum|circuit\w*|choiceless|counting|Forrelation|oracle|precision|computation|characteristic|IMM|lower.bound|siphon|P138')]:
 rx=re.compile(pattern,re.I);out=[]
 for p in files:
  add(p)
  for no,line in enumerate(Path(p).read_text(errors='replace').splitlines(),1):
   for m in rx.finditer(line):out.append(dict(path=p,line=no,start=m.start(),end=m.end(),text=m.group(),line_text=line))
 save(label+'-query.json',dict(files=files,pattern=pattern,flags='IGNORECASE',convention='UTF8 replacement decoded; no Unicode normalization; one-based splitlines, zero-based half-open character offsets; multiplicity retained'))
 save(label+'-results.json',out)
# Original mandatory corpus map/tree referenced, never copied.
for p in ['frontier/sources/i114_quantum_information_discovery/search-domain.json','frontier/sources/i114_quantum_information_discovery/snapshots/sources/preprints-tree.json','frontier/sources/i114_quantum_information_discovery/corpus-rg-inventory.json']:add(p)
save('references.json',sorted(refs.values(),key=lambda r:r['path']));save('inherited-packages.json',packs)
bind=[]
for log in ['http-log.json','http-log-more.json']:
 for r in load(S/log):
  b=dict(r);b['text']=r.get('text',str(Path(r['path']).with_suffix('.txt')));b['text_binding']=row(b['text']);b['source_binding']=row(r['path'])
  if r['path'].endswith('.pdf'):
   b.setdefault('extraction_command',['pdftotext','-layout',r['path'],b['text']]);b.setdefault('extraction_exit',0)
   b['normalization']='Poppler pdftotext -layout, preserved UTF8 bytes including LF/form feeds; no further normalization'
  bind.append(b)
save('new-bindings.json',bind)
versions=[]
for p in sorted((S/'external').glob('*.txt')):
 t=p.read_text();rx=re.compile(r'arXiv:\s*\d{4}\.\d{4,5}v\d[^\n]*|\b(?:Received|Revised|Accepted)[^\n]*')
 for m in rx.finditer(t[:5000]):versions.append(dict(path=str(p),start=m.start(),end=m.end(),text=m.group(),sha256=hashlib.sha256(m.group().encode()).hexdigest()))
# Current live version-page observations are kept as tool responses, not fabricated raw HTTP HTML.
for p in [S/'primary-pages-1.json',S/'primary-pages-final.json']:
 t=p.read_text()
 for m in re.finditer(r'last revised[^\n]{0,100}',t):versions.append(dict(path=str(p),start=m.start(),end=m.end(),text=m.group(),sha256=hashlib.sha256(m.group().encode()).hexdigest()))
save('current-versions.json',versions)
save('failure-log.json',[
 {'kind':'display-truncation','detail':'Initial decoded-view 0:40000 and 0:70000 attempts truncated. A combined 78000:102000 and 102000:126000 display also truncated around decoded IDs 534-538. All four attempts remain marked; later smaller complete supplied displays cover the entire view. An unrecorded broad cat of I07 plus context metadata also truncated; only its later bounded early-screen passage is claimed read.'},
 {'kind':'preparation-failure','detail':'Initial binding assembly encountered a missing text key for the manually extracted transitive PDF; the retained .txt path is now derived explicitly. Initial HTML extraction attempted an unavailable bs4 import. Acquisition was completed using the explicitly recorded stdlib HTMLParser normalization. No missing full text is represented as retrieved.'},
 {'kind':'unused-preparation','detail':'context-lines.json/context-fields.json/context-view.txt and decoded-scalars.txt are preserved preparation artifacts, not claimed semantic read records. Reading uses decoded-view.txt and scalar-values.txt with exact occurrence maps.'},
 {'kind':'external-literal-discrepancy','detail':'JTVW v4 Lemma 5.5 in retained HTML/text states a Fourier-tail difference bounded by twice the squared L2 distance, while its proof ends with twice the unsquared L2 distance. These are not identified or silently repaired; no version of this lemma is a premise of I147. The comparator theorem is not an upstream truth audit.'},
 {'kind':'inherited-failures','detail':'All original literal mathematical failures, truncated retrievals, failed publisher403 responses and frozen receipts remain in the flat ancestor union. No ancestor verifier/diagnostic/extraction was executed.'},
 {'kind':'coverage-limit','detail':'All pinned mathematical sections selected for families243,274,284 were read through endings. External semantic reading is exactly scoped in read-manifest and report; CPT/query comparators have selected statements/constructions, not a claim of full-paper validation. Crossing proof remains unread beyond introduction and is not a premise. Additional exploratory web searches in the session were not all separately serialized; retained searches alone are not claimed exhaustive.'},
 {'kind':'research-limit','detail':'Original I144 paid claims PASS unchanged; generalP138 PARK. T1 technical theorem paid, substantiality not established. T2 transitive total compiler and T3 growing-stabilizer estimate missing. No ninth nomination.'}])
print(json.dumps(dict(flat_references=len(refs),inherited_packages=len(packs),read_records=len(reads),new_bindings=len(bind),source_occurrences=len(load(S/'source-results.json')),overlap_occurrences=len(load(S/'overlap-results.json')))))
