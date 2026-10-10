"""One-time I130 preparation. Not executed by the offline verifier; cannot reseal."""
from pathlib import Path
import json,hashlib,re
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i130_spectral_harmonic_discovery'
E=ROOT/'frontier/experiments/i130_spectral_harmonic_discovery'
assert not (S/'seal.json').exists()
def sha(b):return hashlib.sha256(b).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
def rel(p):return str(p.relative_to(ROOT))
task=json.loads((S/'snapshots/frontier/iterations/iteration130-spectral-harmonic-discovery-task.json').read_text())
markers=['--- ORIGINAL DIRECT I127 BRIEF ---','--- ORIGINAL I127 REPORT ---','--- FINALIZED I127 PARENT RESPONSE ---']
names=['supplied-original-i127-brief.txt','supplied-original-i127-report.txt','supplied-finalized-i127-parent-response.txt']
for i,n in enumerate(names):
 t=task['brief'].split(markers[i],1)[1]
 if i+1<len(markers):t=t.split(markers[i+1],1)[0]
 (S/n).write_text(t)
assert (S/names[1]).read_text().strip()==(S/'snapshots/frontier/iterations/i127-diagonal-pinned-distance.md').read_text().strip()
assert json.loads((S/names[2]).read_text())==json.loads((S/'snapshots/frontier/experiments/i127-parent-verification.json').read_text())
dump(S/'input-freeze.json',dict(task130=rel(S/'snapshots/frontier/iterations/iteration130-spectral-harmonic-discovery-task.json'),task127=rel(S/'snapshots/frontier/iterations/iteration127-diagonal-pinned-distance-task.json'),markers=markers,parts=names,convention='Exact substrings preserve surrounding LF; report comparison strips surrounding whitespace only; parent comparison parses full JSON.'))
# Search complete original/text representation once, never treating matches as readings.
domain=json.loads((ROOT/'frontier/sources/i112_inverse_boundary_discovery/search-domain.json').read_text())
expr=r'(?i)(nodal.{0,40}(?:bound|measure)|harmonic.{0,40}(?:growth|dimension)|tangent cones?|infinity[- ]harmonic)'
rx=re.compile(expr);rows=[]
for x in domain:
 b=(ROOT/x['local']).read_bytes()
 assert sha(b)==x['sha256']
 for i,l in enumerate(b.decode('utf-8',errors='replace').splitlines(),1):
  mm=list(rx.finditer(l))
  if mm:rows.append(dict(path=x['path'],local=x['local'],splitlines_line=i,text=l,spans=[list(m.span()) for m in mm]))
dump(S/'lexical-search.json',dict(patterns={'spectral_harmonic':expr},results={'spectral_harmonic':rows},scope='Complete inherited 10,373-position domain, one flat traversal; search evidence only.'))
paths=['frontier/iterations/'+n for n in ['i02-crossfield.md','i02-crossfield-r2.md','i07-analysis.md','i13-fresh-discovery.md','i14-spectral-width-novelty-r3.md','i27-geometric-analysis-discovery.md','i52-ergodic-dynamical-discovery.md','i80-geometric-flows-computation-discovery.md']]
# Obtain exact existing report names from the already-read manifest rather than guess.
manifest=json.loads((S/'read-manifest.json').read_text())
paths=sorted({p['local'] for p in manifest['passages'] if p['local'].startswith('frontier/iterations/') and re.search(r'/i(?:02|07|13|14|27|52|80)[-]',p['local'])})
orx=r'(?i)(nodal|harmonic|spectral|hot.spot|flow|technical|witness|width|quantum)';rr=re.compile(orx);orows=[]
for p in paths:
 for i,l in enumerate((ROOT/p).read_text().splitlines(),1):
  mm=list(rr.finditer(l))
  if mm:orows.append(dict(path=p,splitlines_line=i,text=l,spans=[list(m.span()) for m in mm]))
dump(S/'overlap-search.json',dict(paths=paths,expression=orx,results=orows))
refs={p['local'] for p in manifest['passages'] if not p['local'].startswith(rel(S)+'/')}
refs.update(paths)
refs.update(x['path'] for x in json.loads((S/'recursive-freeze.json').read_text())['records'])
refs.update(['frontier/experiments/i124_fractal_incidence_discovery/extract_html.py','frontier/experiments/i127-parent-verification.json','frontier/iterations/i127-diagonal-pinned-distance.md','frontier/sources/i127_diagonal_pinned_distance/seal.json'])
refs.difference_update(['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'])
dump(S/'immutable-references.json',[dict(path=p,sha256=sha((ROOT/p).read_bytes())) for p in sorted(refs)])
dump(S/'reading-limitations.json',dict(
 conventions='splitlines() for new corpus and HTML; passage LF join without terminal newline. Inherited PDF LF/form-feed conventions retained. Complete downloaded text is not a complete semantic reading claim.',
 complete_selected_construction='3D harmonic companion: introduction, crossings, angular-program, geometry, transfer, matching, growth, each through its end.',
 scoped_other_reads='Nodal exactification/persistence and power global operation through endings; surface introduction/final length operation; infinity introduction/reduction/rigidity. Other lower statements are stipulated dependencies, not claimed read proofs.',
 truncated_attempts=[
 'Initial broad ledger/overlap rg output exceeded tool output budget; only displayed portions count; narrower report ranges logged separately.',
 'Combined original-i124 ending plus original-i121 1-160 lost original-i121 opening; original-i121 1-40 was reread. Lines 41-160 were displayed.',
 'Original-i118 1-105 lost a short opening segment; 14-20 reread; the full remaining recursive brief was displayed in bounded calls.',
 'Broad primary-text rg was truncated; exact relied-upon theorem/proof ranges reread through read_support.',
 'A combined web-search plus Huang reading result had outer truncation in the search portion; Huang 1-211 display was complete. Search hits are never counted as proof reading.'
 ],
 failed_reads=['Guessed Falconer 01_preparation.tex did not exist; actual 04_preparation.tex read.'],
 retrieval='All recorded HTTP retrievals succeeded; current-version pages separate from versioned HTML. No new PDF extraction.',
 search='Bounded official arXiv and primary journal search; no worldwide novelty, human review or certification.'
))
print(json.dumps(dict(lexical_lines=len(rows),overlap_lines=len(orows),references=len(refs),passages=len(manifest['passages']))))
