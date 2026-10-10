"""One-time provenance packaging; do not run to refresh a sealed review."""
from pathlib import Path
import json,re,hashlib
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i38_propeller_stability_novelty_r3';L=S/'literature'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
# Supplement tool-generated read.py logs with actual earlier cat/sed reads.
paths=['frontier/iterations/i38-inequality-stability-discovery.md','frontier/reviews/i38-propeller-stability-r2.md','frontier/reviews/i25-rooted-entropy-novelty-r3.md','frontier/reviews/i30-einstein-metric-stability-novelty-r3.md','frontier/reviews/i36-common-geometric-avoidance-novelty-r3.md','AGENTS.md','sources/upstream.json']
C=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
G=C/'preprints/The-Gaussian-Propeller-Bound-in-Every-Dimension-September-24-2026'
paths += [str(p.relative_to(R)) for p in sorted(G.rglob('*')) if p.is_file()]
manual=[{'path':n,'sha256':sha(R/n),'scope':'full text read; earlier direct tool output and/or read.py spans; not a computational proof audit'} for n in paths]
manual += [dict(path=str((L/n).relative_to(R)),sha256=sha(L/n),scope=s) for n,s in [('hei14-author.txt','Earlier direct reads: definitions and Lemmas 2.5–2.8, full proof of 2.8, closing discussion; later read.py closing ranges supplement.'),('kn-author.txt','Earlier direct reads of Lemmas 3.2,3.3,3.7 and Corollary 3.4; later read.py fills existence and tails.')]]
(S/'manual-read-scope.json').write_text(json.dumps(manual,indent=2)+'\n')
versions=[]
for p in sorted(L.glob('*current*.html')):
 s=p.read_text(errors='replace');hit=s.find('class="submission-history"');end=s.find('</div>',hit)
 versions.append({'file':p.name,'sha256':sha(p),'history':re.sub('<[^>]*>',' ',s[hit:end]).replace('\n',' ')})
(L/'versions-all.json').write_text(json.dumps(versions,indent=2)+'\n')
hits=[];files=0
for category in ['iterations','reviews','findings']:
 d=R/'frontier'/category
 if not d.exists():continue
 for p in sorted(d.rglob('*.md')):
  if p.name=='i38-propeller-stability-novelty-r3.md':continue
  files+=1
  matches=[{'line':i,'text':l} for i,l in enumerate(p.read_text(errors='replace').splitlines(),1) if re.search(r'propeller|Heilman|Gaussian.{0,50}(partition|maximum)|first.moment.{0,50}stabil',l,re.I)]
  if matches:hits.append({'path':str(p.relative_to(R)),'sha256':sha(p),'matches':matches})
(S/'project-search.json').write_text(json.dumps({'scope':'All Markdown files recursively in frontier/iterations, frontier/reviews, frontier/findings; excluded this review. Supplement to corpus search, not a proof of absence.','files':files,'hits':hits},indent=2)+'\n')
# Add the only explicit Gaussian companion interface found in the complete corpus.
m=json.loads((C.parent/'corpus-manifest.json').read_text())['files']
sel=json.loads((S/'selected-pinned.json').read_text())
sel += [x for x in m if x['path'] in ['preprints/The-Unique-Games-Theorem-September-23-2026/build/sections/07-consequences.tex','preprints/The-Unique-Games-Theorem-September-23-2026/build/references.bib']]
(S/'selected-pinned.json').write_text(json.dumps(sel,indent=2)+'\n')
# Fresh responses compared to frozen previous primary payloads, without modifying them.
prior={}
for stem in ['i38_inequality_stability_discovery','i38_propeller_stability_r2']:
 for p in (R/'frontier/sources'/stem).rglob('*.pdf'):prior.setdefault(sha(p),[]).append(str(p.relative_to(R)))
identities=[{'file':str(p.relative_to(R)),'sha256':sha(p),'byte_identical_previous':prior.get(sha(p),[])} for p in sorted(L.glob('*.pdf'))]
(S/'primary-identities.json').write_text(json.dumps(identities,indent=2)+'\n')
print({'manual_full_texts':len(paths),'current_version_pages':len(versions),'project_markdown_files':files,'project_hit_files':len(hits),'selected_pinned':len(sel),'pdf_payloads':len(identities)})
