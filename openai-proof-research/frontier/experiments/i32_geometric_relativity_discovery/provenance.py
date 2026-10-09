"""Build compact provenance references without copying the reused corpus."""
from pathlib import Path
import json,hashlib,re,html
R=Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i32_geometric_relativity_discovery'
C=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
def sha(b):return hashlib.sha256(b).hexdigest()
def put(name,value):(S/name).write_text(json.dumps(value,indent=2,ensure_ascii=False)+'\n')

inputs=json.loads((S/'input-manifest.json').read_text())
for name in ['frontier/iterations/iteration30-einstein-metric-stability-task.json','frontier/iterations/iteration30-einstein-metric-stability-novelty-r3-task.json']:
    if not any(e['path']==name for e in inputs):
        b=(R/name).read_bytes();p=S/'inputs'/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
        inputs.append(dict(path=name,frozen=str(p.relative_to(R)),sha256=sha(b),bytes=len(b)))
put('input-manifest.json',inputs)

manifest=json.loads((C.parent/'corpus-manifest.json').read_text())
index={e['path']:e for e in manifest['files']}
reads=json.loads((S/'read-passages.json').read_text())
prefix=str(C.relative_to(R))+'/'
selected={e['path'][len(prefix):] for e in reads if e['path'].startswith(prefix)}
# Prior to the structured read logger, these complete sections were opened directly.
# Retain that distinction rather than pretending they were logged at the time.
direct=[
 ('Sharp-One-Third-Stability-of-Brenier-Maps-September-25-2026/build/source/sections/introduction.tex','Statement and normalization, direct early read'),
 ('Sharp-One-Third-Stability-of-Brenier-Maps-September-25-2026/build/source/sections/moments.tex','Lines 1-160 direct early read; remainder separately logged'),
]
for p,note in direct:selected.add('preprints/'+p)
put('source-manifest.json',{'pin':manifest['pin'],'corpus_root':str(C.relative_to(R)),'files':[dict(index[p],local_path=prefix+p) for p in sorted(selected)],'direct_read_notes':[{'path':'preprints/'+p,'note':n} for p,n in direct],'read_log_note':'Line ranges in read-passages.json use Python splitlines(keepends=True), including PDF form feeds. Initial direct reads are not a complete chronological log. Reopened decisive passages supply the auditable dependency record; inventory regex hits are not semantic reads.'})

families={
 'K2':'Generic-Future-Inextendibility-with-Square-Integrable-Connection-Near-a-Fixed-Kerr-Spacetime-September-23-2026/build/sections/',
 'K1':'Generic-C1-Future-Inextendibility-Near-Rotating-Subextremal-Kerr-Spacetimes-September-23-2026/build/sections/',
 'K0':'Quantitative-Near-Kerr-Evolution-and-Generic-C2-Future-Inextendibility-September-23-2026/build/sections/',
 'PC':'The-spacetime-Penrose-inequality-with-charge-and-original-data-rigidity-October-5-2026/build/sections/',
 'BT':'Sharp-One-Third-Stability-of-Brenier-Maps-September-25-2026/build/source/sections/',
}
rows=[
 ('K2','introduction.tex',['intro:seminorms','intro:extension','thm:main'],'Exact weighted smooth topology, p10 neighborhood, full-MGHD future extension, weak Koszul interpretation.'),
 ('K2','background.tex',['prop:bg-package','prop:bg-runout','lem:bg-branch-tube'],'Fixed-center geometry, summable low envelopes, fixed-order subexponential jets, full-lifetime classification and canonical branch tubes.'),
 ('K2','weak_exits.tex',['ex:boxes','prop:exit-family','prop:exit-cover'],'Continuous first-exit graph; L1 phase averaging and finite chart witnesses; countable exit cover.'),
 ('K1','05-preparation.tex',['prep:amplitude-independent-exterior'],'Exact signed exterior preparation for every fixed positive exponential amplitude rate; ends at cylinder, not interior.'),
 ('K0','07-interior.tex',['in:entry','in:higher'],'Retained A_S weighted entry trace; actual paired-current proof, two triangular limiting systems, fixed directional damping, bounded-potential recovery.'),
 ('K0','05-compact.tex',['co2:levels'],'Squared time weights A=1.36, A_S=1.06; these are stronger than bare L1 and are retained in the obstruction analysis.'),
 ('K2','packet_preparation.tex',['prop:packet-preparation','pk:template-defect'],'Whole-footprint constrained packet, exact full-bridge correction with permitted tail, double-null template and inverse-lapse residual losses.'),
 ('K2','nonlinear_comparison.tex',['thm:dn-comparison','lem:dn-high-uniform','prop:dn-low-error','dn:interpolation-choice'],'Moving-family high estimates, compensated low Hodge terms, late support, quadratic error, finite-order interpolation and continuation.'),
 ('K2','attachment_signal.tex',['prop:experiment-attachment','prop:curvature-signal','prop:matched-seeds'],'Whole-bridge MGHD attachment, finite persistence, canonical matching and curvature difference on fixed footprint.'),
 ('K2','holonomy_category.tex',['ho:base-comparison','ho:loop-jets','prop:averaged-holonomy','thm:nowhere-dense'],'Timelike boost control, density-only stopped averaging, eighteen-point coefficient extraction, source category mechanism.'),
 ('PC','statements.tex',['def:data','def:full-cut','thm:numerical','thm:rigidity'],'Exact AF charged DEC/cut/mass definitions, upper-area branch and nonextremal original-data equality.'),
 ('PC','variation.tex',['va:area-envelope','va:separation','va:gaussian-jets'],'Datumwise compactness, positive multiplier separation and original-data normal variations; no quantitative near-equality contract asserted.'),
 ('BT','moments.tex',[],'Uniform source midpoint domination gives weighted inverse cell-moment bound with constant 162R^2.'),
 ('BT','finite_stability.tex',[],'Optimal target coupling, no interior site collisions, Laplacian solve without inverse norm estimate, potential bound.'),
 ('BT','gradient.tex',['gradient:interpolation','gradient:extension'],'Known convex gradient interpolation and finite-net limit; uniform atom degenerations already handled.'),
 ('BT','sharpness.tex',['sharpness:exponent'],'Three-atom cube construction, exact W2 and map-distance formulas.'),
]
contracts=[]
for fam,file,labels,contract in rows:
    path='preprints/'+families[fam]+file
    text=(C/path).read_text()
    missing=[x for x in labels if ('\\label{'+x+'}') not in text]
    if missing:raise RuntimeError((path,missing))
    contracts.append(dict(id=fam+':'+file,path=path,labels=labels,contract=contract,sha256=index[path]['sha256'],url=index[path]['url']))
put('contracts.json',contracts)

versions=[]
for p in sorted((S/'literature').glob('*.html')):
    t=p.read_text(errors='replace')
    def meta(name):
        return [html.unescape(m) for m in re.findall(r'<meta\s+name="'+re.escape(name)+r'"\s+content="([^"]*)"',t)]
    versions.append({'file':str(p.relative_to(R)),'sha256':sha(p.read_bytes()),'title':meta('citation_title'),'authors':meta('citation_author'),'date':meta('citation_date'),'arxiv_id':meta('citation_arxiv_id'),'history_excerpt':re.sub('<[^>]+>',' ',t[t.find('Submission history'):t.find('Submission history')+2500]) if 'Submission history' in t else None})
put('literature/versions.json',versions)
put('provenance-notes.json',{'request_archive_limit':'search1.json contains the initial response only; its exact request was not retained. It is not reconstructed. Later request/response objects, including search-final.json, are retained.','failed_fetches':'1109.2165v2 abs and pdf returned 404; exact returned bytes are kept. 1109.2165v1 succeeded.','read_only_command_failures':['An initial command ran in the parent cwd and did not find project paths; subsequent commands set workdir explicitly.','One rg expression used an invalid backslash escape; retried with literal -e patterns.','One guessed companion filename 04-compact.tex was absent; 05-compact.tex was found and read.','Optional SymPy import failed; exact diagnostics use standard-library Fraction arithmetic, no installation.'],'scope':'Only I32 report, sources directory and experiments directory written. Complete corpus reused read-only; no index, git mutation, publication, agents, or other-project writes.','semantic_limit':'Only recorded source/proof passages and stated direct early reads were semantically inspected. Complete inventory and corpus integrity validation do not mean complete semantic reading.','mathematical_status':'Developed logarithmic endpoint gap; technical fixed-p deduction not independently reviewed and not nominated as a substantial finding.'})
print(json.dumps({'selected_sources':len(selected),'contracts':len(contracts),'inputs':len(inputs),'version_pages':len(versions)}))
