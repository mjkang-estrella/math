from pathlib import Path
import json,hashlib,re
ROOT=Path(__file__).resolve().parent
REPO=ROOT.parents[3]
PACKET=ROOT/'packet'
sha=lambda b:hashlib.sha256(b).hexdigest()
def save(p,x):p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
receipts=json.loads((PACKET/'private/upstream/receipts.json').read_text())
tree=json.loads((PACKET/'private/context/preprints-tree.json').read_text()); entries={x['path']:x for x in tree['tree']}
sources=[]
for r in receipts:
 b=(PACKET/r['local']).read_bytes(); assert sha(b)==r['sha256']
 r=dict(r);r['canonical_record']=entries[r['path']];r['labels_present_not_all_read']=re.findall(r'\\label\{([^}]+)\}',b.decode());sources.append(r)
save(PACKET/'public/source-register.json',sources)
primary=json.loads((PACKET/'private/primary/receipts.json').read_text())
limits={
'xu-zhuang-v2':'Text lines35–90,880–902; Theorems1.1–1.3 and complete Theorem1.2 proof. No complete boundedness proof or constructibility helper-chain reading.',
'roots':'Title/introduction1–38;460–550 Lemmas4.1–4.2/Theorem4.1/Corollary4.1 and start4.2;850–1000, especially complete Theorems8.1–8.2 and stable-rigidity discussion. Other sections not fully read.',
'deo-bien-hai-v2':'Text615–670, complete Theorem5 finite multiplication-table proof and adjacent matrix-group comments. Not the whole paper.',
'du-xie-v1':'Text230–398, complete Propositions2.1–2.3 proof, tensor/adjoint definition, coefficient-stability estimate. Label navigation elsewhere. No full split-model/moduli proof reading.',
'du-xie-first-jet-v1':'Text1–419, full introduction and complete Section2/Theorem1.1 proof, first-jet formula, finite alternative, nesting, C2 density and measure limit. Section3 example and cited density/Levi helper proofs not newly read.'}
for r in primary:
 r['pdf_local']='private/primary/'+r['name']+'.pdf';r['text_local']='private/primary/'+r['name']+'.txt';r['semantic_extent']=limits[r['name']];r['external_not_stipulated']=True
save(PACKET/'public/primary-register.json',primary)
selected={
'frontier/iterations/i28-algebra-discovery.md':'Section4 complete; portions175–209 preceding no-MCM discussion; remainder only searches/excerpts. Combined truncation repaired for Section4.',
'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r15/checkpoint.md':'Sections2–3 complete, with late focused49–96 reread. Unrelated Section1 not fully read.',
'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r25/screen-037.md':'Complete; discovered after initial existential-gap thought, before any freeze.',
'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r25/screen-202-history.md':'Complete. Named I104/I108/I110 not fully followed.',
'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r32/screen-203.md':'Complete.',
'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r74/research.md':'Complete, actual weighted orbit/root-adjoining gap.',
'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r74/history-correction.md':'Complete.',
'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r76/packet/public/research.md':'Complete; matrix-algebra/external-scalar interfaces distinguished.',
'frontier/campaigns/2026-10-14/fresh-structural-discovery-r29/screen-050.md':'Complete, late before sealing.',
'frontier/campaigns/2026-10-14/spin-four-factor-r2/candidate.md':'Complete candidate body read during initial screen; primary cited there not freshly acquired.'}
history=[]
for n,(p,extent) in enumerate(selected.items(),1):
 src=REPO/p
 if not src.exists(): raise RuntimeError(str(src))
 b=src.read_bytes();dst=PACKET/'private/history'/f'{n:02d}-{src.name}';dst.write_bytes(b);history.append(dict(origin=p,local=str(dst.relative_to(PACKET)),sha256=sha(b),bytes=len(b),semantic_extent=extent))
save(PACKET/'public/history-register.json',history)
context=[]
for p in ['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json','frontier/NEW-TEN-2026-10-14.md']:
 src=REPO/p;name=src.name; cp=PACKET/'private/context'/name; b=cp.read_bytes();context.append(dict(origin=p,local=str(cp.relative_to(PACKET)),sha256=sha(b),bytes=len(b),note='Retained opening snapshot; semantic extents in reading-limits. Live shared history may evolve.'))
for src in sorted((REPO/'frontier/findings').glob('R*.md')):
 if 23<=int(src.name[1:4])<=40:
  b=src.read_bytes();dst=PACKET/'private/context'/src.name;dst.write_bytes(b);context.append(dict(origin=str(src.relative_to(REPO)),local=str(dst.relative_to(PACKET)),sha256=sha(b),bytes=len(b),note='Complete finding body read; linked proofs/reviews not all read.'))
# Recent context: record identities without copying full packets or repeating large snapshots.
recent={
'fresh-structural-discovery-r117':['packet/public/report.md','packet/public/structural-screens.md','packet/public/automata.md','packet/public/online-fairness.md','packet/public/reading.md'],
'fresh-arithmetic-discovery-r80':['packet/public/research.md','packet/public/reading-limits.md'],
'fresh-analytic-discovery-r121':['HANDOFF.md','packet/public/report.md','packet/public/continuum.md','packet/public/spectral-locality.md','packet/public/coding-geometry.md','packet/public/reading-limits.md'],
'discovery-analytic-r121-parent':['intake.json'],
'fresh-arithmetic-discovery-r85':['REPORT.md','packet/public/report.md','packet/public/anticanonical-rings.md','packet/public/screens.md','packet/public/reading-limits.md'],
'discovery-arithmetic-r85-parent':['intake.json'],
'fresh-arithmetic-discovery-r86':['REPORT.md','packet/public/report.md','packet/public/dutta-compatibility.md','packet/public/virasoro-history.md','packet/public/other-screens.md','packet/public/reading-limits.md'],
'discovery-arithmetic-r86-parent':['intake.json'],
'fresh-structural-discovery-r122':['REPORT.md','packet/public/report.md','packet/public/hypergraph-feasibility.md','packet/public/matching.md','packet/public/one-relator.md','packet/public/other-screens.md','packet/public/reading-limits.md'],
'discovery-structural-r122-parent':['intake.json']}
observed=[]
for d,fs in recent.items():
 for f in fs:
  p=Path('frontier/campaigns/2026-10-14')/d/f;b=(REPO/p).read_bytes();observed.append(dict(origin=str(p),sha256=sha(b),bytes=len(b),retained=False,note='Read complete named body after truncation repair where necessary; no fresh reading of all private underlying sources implied.'))
save(PACKET/'public/context-register.json',context);save(PACKET/'private/context/recent-identities.json',observed)
print(json.dumps({'canonical':len(sources),'primary_pairs':len(primary),'history_copies':len(history),'context_copies':len(context),'recent_identity_only':len(observed)}))
