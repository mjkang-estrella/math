from pathlib import Path
import json,hashlib,datetime
R=Path(__file__).resolve().parent
P=R.parents[3]
def sh(b):return hashlib.sha256(b).hexdigest()
def put(n,x):(R/n).write_text(json.dumps(x,indent=2)+'\n')
sl=json.loads((R/'source-ledger.json').read_text())
for x in sl:
 n=Path(x['path']).name; path=x['path'];e='Acquired and authenticated only; no full body read claimed.'
 if 'Hilbert-transform' in path:
  e={'01-introduction.tex':'Full body (298 lines).','02-reductions.tex':'Lines 1–280 and 450–740.','references.bib':'Bibliography navigation; combined terminal display partly truncated; no full-read claim.'}.get(n,e)
 elif 'six-vertex' in path:
  e={'01-introduction.tex':'Full body.','08-main-proof.tex':'Full body.','07-probabilistic-endgame.tex':'Lines 1–200.','06-chiral-gaussianity.tex':'Lines 1–170.','09-endpoint-rotation.tex':'Lines 1–250.'}.get(n,e)
 elif 'with-local-conservation' in path:
  e={'01-introduction.tex':'Full body.','02-framework.tex':'Full body.','03-kernel.tex':'Lines 460–538: quadratic H gain proof. Other kernel statements navigated by label; lower slice proof not read in full.','04-construction.tex':'Full body.','05-cold.tex':'Full body, in later prefreeze reads (1–99 and 100–370).','06-early.tex':'Full body (split 1–220, 220–end).','07-global.tex':'Lines 1–200 only; no full global proof read claimed.','08-compactness.tex':'Lines 177–239: averaging lemma/proof.','09-dilation.tex':'Lines 1–470. Initial combined display partly truncated, then 1–42 and 43–186 reread; 187–410 reread. 471–end not claimed read.','11-branching.tex':'Full body, in three ranges 1–210, 211–489, 490–end; proposition reread 1–87.','12-separation.tex':'Full body.','references.bib':'Full bibliography body.'}.get(n,e)
 elif 'Nonuniqueness-for-the-periodic' in path:
  e={'01-introduction.tex':'Full body.','07-dilation.tex':'Lines 1–240, late prefreeze companion proof comparison.','09-branching.tex':'Lines 1–120, late prefreeze positive-history proof comparison.'}.get(n,e)
 x['read_extent']=e
 x['line_count']=len((R/x['local']).read_bytes().splitlines())
put('source-ledger.json',sl)
pl=json.loads((R/'primary-ledger.json').read_text())
for x in pl:
 x['raw_local']=f"private/primary/{x['id']}/source.tar"
 x['version_claim']='Exact arXiv version in retrieval URL; no latest-version audit or worldwide literature search claim.'
 x['read_extent']={'1603.06037v2':'BEL-0321.tex lines 324–387 (theorem 1.1 and remarks), 688–806 (lemma 4.2 gain proof), 1014–1247 (lemma 5.1 and global bootstrap proof). Lower sections not in these ranges not claimed read.','2606.01331v3':'TeX lines 245–365 theorem/outline interface; combined terminal display partly truncated in outline. Main same-data distinction read at theorem. Lower proof not read.','2608.13758v1':'main.tex lines 210–258, stationary flexibility statements and Boltzmann conjecture context. Lower proof and preamble not read.'}[x['id']]
put('primary-ledger.json',pl)
reads={
 'AGENTS.md':'Full project AGENTS body. No correct ancestor-wide AGENTS search claimed.',
 'sources/upstream.json':'Full body.',
 'sources/CONTENTS.md':'Initial lines 1–120 and selected 083/225/363 catalogue navigation; not full body.',
 'frontier/NEW-TEN-2026-10-14.md':'Lines 1–180 acceptance/status navigation. User overrides obsolete count.',
 'frontier/campaigns/2026-10-14/discovery-analytic-r136-parent/assessment.md':'Full specifically authorized completed parent assessment.',
 'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r136/DERIVATION.md':'Full specifically requested completed original.',
 'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r136/READING-LIMITS.md':'Full specifically requested completed original.',
 'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r136/NOTES.md':'Full specifically requested completed original.',
 'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r63/working-interface.md':'Full operative original.',
 'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r65/diagonal-route.md':'Full operative original.',
 'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r70/README.md':'Full operative original.',
 'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r21/chaos-interface-obstruction.md':'Full operative original.',
 'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r21/read-extent.md':'Full operative original.',
 'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r52/working-interface.md':'Full operative original.',
 'frontier/iterations/i20-pde-kinetic-discovery.md':'Lines 1–220, late prefreeze operative original.'
}
ledger=[]
for name,e in reads.items():
 p=P/name
 if not p.exists():
  ledger.append(dict(path=name,error='Named expected original absent at snapshot; no traversal fallback attempted',read_extent=e));continue
 b=p.read_bytes();q=R/'private/originals'/name;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b)
 ledger.append(dict(path=name,canonical=str(p),local=str(q.relative_to(R)),size=len(b),sha256=sh(b),read_extent=e,observation='Snapshot at late preseal preparation, not a first-read or historical unchanged certificate.'))
put('original-ledger.json',ledger)
print('source',len(sl),'primary',len(pl),'original snapshots',sum('local' in x for x in ledger))
print('missing',[x['path'] for x in ledger if 'error' in x])
