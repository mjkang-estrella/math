from pathlib import Path
import json,hashlib,shutil
R=Path(__file__).resolve().parents[1];P=R/'packet';repo=R.parents[3]
def write(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
reg=json.loads((P/'public/source-register.json').read_text())
read={
'078/01-introduction.tex':'Lines 1–160; introduction and theorem interface. Remainder not a complete semantic read.',
'078/12-multiplier.tex':'Complete semantic read: thm:oscillatory-estimate and full multiplier reduction, global Hessian extension, kernel/shell/interpolation proof.',
'083/01-introduction.tex':'Complete semantic read; exact supremum outside L2, deterministic subcollections and Hilbert-valued interface.',
'090/06-gaussian-energy-transfer.tex':'Complete semantic read of prop:density-lp, lem:gaussian-duality and proofs.',
'090/08-renormalized-jellium.tex':'Displayed complete in a combined output with earlier material truncated; field normalization, periodic heat comparison and proof through cor:riesz-jellium/confinement visible. No fresh appendix read; not used as a new long-range proof.',
'090/atomic-main.tex':'Lines 650–680 and 1930–2040 read (coordinate normalization and first-cell portion of prop:global-signs); labels elsewhere searched. No full atomic construction or certificate read/audit.',
'090/packing-main.tex':'Complete main/input map and abstract only; no section proof read. Navigation only.',
'219/01-introduction.tex':'Complete semantic read; uniform-potential fixed-energy theorem and interface map.',
'219/02-tree.tex':'Complete semantic read including prop:tree-stability proof, boundary continuity, covariance/logdet and density conclusions.',
'219/03-local-law.tex':'Lines 1–130 semantic read: spectral averaging/Wegner, compression-tail and Ward interfaces. Rest only label navigation.',
'219/04-marked-entropy.tex':'Lines 100–174 semantic read including full lem:conditional-mean proof. Rest label navigation, not full entropy proof.',
'219/07-insertion.tex':'Lines 1–230 semantic read: interval pairing, root-excluded environment bounds, small coefficients/moments and insertion setup. Later cuts/replacement proof not read.',
'219/clean-switching.tex':'Lines 1–240 read: complete prop:continuous-switching proof, Gaussian insertion statement and beginning of first cut. Not the complete later replacement proof.',
'341/01-introduction.tex':'Lines 1–200 displayed with a small combined-output truncation; theorem/cohomology/Kahler/type consequences read. No full-introduction claim.',
'341/05-families.tex':'Lines 1–150 semantic read; entire lem:compatible-family proof. Remaining file only label navigation, no full family-curves proof read.',
'341/11-endpoint.tex':'Complete semantic read including lem:endpoint-kahler-class, lem:endpoint-hodge-type, final construction.',
'341/september-main.tex':'Complete input map only; September proof sections not read anew.',
'366/reductions.tex':'Complete semantic read: reduction to bounded reduced SBV minimizer, clipping and boundary gluing operations.',
'366/completion.tex':'Complete semantic read (reread before seal): cor:classification, thm:main completion, local finiteness, cor:weak-l4 and proof.'}
kept=[];removed=[]
for e in reg:
 key=e['family']+'/'+Path(e['local']).name
 if key not in read:
  (P/e['local']).unlink(); e['reading']='Acquired but not semantically read; removed before sealing.'; e['retained']=False;removed.append(e)
 else:e['reading']=read[key];e['retained']=True;kept.append(e)
write(P/'public/source-register.json',kept);write(P/'public/acquisition-only.json',removed)
pr=json.loads((P/'public/primary-register.json').read_text())
extents={
'goww':'LF lines175–285 (§2 slicing/pseudoconformal) and772–920 (Lemmas3.8/3.10 rescaling and Taylor-amplitude proof); first title page. v1 version page checked. Not whole paper or later published version.',
'dlf':'LF lines1475–1555 Prop2.5.6 and variation proof;8190–8265 entire Thm6.1.6 proof/interface;995–1078 compactness setup/Thm2.2.3;10064–10320 AppendixD Steps0–2 and partial Step3. Later AppendixD unread. Version page v2 checked. No whole book read.',
'll':'LF lines300–380 Thm1.18 statement/setup and1575–1665 decomposition/full Lemma4.25 proof with maximal-function footnote. Not whole memoir.',
'as':'LF lines1–190 introduction/POT hypotheses, Theorem1.1 and beginning Theorem1.2; combined display slightly truncated. Proof sections not read. No proof/priority clearance inferred.',
'hmynew':'LF lines1–170 introduction/setup/Thm1.1; later proof not read. External primary, not stipulated. Extraction font warning retained.'}
for e in pr:e['reading']=extents[e['id']]
write(P/'public/primary-register.json',pr)
history={
'frontier/iterations/i80-geometric-flows-computation-discovery.md':'First120 lines read; equivariant/family and Ricci screens complete in this extent; later forcing proof not used.',
'frontier/iterations/i122-variational-free-boundary-discovery.md':'Opening/first170-line attempted read with combined truncation; operative polynomial-complexity/isolation screen read. No complete report claim.',
'frontier/iterations/i137-crystalline-coherence.md':'First140 lines previously; fresh reread of sections2–3 and lines140–205 (atlas proof), with a whole-file display truncated at middle. Long-range later sections and old primary bodies not fully reread.',
'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r24/quantitative-markov-screen.md':'Complete read; explicit-modulus gap and direct-sum uniformity comparison.',
'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r27/234-prefreeze-comparison.md':'Complete read; earlier orthogonal-outlier interface excluded.',
'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r43/report.md':'Complete read; stochastic boundary gap not selected.',
'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r65/flow-route.md':'Complete read.',
'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r67/selected-diagonal-status.md':'Complete read.',
'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r25/screen-log.md':'Complete late read before sealing; no freeze.',
'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r113/packet/public/operation-comparison.md':'Actual history-screen section and contextual rg excerpts read; no complete fresh proof read.',
'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r23/payload/342-parametric-screen.md':'Complete late read before sealing; actual fixed-cohomology finite-rank augmentation and relative patch proof; no freeze.',
'frontier/campaigns/2026-10-14/fresh-structural-discovery-r119/REPORT.md':'Complete report read; detailed two-frame/research bodies not freshly read in this analytic round.',
'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r83/REPORT.md':'Complete report read; detailed arithmetic bodies not freshly read in this analytic round.'}
# Source usage is recorded independently of any prior author rating.
for fam in ['118','119']:
 files=['HANDOFF.md','packet/public/report.md','packet/public/reading-limits.md']
 files+=['packet/public/'+s+'.md' for s in (['operator-compactness','conditioning','geometric-screens'] if fam=='118' else ['spin-moments','atomic-conditioning','sle-clock','geometric-screens'])]
 for f in files:
  q=f'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r{fam}/{f}'
  if (repo/q).exists():history[q]='Complete semantic read; previous-round scope/comparison only, no independent validation of its underlying theorem.' if not (fam=='118' and f.endswith('reading-limits.md')) else 'Acquired here for reference; report read, this entire limits body not freshly read.'
h=[]
for i,(path,extent) in enumerate(history.items()):
 b=(repo/path).read_bytes();dest=f'private/history/h{i:02d}-{Path(path).name}';(P/dest).write_bytes(b);h.append(dict(path=path,local=dest,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),reading=extent))
write(P/'public/history-register.json',h)
ctx=[]
for path in ['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json','frontier/NEW-TEN-2026-10-14.md']:
 b=(repo/path).read_bytes();ctx.append(dict(path=path,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()))
write(P/'public/context-register.json',ctx)
print('retained source',len(kept),'removed unread',len(removed),'primary',len(pr),'history',len(h))
