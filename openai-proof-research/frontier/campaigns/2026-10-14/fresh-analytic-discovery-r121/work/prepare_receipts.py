from pathlib import Path
import json,hashlib,shutil
root=Path(__file__).resolve().parents[1]; repo=root.parents[3]; packet=root/'packet'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def out(name,x): (packet/'public'/name).write_text(json.dumps(x,indent=2)+'\n')
p=packet/'public/spectral-locality.md';p.write_text(p.read_text().replace('Bach–De Siqueira Pedra–Nachtergaele','Bachmann–De Nittis'))
p=packet/'public/coding-geometry.md';p.write_text(p.read_text().replace('`original-scope.txt`','`original-scope.md`').replace('DefinitionsD.1 and PropositionD.3','PropositionsD.1 and D.3'))
s=json.loads((packet/'public/source-register.json').read_text())
remove=[];keep=[]
for x in s:
 p=packet/x['local'];path=x['path']
 drop=(p.name=='bibliography.tex' or ('A-Fock-space' in path and p.name=='01-introduction.tex') or p.name=='invariant-sk.tex' or p.name=='caustics.tex' or ('The-free-uniform' in path and p.name=='introduction.tex') or ('The-geometric-case' in path and p.name in ['01-introduction.tex','03-windows.tex']))
 if drop:
  x['disposition']='Authenticated acquisition, not relied on semantically; body removed before seal.';remove.append(x);p.unlink()
 else: keep.append(x)
out('source-register.json',keep);out('acquisition-removed.json',remove)
hist={
'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r18/original-scope.md':'Full scope read; actual candidate followed.',
'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r18/candidate.md':'Lines 1–175: covariance inequality, independence, graph exhaustion and start of sampler assembly. Not whole proof.',
'frontier/campaigns/2026-10-14/canonical-sr-contribution-r1/review.md':'Core scope/primary-interface/residual-reduction passages, including sections 1–4; combined display truncated elsewhere. Its verdict is not a premise.',
'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r27/original-scope.md':'Full frozen scope.',
'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r27/234-prefreeze-feasibility.md':'Full feasibility note.',
'frontier/campaigns/2026-10-14/o234-contribution-r2/report.md':'Operative positive/negative outlier reduction, net and monotonicity passages. Some opening display truncation; not whole proof audit.',
'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r16/candidate.md':'Lines 1–170 with initial header truncation: core, framework, count adjustment, mixed cluster enumeration and start of simultaneous iteration.',
'frontier/campaigns/2026-10-14/two-temperature-contribution-r1/review.md':'Full review body read earlier this round; actual integrated-operation comparison, not reliance on rating.',
'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r33/228-conditioned-comparison.md':'Full soft penalty proof and hard-conditioning/reflection-positivity limits.',
'frontier/iterations/i36-harmonic-analysis-discovery.md':'First 170 lines, including simultaneous common-q scope and common physical windows through conditioning.',
'frontier/iterations/i37-supergeometric-avoidance.md':'Search/navigation and previous context only; not freshly read whole proof.',
'frontier/iterations/i153-many-body-spectral-discovery.md':'Keyword-followed lines 119–149 and source269 localization/Gevrey gap passages; larger combined display truncated.',
}
# locate exact I138 filename without fabricating one
for p in (repo/'frontier/iterations').glob('i138*.md'): hist[str(p.relative_to(repo))]='Lines 85–108 on source147 finite-jet diagnostic.'
records=[]
for name,extent in hist.items():
 p=repo/name
 if not p.exists(): raise FileNotFoundError(p)
 local='private/history/'+name
 dst=packet/local;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,dst)
 records.append({'path':name,'local':local,'sha256':sha(p),'bytes':p.stat().st_size,'reading':extent})
out('history-register.json',records)
contexts=['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json','frontier/NEW-TEN-2026-10-14.md']
contexts += [str(next((repo/'frontier/findings').glob(f'R{i:03}*.md')).relative_to(repo)) for i in range(23,41)]
records=[]
for name in contexts:
 p=repo/name;records.append({'path':name,'sha256':sha(p),'bytes':p.stat().st_size})
out('context-register.json',records)
# primary semantic extents are exact extraction line references, not whole-paper claims
extents={
'ruelle1970':'Text 55–155 and 617–780; poor OCR loses formulas. PDF page13, printed139, rendered and semantically inspected. Not complete proof of Theorems0.1–0.2.',
'kkz-published':'Text 1308–1654: PropositionD.3, PropositionD.1 reduction, and proof (a)->(c) through completion; not full converse, bibliography, or main perturbative proof. Title/authors also checked.',
'bdn-v1':'Text 420–674: Assumption3.3, Lemma3.4, Theorem3.5 and proof, beginning Corollary3.6. Title/authors checked; no whole-paper claim.',
'fan-wu-v1':'Text 1915–1980, section5 concentration proof (5.1)–(5.2), derivative norm and SO/O adjustment. No complete high-temperature proof reading.',
'jiang-xi-v1':'Text 118–155 and 200–450: Lemma2.1, reduction to periodic hitting, local-window stability, routing, terminal independence, scale net, open repair and Corollary6.1. Earlier lines were navigation; no full introduction/bibliography claim.'}
a=json.loads((packet/'public/primary-register.json').read_text())
for x in a:x['semantic_reading']=extents[x['id']]
out('primary-register.json',a)
# Keep rendered page private, with explicit derivation and no extra source-rights grant.
p=packet/'private/primary/ruelle1970-printed139.png';shutil.copyfile(root/'work/ruelle-p13.png',p)
out('render-register.json',[{'pdf':'private/primary/ruelle1970.pdf','pdf_page_one_based':13,'printed_page':139,'local':str(p.relative_to(packet)),'sha256':sha(p),'command':'pdftoppm -f 13 -l 13 -scale-to 1800 -png -singlefile','reading':'Entire rendered page, equations (2.21)–(2.25) and accompanying proof.'}])
print({'retained_sources':len(keep),'removed_acquisitions':len(remove),'history_copies':len(hist),'context_receipts':len(contexts)})
