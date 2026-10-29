import datetime, hashlib, json
from pathlib import Path
P=Path(__file__).resolve().parent;B=P.parent.parent;cwd=B.parents[4]
S=P.parent/'sol-edge-irregulator-lower-source-formal-r2'
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for c in iter(lambda:f.read(1048576),b''):h.update(c)
    return h.hexdigest()
E=P/'extracted'
receipt=json.loads((E/'replay-receipt.json').read_text())
assert receipt['status']=='SOURCE_REFUTATION_REPLAY_PASS'
assert receipt['declaration_count']==136
worker=json.loads((S/'verification-fresh/replay-receipt.json').read_text())
assert receipt['declarations']==worker['declarations']
for n in ('OriginAudit.log','AuditPrint.log'):
    assert sha(E/'logs'/n)==sha(S/'verification-fresh/logs'/n)
manifest=json.loads((E/'manifest.json').read_text())
for n,h in manifest.items():assert sha(E/n)==h and sha(S/'component'/n)==h,n
old=P.parent/'sol-edge-irregulator-source-formal-r1/formal'
for n in ('Source','Boundary','Gadget','Edges','Degrees'):
    assert sha(E/'formal'/f'{n}.lean')==sha(old/f'{n}.lean')
actual=[]
for d in receipt['declarations']:
    assert set(d['axioms'])<= {'propext','Classical.choice','Quot.sound'}
    assert not any(d[k] for k in ('unsafe','partial','axiom'))
    if d['origin'] in ('Local','Lower','Charges','Transport','Refutation'):
        actual.append(d)
record={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'status':'ROOT_FRESH_EXTRACTED_SOURCE_REFUTATION_PASS','credit':0,'counts':[7,37],
 'root_read':'Actual Local, Lower, Charges, Transport and Refutation sources; Source/Gadget/Edges/Boundary/Degrees previously inspected. New actual declaration records retained below. Complete machine audits compared byte-identically to independent worker replay.',
 'source_endpoint':'EdgeIrregulator.source_refutation : ¬ EdgeIrregulator.SourceClaim',
 'source_scope':'All Fin n connected finite simple graphs, arbitrary real absolute c>=1, genuine deletions and recomputed retained degrees. Nat.find attained minimum equivalence and isomorphism transport proved, not assumed.',
 'archive_sha256':receipt['archive_sha256'],'root_receipt_sha256':sha(E/'replay-receipt.json'),
 'proof_modules':receipt['proof_modules'],'declarations':136,'inherited_five_sources_identical':True,
 'root_peak_sampled_rss_kib':max(s['peak_group_rss_kib'] for s in receipt['steps']),
 'worker_failure_limits':'FAILURES.md preserved. Early individual per-module resource receipts overwritten; failure source/log copies remain. Final extracted replay complete. No caps raised; sampled transients not excluded.',
 'remaining':['explicit upper witness and exact-minimum combination','manuscript and deterministic final packet','independent final review','final root acceptance transaction'],
 'new_actual_declarations':actual}
(P/'ADOPTION.json').write_text(json.dumps(record,indent=2)+'\n')
nf=B/'NEXT.md';t=nf.read_text()
t=t.replace('Initial formal component replay passes five modules/89 declarations, but the\nunconditional source negation remains absent. Continuation split into global\nlower bound/source transport and explicit upper witness; credit0. See\nroot-edge-irregulator-component-handback-r1/ADOPTION.json.', 'Root fresh extracted source refutation PASS10 modules/136 actual declarations,\nstandard-three axioms only, no residual premises. Lower bound, actual disjoint\ncharges and source vertex transport are closed. Upper witness still running;\npaper/final review/acceptance remain. Credit0. See\nroot-edge-irregulator-source-replay-r2/ADOPTION.json.')
t=t.replace('Active Sol high/default: edge-irregulator lower/source formal r2, upper-witness\nformal r2, and fresh source discovery r78.', 'Active Sol high/default: edge-irregulator upper-witness formal r2,\nfresh finite/algebra discovery r78 and fresh analytic discovery r79.')
nf.write_text(t)
paths=[]
for folder in (S,P):
    for f in sorted(folder.rglob('*')):
        if not f.is_file() or '__pycache__' in f.parts or 'verification-fresh' in f.parts:continue
        if f.suffix in ('.olean','.ilean','.o') or f.name=='pathspec.txt':continue
        paths.append(str(f.relative_to(cwd)))
paths.append(str(nf.relative_to(cwd)))
(P/'pathspec.txt').write_text('\n'.join(paths)+'\n')
print(json.dumps({k:record[k] for k in ('status','declarations','root_peak_sampled_rss_kib','archive_sha256')}))
for d in actual:print(d['name'],d['actual_type'],d['axioms'])
