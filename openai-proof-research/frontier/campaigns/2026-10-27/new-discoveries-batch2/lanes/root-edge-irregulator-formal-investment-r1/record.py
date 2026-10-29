import json,hashlib,datetime
from pathlib import Path
P=Path(__file__).resolve().parent;B=P.parent.parent;cwd=B.parents[4]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
review=P.parent/'sol-edge-irregulator-current-prior-review-r2'
freeze=json.loads((P.parent/'root-edge-irregulator-review-freeze-r1/review-freeze.json').read_text())
src=Path(freeze['source_lane']);assert all(sha(src/n)==h for n,h in freeze['files'].items())
pdf=review/'live/publisher.pdf';assert sha(pdf)=='574aaf95e9d6e94273d2ebc15704bb1209537625d7e59b5282d9a130efb1ceae'
reviewfiles={str(p.relative_to(review)):sha(p) for p in sorted(review.rglob('*')) if p.is_file() and '__pycache__' not in p.parts}
adoption={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'decision':'INVEST_IN_LITERAL_FORMAL_ENDPOINT','credit':0,'counts':[7,37],'scope':'One infinite connected graph family refuting full Bensmail et al. WALCOM2026 Conjecture1; exact I_e(G_t)=3t for m=8t, t>=2, not separate credit.','source_root_read':'Root visually read full publisher printed p356 including literal edge-irregulator definition, recomputed degrees, retained adjacencies, minimum cardinality and all-connected absolute-c conjecture. Publisher PDF hash independently verified.','math':'Root all-t argument and exact corroboration plus independent preliminary MATH PASS adopted.','substantive':'Attachment-stable two-deletion diamond penalty plus independent path penalty yields linear excess; closest actual prior gadgets and positive-labelling theorems do not give a complete bridge. Shortness alone does not exclude; actual prior/subsuming construction would reverse eligibility.','novelty':'Adopt bounded current-prior r2 PASS at recorded17:20UTC heads and selected actual body coverage. Full paths are not full body audits or worldwide absence.','cleared_holds':['current registry head/inventory gap at dated observation','publisher-certified definition/conjecture comparison'],'remaining':['unconditional literal Lean and all axioms/safety/type audits','paper and deterministic packet','independent final review','root fresh extracted replay','acceptance transaction'],'source_pdf_sha256':sha(pdf),'freeze_verified':len(freeze['files']),'review_files':reviewfiles,'assigned_lane':'sol-edge-irregulator-source-formal-r1'}
(P/'ADOPTION.json').write_text(json.dumps(adoption,indent=2)+'\n')
nf=B/'NEXT.md';text=nf.read_text()
text=text.replace('review confirms ordinary math and scoped substantive PASS. Current-prior r2\nreview is pending; no formal investment or credit yet. Root public Git reads','review confirms ordinary math and scoped substantive PASS. Current-prior r2\nclears bounded novelty and publisher wording; root visually checked printedp356.\nFormal investment begins in sol-edge-irregulator-source-formal-r1; credit0.\nAdoption: root-edge-irregulator-formal-investment-r1/ADOPTION.json. Root public Git reads')
text=text.replace('Active Sol high/default: edge-irregulator current-prior r2, fresh finite/algebra r75,','Active Sol high/default: edge-irregulator source formal r1, fresh finite/algebra r75,')
nf.write_text(text)
paths=[str(f.relative_to(cwd)) for folder in (review,P) for f in sorted(folder.rglob('*')) if f.is_file() and '__pycache__' not in f.parts and f.name!='pathspec.txt']
paths.append(str(nf.relative_to(cwd)));(P/'pathspec.txt').write_text('\n'.join(paths)+'\n')
print(json.dumps({'decision':adoption['decision'],'review_files':len(reviewfiles),'freeze_verified':79,'credit':0}))
