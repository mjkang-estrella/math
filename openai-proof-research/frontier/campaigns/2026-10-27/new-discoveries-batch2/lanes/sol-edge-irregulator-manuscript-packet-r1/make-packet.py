from pathlib import Path
import hashlib,json,shutil,re,collections
L=Path(__file__).resolve().parent;P=L/'packet'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
(P/'evidence/audit').mkdir(exist_ok=True)
for f in ['OriginAudit.log','AuditPrint.log']:
 shutil.copyfile(P/'logs'/f,P/'evidence/audit'/f)
inv=json.loads((P/'audit-inventory.json').read_text());counts=dict(collections.Counter(r['origin'] for r in inv))
ids={}
for comp in ['lower','upper']:
 for f in (L/comp/'formal').glob('*.lean'):
  if f.stem not in ['OriginAudit','AuditPrint']:assert sha(f)==sha(P/'formal'/f.name);ids[f'{comp}/{f.name}']=sha(f)
steps=[json.loads(p.read_text()) for p in (P/'logs').glob('*.json')]
prov={'date':'2026-10-29','status':'IMPLEMENTATION PACKET; root final review pending','candidate_credit':0,'campaign_additional':7,'campaign_total':37,'inherited_archives':{'lower':'a94a75354404e27c827dca92c13da7b87df806ec6bda6abd8254376825c520a6','upper':'4d62461a62577e5b2d77045eb2d228814c7481c90b24d45d85383c0313e2d641'},'inherited_mathematical_identity':ids,'modules':14,'unique_actual_declarations':len(inv),'per_module_counts':counts,'paper_sha256':sha(P/'paper.pdf'),'paper_pages':4,'personally_inspected_pages':[1,2,3,4],'no_overfull_boxes':True,'publisher_pdf_sha256':sha(P/'evidence/publisher.pdf'),'publisher_location':'WALCOM2026 pp353-367, Conjecture1 printed356; actual negation stroke visually read','ordinary_and_source_reviews':'See evidence/sol-edge-irregulator-{preliminary-review-r1,current-prior-review-r2}/review.md; bounded existing review 2026-10-29; no new clearance','attribution':'Research manuscript, following accepted campaign manuscripts; Codex preparation disclosed; no personal identity inferred','development_peak_lean_group_rss_kib':max(s['peak_group_rss_kib'] for s in steps),'failures':['Inherited lower early per-module receipt overwrite; not all early individual JSON receipts retained.','Inherited upper early Python launchers lacked separate helper group RSS/wall supervision.','Inherited mathematical and resource/implementation failure histories retained in evidence.','Own first Result compile missing classical instance; first literal AuditPrint generation mishandled numeric private-name parts; sources/logs/receipts retained.','Offline paper builds initially lacked cmr17 metric and cmr12/cmmi12 physical fonts, then hit overfull boxes; resolved with smaller title, included fonts and adjusted paragraph wrapping. First stderr retained; not all intermediate TeX stderr receipts retained.'],'resources':'No cap raise; helpers AS512/groupRSS512MiB CPU210/wall230 BLAS1 40ms; Lean serial-j1-M2700 groupRSS2800MiB CPU210/wall230 45ms AS infinity only Lean; sampled transients cannot be excluded','remaining_gates':['Separate independent final root review of paper/formal correspondence and fresh source-only replay','Root final current-prior refresh and bounded novelty adjudication','Root alone acceptance, integration and any count change'],'external_posting':False,'git_operations':False,'children':0}
(P/'provenance.json').write_text(json.dumps(prov,indent=2)+'\n')
# Strict own helper limit, including supervisor itself; inherited code otherwise unchanged.
for f in ['helper_guard.py','replay_guard.py']:
 p=P/f;s=p.read_text();s=s.replace('LIMIT=512*1024*1024','LIMIT=512*1024*1024\nresource.setrlimit(resource.RLIMIT_AS,(LIMIT,resource.RLIM_INFINITY))\nresource.setrlimit(resource.RLIMIT_CPU,(210,210))\nsignal.alarm(230)');p.write_text(s)
exclude={'logs','paper-build','paper-cache','paper-tmp'}
files=[p for p in P.rglob('*') if p.is_file() and not (set(p.relative_to(P).parts)&exclude) and p.name not in ['manifest.json','dependencies.txt'] and p.suffix not in ['.olean','.ilean','.ir','.o','.so']]
(P/'manifest.json').write_text(json.dumps({str(p.relative_to(P)):sha(p) for p in sorted(files)},indent=2)+'\n')
print('files',len(files),'declarations',len(inv),'counts',counts)
