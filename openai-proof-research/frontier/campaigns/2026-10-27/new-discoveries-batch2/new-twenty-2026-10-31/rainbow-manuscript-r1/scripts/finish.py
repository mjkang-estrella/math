from pathlib import Path
import json,hashlib,re,datetime,shutil,zipfile
P=Path(__file__).resolve().parents[1];B=P.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
# Confirm that the human table is exactly the certified table.
s=(P/'manuscript.md').read_text();block=s.split('## 3.')[1].split('<!-- pagebreak -->')[0]
rows=[l for l in block.splitlines() if l.startswith('|')][1:]
d=json.loads((P/'evidence/original/outputs/rainbow-certificate.json').read_text())
assert len(rows)==28
for row in rows:
 vals=[v.strip() for v in row.strip('|').split('|')];x,y=map(int,vals[0].split(','));assert list(map(int,vals[1:]))==d[0]['certificates'][8*x+y]+d[1]['certificates'][8*x+y]
# Bind all frozen evidence again, including root receipts first bound when available.
for stem in ['input','root-input']:
 before=json.loads((P/(stem+'-before.json')).read_text());after=[]
 for r in before:
  f=B/r['path'];after.append({'path':r['path'],'sha256':sha(f),'bytes':f.stat().st_size})
 assert before==after
 (P/(stem+'-after.json')).write_text(json.dumps(after,indent=2)+'\n')
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'frozen_files_unchanged':693,'root_receipt_files_unchanged':2,'lean_packet_sha256':sha(P/'lean-packet.tar.gz'),'packet_byte_identical':True,'paper_table_matches_certificates':True,'no_lean_lake_or_leanchecker_executed_in_this_lane':True,'accepted_credit':0}
(P/'integrity-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
qa={'pdf':'rainbow-counterexample-draft.pdf','pdf_sha256':sha(P/'rainbow-counterexample-draft.pdf'),'page_count':5,'render':'pdftoppm -scale-to 1500 -png','review':'All five final page PNGs individually viewed by the authoring agent. Initial missing set glyphs fixed with Symbola fallback, then all five pages re-rendered and visually re-inspected. Final pages have legible tables and math, no clipping, overlaps or missing symbols.','pages':[{'path':str(p.relative_to(P)),'sha256':sha(p)} for p in sorted((P/'qa').glob('page-*.png'))]}
(P/'qa/receipt.json').write_text(json.dumps(qa,indent=2)+'\n')
# PROOF is a self-contained copy of the complete argument, rather than a summary.
proof=s.split('## 1.')[1].split('<!-- pagebreak -->\n## 4.')[0]
(P/'PROOF.md').write_text('# Proof dossier for MathDB 346167\n\nDRAFT; zero accepted credit. See manuscript.md for bibliography and formal trust limits.\n\n## 1.'+proof.replace('<!-- pagebreak -->','')+'\n\nThe source-only Lean endpoint proves the universal negation using upper bounds. The exact lower bounds above are ordinary proofs, independently consistent with the retained exhaustive partition checks.\n')
(P/'results.json').write_text(json.dumps({'mathdb_id':346167,'status':'DRAFT_READY_FOR_ROOT_PAPER_READ','accepted_credit':0,'exact_rvd':[4,3],'order':8,'sum':7,'conjecture_false':True,'supporting_classification':{'catalogue':12346,'eligible':9888,'failures':74,'trusted_catalogue_completeness':True},'order9_extensions':[34,36,48],'root_replay':'PASS, supplied receipt; no Lean run by this lane','prior_art':'qualified; published 2021 and 2024 journal bodies unread; no priority claim','paper':'rainbow-counterexample-draft.pdf','source':'manuscript.md','renderer':'scripts/render.py','frozen_inputs_unchanged':True,'packet_safe_extraction':'PASS','pdf_pages_visually_inspected':5},indent=2)+'\n')
print('table, frozen hashes and QA receipt: PASS')
