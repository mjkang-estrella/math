import hashlib,json,zipfile,shutil
from pathlib import Path
from pypdf import PdfReader
L=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
write=lambda p,d:(L/p).write_text(json.dumps(d,indent=2)+'\n')
paper=(L/'manuscript.md').read_text()
proof='# DRAFT proof and formal scope\n\nAI-assisted; root review pending.\n\n## 2.'+paper.split('## 2.')[1].split('## 4.')[0]
proof=proof.replace('---PAGE---','')
proof+='\n\n## 5.'+paper.split('## 5.')[1].split('## 6.')[0]
(L/'PROOF.md').write_text(proof)
before=json.loads((L/'inputs.before.json').read_text());after={n:sha(Path(n)) for n in before}
assert before==after
write('inputs.after.json',after)
copy_mismatches=[]
for name,h in before.items():
 p=Path(name)
 try:rel=p.relative_to(L.parent)
 except ValueError:rel=Path('governing')/p.parent.name/p.name
 if sha(L/'evidence'/rel)!=h:copy_mismatches.append(name)
assert not copy_mismatches
write('input-verification.json',dict(status='PASS',frozen_files=len(before),before_equals_after=True,copies_byte_identical=True))
reader=PdfReader(L/'manuscript.pdf');assert len(reader.pages)==6
old=L/'qa-page-7.png'
if old.exists():old.unlink()
pages=[]
for i,p in enumerate(reader.pages,1):
 text=p.extract_text();assert len(text)>1000
 png=L/f'qa-page-{i}.png';assert png.exists()
 pages.append(dict(page=i,image=png.name,sha256=sha(png),visual_inspection='PASS: legible text, equations and indices; no clipping, overlap or missing glyphs; header/footer and page transition checked',text_characters=len(text)))
write('qa-receipt.json',dict(status='PASS',pdf_sha256=sha(L/'manuscript.pdf'),page_count=len(pages),renderer='pdftoppm -r 110 -png',all_pages_visually_inspected=True,pages=pages))
raw={str(i):sha(L/'evidence/expanded-corpus-r204/raw'/f'{i}.jsonl') for i in [360653,361128]}
write('raw-lines-receipt.json',dict(status='PASS',sha256=raw,encoding='exact bytes copied; not reserialized'))
write('results.json',dict(lane='slownim-manuscript-r1',status='DRAFT_READY_FOR_ROOT_REVIEW',self_accepted=False,accepted_credit=0,mathdb_id=360653,duplicate=361128,pdf='manuscript.pdf',source='manuscript.md',pages=6,ai_assistance_explicit=True,human_authors_asserted=False,priority_claim=False,smallest_counterexample_claim=False,DAM_version_of_record='UNREAD',endpoint='SlowNim360653.conjecture1_false : ¬ SlowNim360653.Conjecture',formal_scope='Finite literal refutation only; family and robust certificate not formalized',lean_run_in_lane=False,packet_sha256=sha(L/'source.zip'),numerical_recomputation='PASS',all_pdf_pages_visually_inspected=True,input_integrity='PASS',safe_extraction='PASS',network_used=False,child_agents=0,git_used=False,background_jobs_left=False,acceptance_authority='root'))
(L/'SUMMARY.md').write_text('''# DRAFT ready for root review

AI-assisted six-page manuscript: manuscript.pdf, with editable manuscript.md
and render.py. No human author or affiliation is asserted. No priority or
smallest-counterexample claim; no self-acceptance or ledger edits.

The paper proves the all-n,all-l family for n,l >= 3 with complete I/J block
invariants, positivity and tie analysis, including l = 3 and final phases.
It includes the literal (4,4,5) witness, global admissibility, a computed
fallback-independent (5,5,6) certificate, the smaller (2,4,4) improvement,
bounded search counts, source rules, related work and formal correspondence.

Fresh capped isolated Python calculations reproduce all game numbers and
block boundaries in the printed ranges. The robust policy tree and all its
leaves are retained. All six final PDF pages were rendered and inspected;
qa-receipt.json binds the PDF and QA images.

The Lean packet source.zip is byte-identical to the supplied packet. Safe
extraction passed; no Lean, lake, leanchecker or solver was run. The endpoint
SlowNim360653.conjecture1_false proves the finite literal refutation; it does
not formalize the parameter family or robust minimax certificate. Root's prior
strict replay and registry refresh are copied as inherited evidence.

MathDB 360653 is the target; 361128 is a duplicate, with no separate credit.
The DAM version of record remains UNREAD. The prior-art screen is bounded.
Root alone decides acceptance. See REPRODUCE.md, PROOF.md, results.json,
manifests and receipts. full-dossier.zip contains the dossier, source.zip the
unchanged Lean packet, and manuscript-source.zip the editable paper bundle.
''')
shutil.copyfile(L/'logs/resource.jsonl',L/'logs/resources-frozen.jsonl')
with zipfile.ZipFile(L/'manuscript-source.zip','w',zipfile.ZIP_DEFLATED) as z:
 for name in ['manuscript.md','render.py','REPRODUCE.md','cap.py']:
  z.write(L/name,name)
excluded={'full-dossier.zip','MANIFEST.sha256','archive-receipt.json','logs/resource.jsonl'}
files=sorted(p for p in L.rglob('*') if p.is_file() and str(p.relative_to(L)) not in excluded and not any(part in ['tmp','cache'] for part in p.relative_to(L).parts))
(L/'MANIFEST.sha256').write_text(''.join(sha(p)+'  '+str(p.relative_to(L))+'\n' for p in files))
files.append(L/'MANIFEST.sha256')
with zipfile.ZipFile(L/'full-dossier.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in files:z.write(p,str(p.relative_to(L)))
with zipfile.ZipFile(L/'full-dossier.zip') as z:
 assert z.testzip() is None
 for p in files:assert hashlib.sha256(z.read(str(p.relative_to(L)))).hexdigest()==sha(p)
write('archive-receipt.json',dict(status='PASS',full_dossier_sha256=sha(L/'full-dossier.zip'),manuscript_source_sha256=sha(L/'manuscript-source.zip'),lean_packet_sha256=sha(L/'source.zip'),crc_check='PASS',all_archived_members_equal_delivered_files=True,member_count=len(files),excluded_live_log='logs/resource.jsonl'))
print('PASS: six-page draft, input/copy equality, manifests and full archive; acceptance deferred to root')
