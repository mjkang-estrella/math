from pathlib import Path
import hashlib,json,shutil,subprocess,sys,zipfile,platform,importlib.metadata
R=Path(__file__).resolve().parent;P=R/'packet'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(65536):h.update(b)
 return h.hexdigest()
def dump(p,obj):p.write_text(json.dumps(obj,indent=2)+'\n')
def run(args,log):
 r=subprocess.run(args,capture_output=True,text=True);log.write_text(r.stdout+r.stderr);assert r.returncode==0,log
rows=json.loads((R/'freeze-before.json').read_text())
for row in rows:assert sha(Path(row['path']))==row['sha256'],row['path']
dump(R/'freeze-after.json',rows)
audit=R/'fresh-source-replay/logs/FullAudit.log'
assert sha(audit)==sha(P/'component'/ 'logs/FullAudit.log') if (P/'component/logs/FullAudit.log').exists() else True
assert sha(audit)==sha(R.parent/'sol-factorial-product-source-formal-r1/logs/FullAudit.log')
for name in ['portable-receipt.json','logs/FactorialProduct.log','logs/FactorialProduct.json','logs/FullAudit.log','logs/FullAudit.json']:
 dest=P/'evidence/fresh-replay'/name;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(R/'fresh-source-replay'/name,dest)
fail='''# Preserved preparation failures and qualifications

The immutable source-only.zip and all mathematical/audit/Lean guard bytes remain unchanged.
The first legacy replay stopped before compilation at verify.py line24: historical NEXT.md hash
5dbf6b6bee3f9450ab93c0ca0c7027a028ef8adb9ebbc00629833fc194df6c78 no longer matches the shared current file.
No shared file was restored or edited. strict-replay/ retains that failed extraction. Portable replay checks
all shipped copied inputs and exact pinned tool/dependency bytes, rather than requiring historical campaign
originals to remain at recorded filesystem paths. It compiles and exhaustively audits unchanged source.
This is a disclosed orchestration change, not an original legacy-replay PASS claim.

First PDF builder failed: ModuleNotFoundError: No module named 'reportlab'. Installed ReportLab4.4.3,
Pillow13.0.0 and charset-normalizer3.5.2 into this lane only under the unchanged helper guard.
The PDF skill marker command failed under AS512MiB: V8 Fatal process out of memory:
SegmentedTable::InitializeTable (subspace allocation); guard_exit -5, peak group RSS25153536 bytes.
A bounded retry with --jitless --no-expose-wasm --no-node-snapshot failed: node bad option --no-expose-wasm,
exit9. The requested successful skill marker was unavailable under the mandatory unchanged cap; no cap was
raised. PDF generation continued using the working Python builder. These are tool-output excerpts, not
independently stored raw stderr logs. No successful marker is asserted.

Initial broad inspection outputs were truncated and are not treated as complete semantic reads; bounded
reads of the complete mathematical module and both complete reviews followed. First rendering showed a
black square for Jevtic's diacritic and an awkward table split; the final builder transliterates that name,
keeps the totals table together and uses slightly tighter typography. Every final manuscript page was viewed.
Historical Lean failures are retained unchanged in component/logs and explained in component/FAILURES.md.
No resource cap failure occurred in the successful Lean replay; sampled resource bounds are not proofs of
continuous peak usage. Literature coverage and all dissent remain bounded as stated in both full reviews.
'''
(P/'PREPARATION-FAILURES.md').write_text(fail)
dump(P/'build-environment.json',{'python':sys.version,'platform':platform.platform(),
 'packages':{n:importlib.metadata.version(n) for n in ['reportlab','pillow','charset-normalizer']},
 'poppler':subprocess.run(['pdftoppm','-v'],capture_output=True,text=True).stderr,
 'zlib':__import__('zlib').ZLIB_RUNTIME_VERSION,'pdf_invariant':True})
prov={'status':'PENDING_INDEPENDENT_FINAL_REVIEW','credit':0,'acceptance':False,'count_change':False,
 'component_sha256':sha(P/'source-only.zip'),'mathematical_source_changed':False,
 'author_convention':'Research manuscript','new_network_research':False,
 'source_pdf_sha256':sha(P/'component/inputs/source.pdf'),
 'source_url':'https://d-nb.info/1346963460/34','source_label':'published Problem5.6 printedp1281; preprint12.6',
 'fresh_replay':'portable source-only; historical-original NEXT assertion excluded explicitly',
 'actual_audit_byte_identical_to_original':True,'full_reviews_preserved':True,
 'dissent':'complete smooth restriction plus classical concentration/pigeonhole proof; Candela-Helfgott Prop2.1 mechanism established',
 'historical_limit':'Jevtic DOI10.1137/S0895480194265623 body unread after403; bounded registry coverage',
 'scope':'solo; no git, other-lane writes, browser/account operations, messages, uploads or publishing',
 'resources':'unchanged helper AS/groupRSS512MiB CPU210 wall230s BLAS1; Lean j1 M2700 groupRSS2800MiB CPU210 wall230s',
 'marker_failure_disclosed':True}
dump(P/'provenance.json',prov);dump(R/'provenance.json',prov)
# Correct preliminary README version estimate and document exact dependency setup.
txt=(P/'README.md').read_text().replace('Poppler 24.02.0','Poppler (version recorded below)')
txt+='\nInstall Python build packages in a local environment: reportlab==4.4.3 pillow==13.0.0 charset-normalizer==3.5.2.\nSee PREPARATION-FAILURES.md for the legacy NEXT hash and unavailable PDF marker qualifications.\n'
(P/'README.md').write_text(txt)
# All payload bytes are fixed before archive construction. No compiled artifacts.
assert not any(p.name.endswith(('.olean','.olean.private','.olean.server','.ilean','.ir','.ir.sig')) for p in P.rglob('*'))
dump(P/'manifest.json',{str(p.relative_to(P)):sha(p) for p in sorted(P.rglob('*')) if p.is_file() and p.name!='manifest.json' or False})
# Include nested component manifest: only the top-level manifest excludes itself.
dump(P/'manifest.json',{str(p.relative_to(P)):sha(p) for p in sorted(P.rglob('*')) if p.is_file() and p!=P/'manifest.json'})
run([sys.executable,str(P/'pack.py'),str(R/'packet.zip')],R/'pack.log')
E=R/'rebuild-extraction';assert not E.exists()
with zipfile.ZipFile(R/'packet.zip') as z:z.extractall(E)
before=sha(E/'paper.pdf')
run([sys.executable,str(E/'certificate.py')],R/'rebuild-certificate.log')
run([sys.executable,str(E/'build_paper.py')],R/'rebuild-paper.log')
assert sha(E/'paper.pdf')==before
run([sys.executable,str(E/'pack.py'),str(R/'packet-rebuilt.zip')],R/'rebuild-pack.log')
assert sha(R/'packet-rebuilt.zip')==sha(R/'packet.zip')
dump(R/'rebuild-receipt.json',{'status':'BYTE_IDENTICAL_FROM_FRESH_EXTRACTION','paper_sha256':before,'packet_sha256':sha(R/'packet.zip'),'certificate_regenerated':True})
shutil.copyfile(P/'paper.pdf',R/'paper.pdf')
print('sealed, extracted PDF and ZIP rebuild byte-identically')
