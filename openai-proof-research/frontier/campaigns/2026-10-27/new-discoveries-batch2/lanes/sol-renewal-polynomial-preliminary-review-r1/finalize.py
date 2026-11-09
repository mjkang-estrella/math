import pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def put(n,x):(L/n).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
freeze=json.loads((L/'freeze-record.json').read_text())
for r in freeze['records']:
 assert h(L/r['copy'])==r['sha256']
 if r['kind']=='scientific':assert h(pathlib.Path(r['original']))==r['sha256']
access=json.loads((L/'access.json').read_text())
for r in access:
 if 'sha256' in r:assert h(L/r['original'])==h(L/r['copy'])==r['sha256']
put('coverage.json',dict(primary_bodies=[dict(id='2307.00545v1',pages='1–7 complete body, definitions2.1–2.9, propositions3.1/3.3/3.5, theorem3.6, conjecture3.7, proposition3.8 and full proofs'),dict(id='2307.00545v2',pages='1–8 complete body, same relevant labels'),dict(id='10.53656/math2024-2-1-pro',pages='111–118 complete journal body, definitions(1)–(8), propositions3.1/3.3/3.5, theorem3.6, conjecture3.7 and full proposition3.8 proof')],search_metadata_only=['frozen/current0-frozen/0-current0.xml','frozen/prior0-frozen/0-prior0.xml','frozen/prior1-frozen/0-prior1.xml','other current query snapshots inspected as metadata; unrelated subjects not prior-proof bodies'],not_covered=['Feller actual book proof bodies','Mitov–Omey actual book proof bodies','current public registry head or complete histories','complete citing-paper network','independent published earlier refutation'],parked=['previously inaccessible historical intervals: not retried','denied GitHub API/raw/codeload/diff/patch, ScienceDirect, Google challenge routes'],boundary_coverage=['closed simplex including all faces and vertices','every integer renewal time n>=1','periodic and degenerate laws','total degree3 after eliminating p4','strict domination somewhere, not everywhere'],chronology=dict(arxiv_v1='2023-07-02T11:38:18Z',arxiv_v2='2024-05-01T18:49:07Z',journal_print='2024-04-29 per Crossref',journal_online='2024-04-30 per Crossref',crossref_deposit='2025-06-09; not publication',review='2026-10-30'),live_access_record='access.json',novelty_conclusion='UNCLEARED, not a failed-search inference'))
(L/'failures.md').write_text('''# Retained failures and limits

Candidate failures are preserved verbatim in frozen/FAILURES.md, including overwritten first search responses and the failed xyz subclass route. They are not silently repaired or used as retained original-byte evidence.

This review initially used a broad native rg inventory with duplicated roots, yielding truncated output. It read no scientific body and made no edits. Later inventories/reads were bounded. The initial administrative cat output was also truncated; the guarded extract.py subsequently parsed both full snapshot JSON objects, checked top-level keys and found no renewal mention. The first draft freeze copied flat target PDFs/text from both the source directory and the scout frozen directories; it does not recursively copy historical evidence trees.

The first check.py run exited 1 at line16, `assert p==xx*yy+xx**2*(zz-1)`, because SymPy structural equality compared an expanded expression with an unexpanded one. Traceback ended in AssertionError; guard exit1, no cap violation, sampled peak59748352 bytes, wall0.320848s. The corrected checker uses exact expanded subtraction and passes. The mathematical identity was unchanged. This failed checker is not treated as evidence of mathematical failure. Original assertion retained here explicitly.

A draft review said common support was exactly {xyw}; inspection corrected it to {xyw,xyz} before finalization. The coefficient-subtraction conclusion using xyw is unchanged. No earlier draft is presented as a verified artifact.

No access denial, challenge, resource termination or TLS bypass occurred in this review. All four attempted live requests returned200. There were no denied-route retries. Registry history, citing-network and book proof-body limitations remain explicit in coverage.json.
''')
guard='/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
(L/'RUN.md').write_text(f'''# Capped replay

Run each command with OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1.

    python {guard} python {L}/check.py
    python {guard} python {L}/verify.py

The fixed guard enforces AS/groupRSS512MiB CPU210s wall230s. check.py requires installed SymPy, uses exact rational polynomial expansion and a bounded diagnostic grid. No Lean. Do not rerun freeze.py/access.py/finalize.py for verification: they are construction/retrieval records. verify.py is read-only except its receipt. To preserve final manifest identity, use verify.py directly on this completed lane; replaying check.py writes its deterministic result file.
''')
put('provenance.json',dict(lane=L.name,generated_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),recommendation='EXCLUDE conditional on root adopting explicit routine-adaptation bridge; otherwise HOLD',decisions={'SOURCE':'PASS','MATH':'PASS','SUBSTANTIVE':'FAIL recommended, root adjudicates','NOVELTY':'HOLD / bounded uncleared','FORMAL-FEASIBILITY':'PASS in principle only'},counts={'additional':9,'total':39,'next':40,'authority':'root alone'},freeze_record='freeze-record.json',live_access='access.json',extraction='extraction.json',coverage='coverage.json',failures=['failures.md','frozen/FAILURES.md'],checks='check-results.json',source_hashes=[r for r in freeze['records'] if r['kind']=='scientific'],live_source_hashes=access,caps={'AS_MiB':512,'groupRSS_MiB':512,'CPU_s':210,'wall_s':230},guard_path=guard,guard_sha256=h(pathlib.Path(guard)),no_credit_claim=True))
put('manifest.json',{str(p.relative_to(L)):dict(sha256=h(p),bytes=p.stat().st_size) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']})
print('final files written; separate verify.py invocation still required')
