from pathlib import Path
import json,hashlib,datetime,subprocess,sys
D=Path(__file__).resolve().parent;L=D.parent;B=L.parent
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
flat=json.loads((D/'flat-bindings.json').read_text())
for p in [L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',B.parent.parent.parent.parent/'AGENTS.md']:
 if p.exists() and str(p) not in {r['path'] for r in flat}:flat.append({'path':str(p),'sha256':H(p),'size':p.stat().st_size})
(D/'flat-bindings.json').write_text(json.dumps(flat,indent=2)+'\n')
pv=json.loads((D/'source-provenance.json').read_text())
fail=[r for r in pv if 'failure' in r]
fail.append({'deviation':'An early structural head probe displayed one unassigned not_retrieved sentinel row (413524, null statement) from chunk0020 before the all-chunk verification. No mathematical screening or review credit was assigned to that row; only assigned fifty statements were screened. This pre-verification display is retained as a bind-first/scope deviation.'})
fail.extend([{'route':'initial head/rg of gyarfas.txt/christensen.txt','failure':'files not yet present; neither body read; subsequent fetches failed'},{'deviation':'HTML derivative hashes computed before reading but derivative-bindings.json persisted after initial reads of queue/hovey/topp52 text. This ordering deviation is retained, not retroactively cured. Bytes now bound and independently verified.'},{'gate':'current proof registry unavailable; zero MathDB requests; novelty HOLD'},{'parked_routes':'AIM/Kourovka/EGRES/AIProofWatch; DMGT TLS; ProjectEuclid challenge; ResearchGate403; OEIS A274199/internal403. No retries or alternate-route fishing.'}])
(D/'failures.json').write_text(json.dumps(fail,indent=2)+'\n')
coverage={'record_statements_read':50,'source_complete_mathematical_statements_claimed':False,'primary_selected_question_passages_ids':[388670,390404,390405,390407,390411],'successor_selected_theorem_and_proof_passages_ids':[388670],'whole_body_read_ids':[],'full_dependency_audit_ids':[],'registry_clear_ids':[],'source_scope_holds':22,'proposals':0,'baseline_assignment':5383,'latest_root_baseline':5433,'not_integrated_delta':50,'no_shared_coverage_edits':True,'queue_source':'TOPP p52 and arXiv1904.04791v5; selected text ranges430-450,995-1081,1240-1274','search_evidence':'web primary-source search identified arXiv1904.04791, arXiv2207.02920 and Christensen-Hovey author PDF. Search metadata is a lead only, never body clearance.'}
(D/'source-coverage.json').write_text(json.dumps(coverage,indent=2)+'\n')
(D/'SUMMARY.md').write_text('''# r578 independent fifty-record breadth screen

50/50 assigned literal cached statements read, with original chunk/line, exact UTF-8 statement SHA256 and canonical-record SHA256 in dispositions.json and literal-records.json. This is record-level screening, not fifty self-contained source-complete mathematical statements. The immutable r577 assignment baseline is 5,383; authoritative r579 baseline is 5,433. This lane contributes 50 unintegrated record reviews. Root alone reconciles totals. Counts stay 9 additional /39 total /next40.

Zero hypotheses proposed. One published-theorem exclusion: 388670, bounded planar queue-number. Primary TOPP question and arXiv1904.04791v5 Theorem1 plus selected Section4/4.1 proof passages were read. The universal planar quantifier matches exactly; no complete dependency replay or whole-paper clearance is claimed. A smaller constant or formalization earns no credit. Two strong prior leads,390733 and390411, remain HOLD because successor bodies were inaccessible. All other dispositions state individual technical obstacles;22 rows explicitly need definitions/conventions restored. Open labels, tags and empty solution lists supplied no eligibility evidence.

Integrity checks independently verified r577/r579 exact payloads and direct original/copy pairs without running their verifiers; all20 original r301 corpus chunks in place and all8 frozen_inputs matched the bound r301 manifest. All three current active fifty-ID reservations are mutually disjoint, outside5,433 coverage and protected IDs. Claude r504 reservations preserved. No corpus copy, historical-tree expansion, shared edit, git operation, formalization, manuscript or credit change occurred.

Selected source coverage, exact URLs/UTC/bytes/hash and access failures are separate JSON files. No complete successor dependency audit or live registry clearance was obtained. HTML text hashes were computed before reading but the derivative binding file was persisted afterward for initial queue/hovey/topp52 reads: explicit timing deviation, not retroactively repaired. PDFs were not obtained; no PDF content was extracted or viewed. arXiv coloring HTML404, author PDF certificate failure and Christensen-Hovey timeout were retained without bypass/retry. Missing-text checks were retained as failed reads. Zero MathDB requests; all inherited parked routes, including OEIS A274199/internal403, remain parked.

Adjudications and restoration flags are retained through bound r579 references and prior-context-check.json, including344924/386396/387650 incomplete;366370 excluded source restriction;365437/365439 parked;372522 proof gap is not a refutation;337963 parked;338290/339564/372627 retired/excluded. r304 accepted-family and historical exclusions and r363 Cayley decision were read before any promotion decision. No assigned ID matched the administrative r304 identifier screen.

Run the read-only verifier with OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python3 -B ../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python3 -B verify.py from this lane. It checks actual originals, exact payload membership, all corpus chunks/inputs, assignments and hashes; exits nonzero on mismatch. Bounded synthetic hash/size/extra-file negatives test the payload checker without changing originals. manifest.json excludes only itself and final-verification-receipt.json. The final receipt reports manifest SHA256+size and integrity outcome. Integrity PASS is neither mathematical validity nor novelty PASS.
''')
with (D/'SUMMARY.md').open('a') as f:f.write('\nAdditional retained deviation: an early structural head probe displayed an unassigned null-statement/not-retrieved sentinel (413524) before all-chunk verification. It was not mathematically screened, reviewed, reassigned, or counted. See failures.json.\n')
# Preserve all files including scripts and failures, exclude exactly two named final artifacts.
ex={'manifest.json','final-verification-receipt.json'}
files=[{'path':str(p.relative_to(D)),'size':p.stat().st_size,'sha256':H(p)} for p in sorted(D.rglob('*')) if p.is_file() and str(p.relative_to(D)) not in ex]
(D/'manifest.json').write_text(json.dumps({'excluded_exact_paths':sorted(ex),'files':files},indent=2)+'\n')
run=subprocess.run([sys.executable,'-B',str(D/'verify.py')],capture_output=True,text=True)
assert run.returncode==0,run.stderr
receipt=json.loads(run.stdout);receipt['verified_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();receipt['negative_tests']=json.loads((D/'negative-tests.json').read_text());(D/'final-verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
