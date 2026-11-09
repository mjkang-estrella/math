import pathlib,json,hashlib,collections
L=pathlib.Path(__file__).parent
rows=json.loads((L/'dispositions.json').read_text());counts=collections.Counter(x['disposition'] for x in rows)
(L/'SUMMARY.md').write_text('''# MathDB breadth screening r416

Completed literal cached-statement screening of the exact fifty reserved IDs from r415. **Zero qualified full-scope briefs, zero proposals, zero credit.** Campaign counts remain **9 additional / 39 total / next 40**. No shared ledger, index, reservation, git, publication, account, or upstream payload was changed.

The intake extension/routing queue is metadata only. No claim of exhaustive corpus review or current open status is made. Fifty individual statements, scopes, reasons, source-version limitations and evidence levels are in [dispositions.json](dispositions.json); [proposals.json](proposals.json) is empty. The statement text is preserved literally even when extraction or notation is defective.

Disposition totals: '''+', '.join(f'{k}: {v}' for k,v in sorted(counts.items()))+'''. These are screening decisions, not findings of mathematical impossibility.

Primary source inspection stopped several tempting false positives. The Ohtsuki collection already reports the Kauffman-skein invariant construction solved (389749), supplies ribbon-category connections for quandle invariants (389762), and explicitly supplies L(25,4), L(25,9) as the LMO/quantum distinguishing example (389776). These are collection-level source reports/examples, not independently audited proof/dependency clearances. The generated-closure notation in Problem 2.28 (389709) makes a generic finite-dimensional basis argument inadequate. Positive-characteristic Kontsevich denominators, all-degree rational associator construction, global skein computations, and the percolation interchange-of-limits issue have no cheap full-scope bridge here. The planar cropping proof does not extend merely by fixing the empty-lattice wording.

Four Benjamini entries remain HOLD_ACCESS after three distinct original PDFs returned 404. The three IPAM entries and two Wikipedia-derived targets remain HOLD_PRIMARY; access or missing definitions do not establish hardness or ineligibility. For parked programs, the reason is that no concrete low-cost full-scope mechanism qualified in this pass. Linked successor proof bodies were not audited and no investment/computational sweep was undertaken. Independent current novelty registry clearance is missing and remains HOLD for every potential positive claim. Open labels and empty solutions establish nothing about novelty.

Read [source-audit.md](source-audit.md) for precise distinctions among original source sections, author/collection context, reported resolutions, proof sections and dependency/registry gaps. Each public retrieval has URL/version clues/UTC/hash recorded before reading in evidence/*.provenance.json. No MathDB requests, Google, prohibited GitHub routes, ScienceDirect, browser, TLS bypass, archive retries or denied-route retries were made. No simulations, Lean files or manuscripts.

[bindings.json](bindings.json) freezes flat hashes/sizes of original intake manifest, bindings and direct actual originals, queue/coverage/reservation, twenty r301 chunks, r304 accepted/history and r363 disposition. No corpus/history snapshot tree was copied or recursively expanded. Only the fifty assigned rows were retained as individual evidence. Assignment checks show exactly fifty, disjoint from 1,783 reviewed IDs, the other fifty active IDs and 372627/372628/368940. Administrative r304 ID comparison found no assigned-ID matches; this is not semantic novelty clearance.

The initial local checker failed on the r301 bytes-versus-size schema field. The failure is preserved, the local checker corrected, and all twenty originals then passed before literal statement reads. A queue metadata title was printed between that failure and the successful chunk check; this ordering deviation is disclosed in [failures.json](failures.json). Flat references had already been frozen. No upstream verifier was executed and no upstream receipt was written.

All Python helpers used the fixed 512 MiB AS/group-RSS, 210 CPU-second, 230 wall-second guard with single-threaded BLAS and bytecode disabled; bounded native source text inspection was used after freeze. No resource limit was raised. There were no scientific calculation checks because no candidate qualified for one.

[verify.py](verify.py) is a separate local verifier: original references, intake manifest and direct original bindings, twenty in-place chunks against r301 manifest, assignment/disjointness, all fifty statement/URL/canonical-record hashes against the originals, public-response hashes, and the exact payload set. It exits nonzero on mismatch. [manifest.json](manifest.json) includes every lane file except exactly manifest.json and finalreceipt.json by relative path. [finalreceipt.json](finalreceipt.json) records the final verification result.
''')
files=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and str(p.relative_to(L)) not in {'manifest.json','finalreceipt.json'}:
  b=p.read_bytes();files.append({'path':str(p.relative_to(L)),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)})
(L/'manifest.json').write_text(json.dumps({'excluded_relative_paths':['manifest.json','finalreceipt.json'],'files':files},indent=2)+'\n')
print(dict(counts),'payload_files',len(files))
