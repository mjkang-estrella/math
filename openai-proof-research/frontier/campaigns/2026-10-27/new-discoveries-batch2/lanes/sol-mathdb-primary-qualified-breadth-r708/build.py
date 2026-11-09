from pathlib import Path
import json,hashlib,collections
O=Path(__file__).parent
j=lambda p:json.loads(p.read_text())
notes={}
for line in (O/'assessments.tsv').read_text().splitlines():
 i,c,r,q,d,a=line.split('\t');notes[int(i)]=(c,r,q,d,a)
rows=j(O/'literal-records.json');assert len(notes)==len(rows)==50
coverage={
351775:('cached arXiv2108.13537v1 HTML-derived text','Conjecture27 and displayed initial polynomials; selected passage only','No full body or successor proof audit'),
352797:('arXiv2112.00444v1','Conjecture2 line1664; Lemma20 proof1730-1810; Corollary2/Proposition4 lines1825-1865','Source-internal proof read; dependencies not fully replayed; no independent successor audit'),
353918:('arXiv2203.07227v1','Selected final even-sequence theorem argument lines450-490 and title; general c(n) passage not located','Version mismatch HOLD; no successor clearance'),
354698:('arXiv2205.09902v1','Section5 Conjecture5.2 lines920-942','Question and contextual discussion only; no successor bodies'),
352844:('arXiv2112.03338v1','Weiner conjecture and preceding Dyck-code argument lines210-240','Selected local proof only; no full-body or successor audit'),
353190:('arXiv2201.01352v1','Theorem1.1 lines85-105; proof3.1 opening1290-1320 and closing1443-1446','Published theorem and selected proof passages; no full asymptotic dependencies/finite-check replay'),
}
for i in [351408,351409,351410,351411]:coverage[i]=('arXiv2107.11160v1','Jump definitions lines11-25 and Definition3.3; Conjecture3.6 and Proposition3.5 lines252-275; concluding heuristic selected passage','Primary definitions/selected results only; later threshold passages not established; no successor proof audit')
disp=[]
for x in rows:
 r=x['record'];i=r['mathdb_id'];c,reason,q,d,a=notes[i];src=coverage.get(i)
 disp.append({'mathdb_id':i,'corpus_chunk':x['chunk'],'corpus_line':x['line'],'canonical_record_sha256':x['canonical_record_sha256'],'statement':r['statement'],'statement_utf8_sha256':hashlib.sha256(r['statement'].encode()).hexdigest(),'literal_classification':c,'classification_reason':reason,'quantifiers':q,'disposition':d,'technical_assessment':a,'source_url_literal':r['source_url'],'source_evidence':{'level':'selected primary passage' if src else 'literal record only','source_version':src[0] if src else None,'passage':src[1] if src else None,'limit':src[2] if src else 'No primary question/body/successor clearance; metadata never proof evidence','whole_body_read':False,'full_dependency_audit':False,'current_registry_cleared':False},'credit':0,'prior_cleared':False,'full_scope_proof_established':False})
(O/'dispositions.json').write_text(json.dumps(disp,ensure_ascii=False,indent=2)+'\n');(O/'proposals.json').write_text('[]\n')
counts=dict(collections.Counter(x['literal_classification'] for x in disp))
(O/'source-coverage.json').write_text(json.dumps({'literal_records':50,'classifications':counts,'primary_selected_records':len(coverage),'primary_selected_documents':7,'whole_bodies_read':0,'full_dependency_audits':0,'successor_body_clearances':0,'registry':'HOLD unavailable; zero MathDB requests','documents':{str(i):v for i,v in coverage.items()},'calculation_limit':'Executed finite checks are in calculations.json; not full-scope proofs or novelty clearance'},indent=2)+'\n')
inherited=j(O.parent/'root-mathdb-breadth-intake-r707/frozen/sol-mathdb-primary-qualified-breadth-r706/failures.json')
(O/'failures.json').write_text(json.dumps({'access_failures_this_lane':[],'preserved_stops':inherited['preserved_stops'],'new_holds':['2203.07227v1 is even-sequence version; general-statement passage unavailable in inspected version'],'deviations':['Initial full-record print truncated; all50 literal statements read through first10 retained output plus bounded10..34 and35..49 excerpts. No unassigned literal exposed.','A cached one-line HTML-derived source grep and an overbroad six-document search generated truncated output; subsequently used bounded assigned-source passages. No whole-body clearance inferred.','Initial TSV guessed factor-four suffix distinction; executed computation shows factor eight, corrected final assessment.','Initial TSV incorrectly omitted odd-part normalization from first Syracuse jump; corrected before sealing.','A mistyped r363 path failed; correct original was bound before successful reading.'],'scientific_failed_checks':['No digit-bound counterexample found through10000; floating h evaluation cannot certify exact positivity or all n.','Catalan finite residues through k12 do not establish eventual avoidance.'],'credit_exclusions':inherited['credit_exclusions']+['Known source proof, endpoint/convention/transcription corrections, finite helpers earn zero credit.'],'reservations':'r704 independently running/unreconciled and r628 HELD preserved'},indent=2)+'\n')
summary=f'''# r708 breadth screening

Reviewed exactly **50 assigned literal records**, without replacements. Classification: {counts}. These are literal-statement reviews, not full technical corpus coverage. Intake baseline is 8,583; this lane supplies 50 disjoint reviews for root reconciliation (potential baseline 8,633 only after integration). Routing's 10,000 metadata rows are not reviews. Counts remain 9 additional / 39 total / next40.

**Zero proposals, zero credit.** Selected primary passages cover 10 records in seven documents. No whole-body, complete dependency, current registry, or successor-body clearance is claimed. None warranted substantial proof investment after these gates. The suffix paper explicitly proves its own conjecture later, and the plane-partition paper states and proves the target theorem. Literal suffix/root counting, falling-factorial, spectral trivial-eigenvalue and Syracuse-definition mismatches are corrections, not discoveries. Other rows have individual scope or technical obstructions in dispositions.json.

Pre-reading verification passed: exact r707 payload, 46 direct original/copy pairs, all20 original r301 chunks in place, all8 frozen inputs, r301 manifest binding, all3 pairwise-disjoint reservations versus8,583 coverage/protected IDs. Flat bindings retain originals without corpus copies or recursive history expansion. r304 exclusions, r363 Cayley decision, ledger/context and r707 adjudications were consulted after binding. Exact-ID context matches were empty; that is not family/prior clearance.

Executed bounded checks: suffix root counts 8,24,72 versus distinct square suffix counts1,3,9 at lengths3..5; row-polynomial convention mismatch n3,x0; positive-n digit-bound exploratory check through10,000 with no violation; Catalan residues at n=2^k-1 through k12; trivial spectral endpoint inequality128<225. None gives eligible full-scope novelty. See calculations.json and failures.json for limits and corrected preliminary errors.

Zero MathDB requests. Six lawful arXiv v1 PDFs fetched with generic headers; bytes bound before extraction, text bound before reading. Cached Riordan source reused after binding. All inherited stops remain parked, including r578, r642 TLS, r684 v2 404s, r542 OEIS403 and r618 OUP403. Current registry unavailable => HOLD. r704 and r628 reservations unchanged. No shared files, manuscripts, Lean, credit, git, messages or publications changed.

Run independent verification from this lane with the fixed guard:

`OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python3 -B ../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python3 -B verify.py`

Verifier checks original bindings, exact intake/output payloads, all20+8 inputs, reservations, original assigned lines, canonical/statement hashes and receipt binding. Bounded negative fixtures test hash, size and extra-file rejection without mutating originals. Integrity PASS is not mathematical or novelty PASS. Manifest excludes only itself and final-verification-receipt.json.
'''
(O/'SUMMARY.md').write_text(summary)
print(counts)
