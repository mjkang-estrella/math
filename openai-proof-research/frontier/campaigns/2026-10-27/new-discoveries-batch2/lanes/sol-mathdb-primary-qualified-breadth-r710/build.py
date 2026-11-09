from pathlib import Path
import json,hashlib,collections
P=Path(__file__).parent;L=P.parent
def write(n,x):(P/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
lit=json.loads((P/'literal-records.json').read_text())
ass={}
for line in (P/'assessments.tsv').read_text().splitlines():
 id,c,r,t=line.split('|');ass[int(id)]=(c,r,t)
assert set(ass)=={r['mathdb_id'] for r in lit}
ds=[]
for f in lit:
 id=f['mathdb_id'];r=f['record'];c,reason,tech=ass[id]
 ds.append({'mathdb_id':id,'corpus_chunk':f['corpus_chunk'],'corpus_line':f['corpus_line'],'statement_utf8':r['statement'],'statement_utf8_sha256':hashlib.sha256(r['statement'].encode()).hexdigest(),'canonical_record_sha256':f['canonical_record_sha256'],'classification':c,'classification_reason_and_quantifiers':reason,'technical_assessment':tech,'disposition':'EXCLUDE_SCOPE_CORRECTION' if id in [356229,357705] else 'HOLD_SOURCE_PRIOR_OR_HARD_ROUTE','accepted_credit':0,'source_url':r['source_url'],'source_body_coverage':'selected primary passages only' if id in [356229,357317,357705] else 'literal only; no primary body read','whole_body_read':False,'successor_body_read':False,'full_dependency_audit':False,'registry_cleared':False,'prior_cleared':False,'source_restoration_required':c!='complete','complete_mathematical_statement_review':c=='complete'})
write('dispositions.json',ds);write('proposals.json',[])
coverage=[
 {'id':356229,'source':'2209.12436v1','text_lines':['40-70','70-110','1547-1563'],'coverage':'Primary definitions and Conjecture5.6 read. Global keyword locator search also executed. No whole-body or cluster-theorem dependency audit.','finding':'Consecutive pattern convention explicit, incompatible with literal classical statement. Enumeration n<=7 confirms distinction.','successor':'No successor body identified or read; search hits are not clearance.'},
 {'id':357317,'source':'2301.09846v1','text_lines':['37-66','92-135'],'coverage':'Equation1, primary Conjecture1 and nearby Theorem6/8 statements read; no Radu implementation/proof-body replay.','finding':'Product definition restored; only n0 selected-prime coefficients checked. No full-scope route established.','successor':'No successor body read; no absence inference.'},
 {'id':357705,'source':'2303.05673v1','text_lines':['1350-1368','1690-1790','1788-1845','1858-1884'],'coverage':'Definition11, Section5 contextual nonredundancy, family sufficiency calculation and Conjecture1 read. Earlier unfolding-tree classification and dependencies not audited.','finding':'Equal-row-sum example is an explicit common-expansion correction to the literal; source excludes it contextually.','successor':'Search result on third-party ProbXiv reports same example; not opened, no proof-body or registry clearance. No novelty asserted.'}
]
write('source-coverage.json',{'literal_records':50,'complete_statement_count':sum(d['classification']=='complete' for d in ds),'primary_passages':coverage,'whole_bodies':0,'successor_bodies':0,'dependency_audits':0,'registry':'HOLD unavailable','searches':{'utc_date':'2026-10-31','queries':['"2303.05673" monoid conjecture','"2301.09846" congruences conjecture','"2209.12436" conjecture 5.6'],'result_limit':'Nonprimary search snippets not used as mathematical proof. MathDB and ResearchGate results not opened. No search hit qualifies successor-body clearance.'}})
inherited=json.loads((L/'root-mathdb-breadth-intake-r709/frozen/sol-mathdb-primary-qualified-breadth-r704/failures.json').read_text())
write('failures.json',{'new_network_failures':[],'inherited_stops':inherited['stopped_routes_preserved'],'inherited_adjudications':inherited['inherited_adjudications'],'mathdb_requests':0,'registry':'HOLD unavailable; no absence-of-hits inference','deviations':['Prebinding diagnostic heads displayed administrative/metadata content, documented in pre-reading-checks.json; no scientific statement read before checks.','First full-record diagnostic exceeded output cap; recovered all omitted statements using bounded assigned-record displays.','Third-party search snippets were incidentally returned, including a MathDB result; no prohibited site opened, no snippets treated as proof.','Negative tests use in-memory altered byte maps; originals are never mutated.'],'failed_guard_checks':['Initial build failed on an unescaped absolute-value delimiter; fixed before output generation. Guard resource limits were not hit.'],'helpers':'All Python through fixed helper_guard under unchanged limits; no bypass, raising or splitting to evade limits.'})
# Bind guard itself and read-only instructions, plus every source byte/derivative.
bindings=json.loads((P/'flat-bindings.json').read_text())
for p in [L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',*P.glob('*.pdf'),*P.glob('*.txt')]:
 bindings.append({'path':str(p.resolve()),'size':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
write('flat-bindings.json',bindings)
counts=collections.Counter(d['classification'] for d in ds)
(P/'SUMMARY.md').write_text(f"""# r710 breadth handback

Exactly 50 assigned literal records read and individually assessed, no replacements. Classification: {dict(counts)}. Zero proposals, zero credit. Baseline 8,633 reported literal reviews; this lane supplies 50 disjoint reviews for root reconciliation, not a shared coverage update. Routing's 10,000 metadata rows are not review coverage. Counts remain 9 additional / 39 total / next 40.

All 20 original r301 corpus chunks and eight frozen inputs checked in place against the intake-bound inventory manifest; intake exact payload and all direct original/copy pairs independently checked without executing upstream verify.py. All three reservation sets are disjoint from coverage, each other and protected IDs. Sol r708 and rate-limit-HELD Claude r628 reservations remain untouched.

All statements, quantifier/scope assessments, exact UTF8 statement hashes and canonical record hashes are in dispositions.json and literal-records.json. Only complete statements count as complete; missing definitions, omitted propositions and ambiguous domains remain flagged. No tags, open labels or solution arrays were used as evidence of novelty.

Three primary passage reviews: 356229 has classical/consecutive scope mismatch (m4,n5 gives11 versus12); 357705 has a six-rewrite equal-row-sum witness excluded by source-context nonredundancy. Both are corrections, not discovery. 357317's exact product checks cover n0 and primes2,3,5,7,11,13 only; all seven congruences pass there, providing no universal proof. Executed calculations are retained. No successor bodies or full dependency chains audited; no substantial hypothesis investment justified. No brief manufactured.

r304 exclusions/historical dispositions were bound and checked for assigned IDs; no target-specific matches displayed. r363 Cayley prior-body exclusion and r709 adjudications preserved, including retire338290/339564/372627, park337963 and excluded338366 with text/figure reconstruction and unread-journal limitations.

Zero MathDB requests. Current proof registry unavailable: HOLD. All inherited stopped routes remain parked; no retry, workaround, browser, upload, contact, git, Lean, manuscript, shared-index or credit changes. Three lawful arXiv v1 PDF fetches succeeded, bound before extraction; derivatives bound before reading. Source coverage distinguishes literal, selected primary passage, whole body, local calculation, dependency and registry evidence. Search snippets are not clearance.

Integrity PASS is not mathematical or novelty PASS. The read-only verifier checks exact lane payload, actual originals, twenty chunks, eight inputs, reservations, literal identity and both record hashes. It rejects hash, size and extra-file mismatches. The final receipt separately binds the manifest. Run ./verify.sh from any directory. See failures.json for prebinding metadata-display deviation and recovered truncated diagnostic.
""")
print(dict(counts))
