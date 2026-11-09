import pathlib,json,hashlib,collections,datetime,subprocess
O=pathlib.Path(__file__).resolve().parent;L=O.parent
J=lambda p:json.loads(p.read_text())
def put(n,v):(O/n).write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n')
def binding(p):
 b=p.read_bytes();return dict(path=str(p.resolve()),sha256=hashlib.sha256(b).hexdigest(),size=len(b))
refs=J(O/'initial-bindings.json')
for p in [L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',L.parent/'AGENTS.md',L.parents[3]/'AGENTS.md']:
 if p.exists():refs.append(binding(p))
put('initial-bindings.json',refs)
rows={int(z[0]):z[1:] for line in (O/'reviews.tsv').read_text().splitlines() if (z:=line.split('\t'))}
records=J(O/'literal-records.json');assert len(rows)==50
out=[]
for x in records:
 i=x['mathdb_id'];r=x['record'];c,reason,status,tech=rows[i]
 out.append(dict(mathdb_id=i,chunk=x['chunk'],line=x['line'],canonical_record_sha256=x['canonical_record_sha256'],literal_line_sha256=x['literal_line_sha256'],statement=r['statement'],statement_sha256=hashlib.sha256(r['statement'].encode()).hexdigest(),source_url=r['source_url'],source_version=r['source_name'],completeness=c,completeness_reason=reason,quantifier_scope=r['statement'],disposition=status,technical_assessment=tech,primary_question_passage_read=False,full_dependency_audit=False,current_registry='HOLD_unavailable',credit=0))
put('dispositions.json',out);put('proposals.json',[])
put('source-coverage.json',[
 dict(ids=[400164],source='matroid.pdf',version='Annals188(2018)381-452 DOI10.4007/annals.2018.188.2.1',read_text_lines=['1-115','3245-3295'],coverage='Conjecture1.1; Theorem9.9(2) exact coefficient scope; selected local proof via Proposition9.8 and convolution. Whole body and dependencies not audited. Original EMS question passage unread.',eligibility='published theorem objection; no novelty clearance'),
 dict(ids=[400175],source='tree.pdf',version='author BTfinal.pdf bytes pinned; date/version not internally established',read_text_lines=['1-180'],coverage='Finite simple conventions; Conjecture1; Theorem2 and selected local proof using Theorems3,4,6,7. Internal dependencies not audited. Vertex-to-edge connectivity bridge is routine. Original EMS passage unread.',eligibility='published theorem objection for intended scope'),
 dict(ids=[400535],source='schmidt.pdf',version='arXiv1001.2694v1 15Jan2010',read_text_lines=['1-210'],coverage='Bad definitions, Theorems1/2, Corollary1, selected proof of Theorem2=>Theorem1. Main construction and dependencies unread. Original EMS passage unread.',eligibility='stronger finite-intersection theorem objection')])
put('failures.json',dict(new_http_failures=[],deviations=[dict(stage='extract.py administrative output',issue='Printed coverage map keys and truncated 500-character values for all historical coverage entries, producing excessive truncated tool output. No unrelated corpus literals were selected for scientific review; this output was not used as mathematical evidence. Retained helper discloses the error; not rerun.')],stopped_routes_preserved=['MathDB429 zero requests','Google/GitHub API/raw/codeload/diff','ScienceDirect','browser/preview','AIM/Kourovka/EGRES/AIProofWatch','DMGT TLS','ProjectEuclid challenge','ResearchGate403','Gorenstein author PDF TLS r642','OEIS A274199/internal403 r542','DOI10.1093/imrn/rnz305 academic.oup.com403 r618'],registry='Unavailable HOLD; no absence-of-hits inference'))
put('administrative-gates.json',dict(counts='9 additional /39 total /next40 unchanged',baseline=7583,r666='continues untouched',r628='rate-limit HELD untouched and uncounted',retired=[338290,339564,372627],parked=[337963,338408],excluded338366='No credit; published object reconstructed modulo two text/figure defects and journal bodies unread; not a named-refutation claim',cayley364119='r363 exclusion retained',accepted_family_gate='r304 files bound; top-level schema inspected, no candidate promotion and no full family text audit claimed',historical_context='ledger/prior context bound; beginning excerpts read; no blanket full-document reading claim'))
counts=dict(collections.Counter(x['completeness'] for x in out));put('coverage.json',dict(literal_reviews=50,independent_completeness=counts,baseline=7583,lane_only_sum=7633,root_reconciliation_required=True,proposals=0,primary_question_passages=0,selected_successor_theorem_bodies=3,full_dependency_audits=0,registry='HOLD',credit=0))
put('bounded-checks.json',dict(executed=['hash/size checks','exact assigned-literal extraction','canonical UTF8 hash verification','all20 chunk and all8 frozen input verification','reservation/baseline/protected disjointness'],mathematical_calculations_executed=[],reason='No bounded full-scope new mechanism survived literal screening; do not manufacture parameter sweeps.'))
(O/'SUMMARY.md').write_text('''# r668 independent breadth handback

Exactly 50 assigned literal records reviewed, no replacements; zero proposals and zero credit. Baseline remains 7,583 reported literal reviews pending root reconciliation (lane-only arithmetic 7,633). This is not full technical corpus coverage.

Independent completeness counts: '''+json.dumps(counts)+'''. Each disposition preserves the exact statement, quantifier scope, corpus chunk/line, literal-line hash and canonical record hash, with an individual reason and technical obstruction.

Intake exact payload, original/copy bindings, all 20 original r301 chunks, all 8 frozen inputs, and three reservation sets checked independently without upstream verify.py. No corpus/history tree copied. Runnable `./verify.sh` checks the actual originals and exact local payload, fails nonzero on mismatches, and performs bounded hash/size/extra-file negatives in memory.

Three bound primary successor sources support published-resolution objections: 400164 matroid coefficients, 400175 tree decompositions, 400535 Schmidt intersections. Selected theorem statements and local proof passages read; no full body/dependency audit or original EMS question-passage reading claimed. Other prior objections remain HOLD. Metadata is not proof-body clearance.

No newly justified full-scope mechanism warrants a hypothesis brief. Missing definitions, domain corrections, parameter examples and standard adaptations receive no credit. Current registry remains unavailable HOLD. No MathDB request, browser, forbidden route, Lean/manuscript/credit/shared file edit or child agent. All helpers ran through the fixed guard with unchanged caps. The overbroad administrative-output deviation is retained in failures.json. Retired/parked gates and 338366 reconstruction/unread-journal caveats remain unchanged.

Integrity PASS means byte/assignment consistency only, not mathematics or novelty PASS.
''')
put('flat-bindings.json',refs)
files=[dict(path=str(p.relative_to(O)),sha256=binding(p)['sha256'],size=p.stat().st_size) for p in sorted(O.rglob('*')) if p.is_file() and p.name not in ['manifest.json','final-verification-receipt.json']]
put('manifest.json',dict(excluded_exact_paths=['manifest.json','final-verification-receipt.json'],files=files))
p=subprocess.run([str(O/'verify.sh')],capture_output=True,text=True);assert p.returncode==0,(p.stdout,p.stderr)
put('final-verification-receipt.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest=binding(O/'manifest.json'),verification=json.loads(p.stdout),guard_stderr=p.stderr,exit_code=p.returncode))
print(p.stdout);print(json.dumps(binding(O/'manifest.json')))
