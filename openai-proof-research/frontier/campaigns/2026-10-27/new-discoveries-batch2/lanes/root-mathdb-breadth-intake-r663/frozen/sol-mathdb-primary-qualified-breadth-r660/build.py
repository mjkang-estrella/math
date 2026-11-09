import pathlib,json,hashlib,collections,datetime
from fractions import Fraction
P=pathlib.Path(__file__).resolve().parent;L=P.parent;B=L.parent
def write(n,z):(P/n).write_text(json.dumps(z,ensure_ascii=False,sort_keys=True,indent=2)+'\n')
def h(d):return hashlib.sha256(d).hexdigest()
reviews={}
for line in (P/'reviews.tsv').read_text().splitlines():
 id,c,reason,a=line.split('\t');assert int(id) not in reviews;reviews[int(id)]=(c,reason,a)
rows=json.loads((P/'literal-records.json').read_text());assert len(reviews)==len(rows)==50
source={398323:dict(path='ems12479.pdf',pdf_pages=[36],printed_pages=[998],scope='Selected addendum and references; no MSS proof body or full dependency audit.'),398339:dict(path='ems12480.pdf',pdf_pages=[53,54,55],printed_pages=[1077,1078,1079],scope='Selected report contribution and references; Hodge-theory proof is only reported, not independently replayed.'),398470:dict(path='ems12491.pdf',pdf_pages=[37,38,39],printed_pages=[1665,1666,1667],scope='Selected theorem and full short report proof sketch with references; cited 2012 paper body and dependencies unread.'),398471:dict(path='ems12491.pdf',pdf_pages=[39],printed_pages=[1667],scope='Adjacent assigned-record passage states n<=6 theorem; no arbitrary-n proof clearance.')}
ds=[]
for x in rows:
 r=x['record'];id=r['mathdb_id'];c,reason,a=reviews[id]
 d=dict(mathdb_id=id,statement=r['statement'],statement_utf8_sha256=h(r['statement'].encode()),canonical_record_sha256=h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()),corpus_chunk=x['corpus_chunk'],corpus_line=x['corpus_line'],source_url=r['source_url'],source_name=r['source_name'],independent_completeness=c,completeness_reason=reason,complete_mathematical_statement_reviewed=c=='complete',quantifier_and_technical_assessment=a,disposition='PARK_NO_FULL_SCOPE_ROUTE' if c=='complete' else 'HOLD_SCOPE',accepted_credit=0,current_registry_cleared=False,primary_coverage=source.get(id,{'scope':'Literal only; primary body not inspected.'}),whole_primary_body_read=False,successor_proof_body_read=False,full_dependency_audit=False,local_proof_established=False)
 if id==398470:
  d['disposition']='EXCLUDE_SOURCE_STATED_THEOREM';d['quantifier_and_technical_assessment']+=' Primary report p1665 states exactly all g>=1 as Theorem1; p1666 explains TQFT representations, density and strong approximation; cites Masbaum-Reid Geometry and Topology16(2012)1393-1411. No discovery credit and no proof-body replay claimed.'
 if id==398339:d['disposition']='EXCLUDE_SOURCE_REPORTED_RESOLUTION';d['quantifier_and_technical_assessment']+=' Actual report p1078 explicitly announces deduction of Soergel conjecture and KL positivity; ref[6] is arXiv1212.0791. Coefficient-scope details and full proof remain unread.'
 if id==398323:d['disposition']='HOLD_ENDPOINT_AND_GENERAL_SCOPE';d['quantifier_and_technical_assessment']+=' Report p998 also states the signing conjecture and specifically reports a bipartite result by Marcus-Spielman-Srivastava, arXiv1304.4132; no assertion that this settles arbitrary nonbipartite two-sided scope.'
 if id==398471:d['quantifier_and_technical_assessment']+=' Actual report p1667 proves n<=6 and retains all-n as a conjectural route, so the finite range is not a full answer.'
 ds.append(d)
write('dispositions.json',ds);write('proposals.json',[])
counts=dict(collections.Counter(d['independent_completeness'] for d in ds))
write('coverage.json',dict(baseline_reported_literal_reviews=7383,new_disjoint_literal_reviews=50,combined_if_root_reconciles=7433,independent_completeness=counts,primary_selected_record_passages=4,whole_primary_bodies=0,successor_proof_bodies=0,full_dependency_audits=0,proposals=0,credit=0,corpus_exhaustive=False))
# Exact bounded checks are diagnostic only.
assert Fraction(21,25)<1
checks=[dict(id=398284,executed=True,calculation='det(A)^2=21/25<1',result='Necessary lattice-density condition only; no sufficiency or Gaussian formula reconstruction.'),dict(id=398323,executed=True,calculation='For s=+1 and -1, characteristic polynomial of [[0,s],[s,0]] is x^2-1; d=1 gives bound 2sqrt(0)=0.',result='Both signed K2 matrices have eigenvalues +1,-1, outside bound. Endpoint correction only; no discovery credit.')]
for s in [-1,1]:assert s*s==1
write('bounded-checks.json',checks)
write('source-coverage.json',dict(records={str(k):v for k,v in source.items()},limits='No whole report was reviewed; no downloaded journal/successor theorem proof body or full dependency audit. No search absence evidence. Current registry unavailable HOLD. Other rows literal technical screening only. The primary theorem statements suffice to stop investment, not to claim proof verification.'))
stops=['MathDB429: zero requests','Author Gorenstein PDF TLS r642 stopped','AIM/Kourovka/EGRES/AIProofWatch parked','DMGT TLS parked','ProjectEuclid challenge parked','ResearchGate403 parked','OEIS A274199/internal HTTP403 r542 parked','DOI10.1093/imrn/rnz305 OUP403 Cloudflare r618 parked','Current proof registry unavailable HOLD']
write('failures.json',dict(inherited_stops=stops,fetch_failures=[],guard_failures=[],deviations=[dict(kind='Unrelated primary-page display',detail='A page-offset selection mistake displayed ems12479 PDF p37, ems12491 pp10-11, ems12480 p40 while locating assigned passages. Adjacent contributions also appeared on boundary pages37/39 and53/55. These were not assigned corpus record reviews, add no coverage, and were not pursued. Correct selected pages were then inspected. No unrelated scientific corpus record was selected or reviewed.')],credit_exclusion_338366='Retained: reconstructed published object modulo text/figure defects; unread journal bodies and current registry HOLD; no named prior refutation inferred.',parked_338408=True,no_retries=True))
# Extend flat bindings before reading additional administrative details.
flat=json.loads((P/'flat-bindings.json').read_text())
refs=[L/'pi-mathdb-full-corpus-inventory-r301/manifest.json',L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',B/'AGENTS.md',B.parents[2]/'AGENTS.md']
for q in refs:
 if q.exists():
  d=q.read_bytes();flat[str(q)]=dict(sha256=h(d),size=len(d))
write('flat-bindings.json',flat)
# Accepted/historical records are administrative gates; no underlying scientific rows expanded.
admin={}
for n in ['accepted-exclusions.json','historical-dispositions.json']:
 z=json.loads((L/'root-mathdb-accepted-exclusions-r304'/n).read_text())
 def ids(v):
  if isinstance(v,dict):
   for k,w in v.items():
    if k in ['mathdb_id','mathdb_related_id'] and isinstance(w,int):yield w
    elif k in ['mathdb_ids','problem_ids'] and isinstance(w,list):yield from (q for q in w if isinstance(q,int))
    else:yield from ids(w)
  elif isinstance(v,list):
   for w in v:yield from ids(w)
 admin[n]=dict(assigned_id_intersection=sorted(set(reviews)&set(ids(z))),limit='Administrative identifiers and accepted-family gates inspected; not primary proof clearance.')
write('administrative-gates.json',dict(exclusions=admin,cayley_364119='r363 excludes literal equal-maximum conjecture through published length7 counts33712 vs33710; retained formal certificate earns no credit.',current_r659='338290/339564/372627 retired or excluded;337963 parked;338366 excluded with reconstruction/unread-journal caveats;338408 parked. No protected target promoted.'))
(P/'SUMMARY.md').write_text(f'''# r660 breadth screening

Exactly 50 reserved literals independently screened; no replacements. Baseline 7,383 reported literal reviews; 7,433 only if root reconciles this lane. This is not full technical corpus coverage.

Independent completeness: {json.dumps(counts,sort_keys=True)}. Exact statements, UTF-8 hashes, canonical-record hashes, corpus locations, quantifier assessments and individual reasons are in dispositions.json. Zero proposals and zero credit.

Primary passage coverage: four assigned rows across three reports. 398470 is exactly source Theorem1 for all genera; the report includes a TQFT/strong-approximation proof sketch. 398339 is explicitly reported resolved in its primary contribution. 398323 reports the bipartite signing theorem only; the d=1 diagnostic is an uncredited endpoint correction. Adjacent assigned398471 passage gives n<=6, not all n. No whole-primary-body, successor-proof-body or complete dependency clearance is claimed. Other records remain literal-only technical screening. No substantial hypothesis investment follows.

All20 original r301 chunks and8 frozen inputs verified in place. Intake exact payload and37 direct original/copy pairs checked independently without executing upstream verify.py. All three reservation sets are disjoint from baseline, protected IDs and one another. Immutable flat references reused; corpus not copied.

Current registry/source/prior gates remain HOLD; no absence-of-hits inference. All access stops preserved, including Gorenstein TLS, OEIS403 and OUP403. Zero MathDB requests; no API, browser, account, contact, publication or git actions. No Lean/manuscript/credit changes. Fixed guard applied to every Python/helper computation with unchanged512MiB/210CPU/230wall caps. Three wrong report-page selections and adjacent contribution exposure are disclosed in failures.json; no additional record coverage is counted.

Run `bash verify.sh` for read-only integrity verification. Final receipt records manifest SHA256/size and bounded negative hash/size/extra-file rejection. Integrity PASS is not mathematical or novelty PASS. Counts9additional/39total/next40 unchanged.
''')
print(counts)
