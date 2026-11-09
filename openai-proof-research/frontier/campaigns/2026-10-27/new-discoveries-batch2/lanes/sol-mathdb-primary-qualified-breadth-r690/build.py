import pathlib,json,hashlib,datetime,collections,math
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r689'
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
def write(n,o):(P/n).write_text(json.dumps(o,ensure_ascii=False,indent=2)+'\n')
reviews={}
for line in (P/'reviews.tsv').read_text().splitlines():
 id,cl,reason,assessment=line.split('\t');reviews[int(id)]=(cl,reason,assessment)
lits=j(P/'literal-records.json');assert len(reviews)==len(lits)==50
out=[]
for x in lits:
 r=x['record'];id=r['mathdb_id'];cl,reason,assessment=reviews[id]
 out.append({'mathdb_id':id,'chunk':x['chunk'],'line':x['line'],'statement_utf8':r['statement'],'statement_sha256':h(r['statement'].encode()),'canonical_record_sha256':h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()),'source_url':r['source_url'],'canonical_url':r['canonical_url'],'classification':cl,'classification_reason_and_quantifiers':reason,'technical_assessment':assessment,'final_disposition':'EXCLUDE_ROUTINE_OR_SOURCE_SCOPE' if id in [335423,406505] else 'SOURCE_REPORTED_RESOLUTION_NO_NEW_CREDIT' if id in [330114,332966] else 'HOLD','source_coverage':'selected primary passages' if id in [335423,406505] else 'literal record only','whole_source_body_read':False,'successor_body_cleared':False,'full_dependency_audit':False,'current_registry_cleared':False,'accepted_credit':0})
write('dispositions.json',out);write('proposals.json',[])
# A bounded exact arithmetic sanity check of the generic binomial Bezout decomposition.
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for k,y in enumerate(b):c[i+k]+=x*y
 return c
def power(a,n):
 c=[1]
 for _ in range(n):c=mul(c,a)
 return c
def addto(a,b,s=1):
 a.extend([0]*max(0,len(b)-len(a)))
 for k,v in enumerate(b):a[k]+=s*v
checks=[]
for n,r in [(1,1),(2,2),(3,3),(5,4)]:
 U=[1]*n;V=[1]*(n+1);total=[]
 for k in range(2*r):
  term=mul(power(V,k),[0]*(2*r-1-k)+power(U,2*r-1-k));addto(total,term,(-1)**(2*r-1-k)*math.comb(2*r-1,k))
 assert total[0]==1 and all(v==0 for v in total[1:]);checks.append({'n':n,'r':r,'expanded_identity_equals_one':True})
write('bounded-calculations.json',{'executed':checks,'not_a_proof_by_cases':True,'full_scope_symbolic_argument':'V-qU=1. In (V-qU)^(2r-1), k>=r gives V^r; k<r gives U^r. The coefficients after division are integer polynomials. Multiplication by (1-q)^r yields the literal identity. Routine adaptation; excluded.'})
write('source-coverage.json',{'literal_reviews':50,'classification_counts':dict(collections.Counter(d['classification'] for d in out)),'selected_primary_ids':[335423,406505],'whole_bodies':0,'successor_proof_bodies':0,'current_registry':'unavailable HOLD','no_novelty_inference':True,'passages':{'335423':'arXiv1703.00003v1 selected introduction, section2 proof and conjecture locators; q-integer rational Bezout ingredient (2.5); no named literal conjecture established in selected text','406505':'arXiv2610.20097v1 introduction GP, variational setup (2.1), full subsection3.1 Theorem3.1 proof, beginning subsection3.3 including theorem and trial-space setup; latter proof not read to end. Same-index versus shifted-index distinction decisive.'},'planned_not_executed':'No full dependency replay or successor-body search: no substantial hypothesis survives routine/scope objections.'})
stops=['MathDB HTTP429: zero requests','r578 inherited failures preserved; no retry','r642 author Gorenstein PDF TLS failure','r684 two arXiv v2 HTTP404 fetches','OEIS A274199/internal HTTP403 r542','DOI10.1093/imrn/rnz305 academic.oup.com403 Cloudflare r618','AIM/Kourovka/EGRES/AIProofWatch parked','DMGT TLS failure','ProjectEuclid challenge','ResearchGate403','Current proof registry unavailable HOLD']
write('failures.json',{'new_http_failures':[],'stopped_routes_preserved':stops,'deviations':['Intake receipt and metadata queue prefix displayed before binding, before scientific reading; disclosed in initial-checks.json. Hash matching does not undo ordering deviation.','First r363 directory spelling in bind.py matched no files. Correct directory bound in context.py before its DECISION was read.'],'338366_credit_exclusion':'Published object reconstructed modulo text/figure defects; journal bodies unread; no retry of parked journal route.','access':'Only two generic-header arXiv HTML fetches; zero MathDB, Google, GitHub, ScienceDirect, browser or registry requests; no contacts or uploads.'})
# Bind every downloaded and derivative byte path before final review.
bs=j(P/'flat-bindings.json')
for e in j(P/'source-provenance.json'):
 if 'path' in e:
  b=(P/e['path']).read_bytes();assert h(b)==e['sha256'] and len(b)==e['size']
  bs.append({'path':str(P/e['path']),'size':len(b),'sha256':h(b)})
for s in (P/'derivative-bindings.jsonl').read_text().splitlines():
 e=json.loads(s);b=(P/e['path']).read_bytes();assert h(b)==e['sha256'] and len(b)==e['size'];bs.append({'path':str(P/e['path']),'size':len(b),'sha256':h(b)})
write('flat-bindings.json',bs)
counts=dict(collections.Counter(d['classification'] for d in out))
(P/'SUMMARY.md').write_text('''# r690 independent breadth screening

Exactly 50 assigned literal records reviewed, with no replacements. Classification counts: '''+json.dumps(counts)+'''. Baseline 8,133 reported literal reviews; this lane adds 50 disjoint literal reviews, yielding baseline-relative 8,183 only. Concurrent r688 is not reconciled here; r628 remains HELD. Routing's 10,000 metadata rows carry no technical review credit. Counts 9 additional /39 total /next40 unchanged.

Zero proposals and zero credit. Every literal has a separate scope/quantifier assessment and technical disposition. Two primary HTML sources inspected in bounded passages, no whole-body or successor-body clearance. The integral polynomial Bezout identity has a routine binomial proof; four finite exact expansions are sanity checks only. The Payne source concerns the shifted-index inequality; the literal same-index comparison is a routine Cauchy–Schwarz/minmax consequence. Neither is eligible. Other records remain definition, scope, source or substantive HOLD or contain source-reported historical resolutions; no metadata resolution has been certified as a new proof.

Integrity checks cover exact intake payload, all49 direct original/copy pairs, all20 original r301 chunks and all8 separately listed frozen inputs, canonical/literal hashes, all150 reservation IDs versus baseline and protected IDs. No upstream verifier executed, corpus copied or historical tree expanded. r304 exclusions and historical dispositions checked for assigned IDs; bound r363 decision read; current r689 retirements and parks preserved. Root ledger and prior context loaded only after binding. No focused hypothesis.

Run `./verify.sh` for independent read-only integrity verification (nonzero on mismatch). Manifest covers every payload including verifier and scripts, excluding only manifest.json and final-verification-receipt.json. Final receipt binds manifest SHA256 and size and records hash/size/extra-file rejection tests. Integrity PASS is neither mathematical acceptance nor novelty PASS. Current registry unavailable: HOLD. No Lean, manuscript, ledger, coverage index, sibling, upstream or git changes.

The receipt/queue-metadata prebinding display and initial r363 path mismatch are candidly recorded in failures.json. All inherited stopped routes remain parked, including r578, r642 TLS, r684 v2 404s, OEIS403 and OUP403. Two successful generic-header arXiv HTML fetches; no new HTTP failures, MathDB requests, browser use, accounts, messages or uploads. Primary bytes were hashed before parsing and derivatives before reading.
''')
print(counts)
