import pathlib,json,hashlib,collections
D=pathlib.Path(__file__).parent.resolve();L=D.parent
def read(p):return json.loads(p.read_text())
def write(n,o):(D/n).write_text(json.dumps(o,ensure_ascii=False,sort_keys=True,indent=2)+'\n')
notes={}
for l in (D/'reviews.tsv').read_text().splitlines():
 i,scope,disp,reason=l.split('\t');notes[int(i)]=(scope,disp,reason)
rows=read(D/'literal-records.json');assert len(notes)==len(rows)==50
sources={357497:('2302.12106','Conjecture 2.4; Definition 4.1; Lemmas 4.2-4.3; concluding proof','selected local proof body'),358388:('2305.07727','Section 5, Conjecture 5.4, Theorem 5.5; selected Appendix C statements','selected question/definitions and internal result statements'),358389:('2305.07727','Section 5 Conjecture 5.6 and heuristic','selected question/definitions'),360679:('2311.04487','Section 4 definition of Phi, Definition 4.1; Theorems 4.2-4.7; Conjecture 4.8','selected question/definitions and internal result statements'),359290:('2307.13684','Conjecture 1.1 and attribution to [6]','selected passage; referenced proof body unread'),359291:('2307.13684','Conjecture 1.2; Theorem 1.3','selected question and internal result statement'),359327:('2307.15573','W_k definition; Theorems 1-3 and proofs; final counterexample paragraph','short mathematical body read; exact bridge failed')}
ds=[]
for x in rows:
 r=x['record'];i=r['mathdb_id'];scope,disp,reason=notes[i]
 ds.append({k:v for k,v in x.items() if k!='record'}|{'mathdb_id':i,'title':r['title'],'source_url':r['source_url'],'corpus_reported_completeness':r['statement_completeness'],'literal_statement_scope':scope,'complete_mathematical_statement_review':scope=='complete','complete_self_contained_statement':scope=='complete','quantifiers':'Exact quantifiers retained in statement; scope-specific obligations in technical_review.','disposition':disp,'technical_review':reason,'evidence_level':sources[i][2] if i in sources else 'literal statement review only','primary_passage':{'version':'v1','url':'https://arxiv.org/html/'+sources[i][0]+'v1','locator':sources[i][1]} if i in sources else None,'source_coverage':{'selected_primary_passage_read':i in sources,'whole_mathematical_body_read':i==359327,'full_dependency_audit':False,'closest_successor_body_clearance':False,'registry_evidence':'unavailable HOLD'},'accepted_credit':0,'current_registry_cleared':False,'novelty':'HOLD; no inference from open labels or search absence'})
write('dispositions.json',ds);write('proposals.json',[])
refs=read(D/'flat-bindings.json')
for p in [L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py']:
 b=p.read_bytes();refs.append({'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)})
write('flat-bindings.json',refs)
ex=read(L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json');hi=read(L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json')
def ids(o):
 out=set()
 if isinstance(o,dict):
  for k,v in o.items():
   if str(k).isdigit():out.add(int(k))
   if k in ['mathdb_id','related_mathdb_id'] and isinstance(v,int):out.add(v)
   out|=ids(v)
 elif isinstance(o,list):
  for v in o:out|=ids(v)
 return out
inter=sorted(set(notes)&(ids(ex)|ids(hi)))
write('context-check.json',{'accepted_historical_id_matches':inter,'cayley_r363':'read after binding; no upgrade from abstraction-level retirement','r609_adjudications':'338290/339564/372627 retired,337963 parked; all protected excluded','baseline_literal_reviews':6183,'reservation_sets':[602,606,610],'r608':'completed/reconciled','routing_metadata_rows':8000,'counts':{'additional':9,'total':39,'next':40}})
counts=collections.Counter(x['literal_statement_scope'] for x in ds)
write('source-coverage.json',{'rows':{str(i):{'version':'v1','url':'https://arxiv.org/html/'+a+'v1','passages':loc,'coverage':cov} for i,(a,loc,cov) in sources.items()},'not_claimed':['whole-body clearance for other records','full dependency audit','successor/prior body clearance','current registry clearance'],'scope_counts':dict(counts),'registry':'Unavailable: HOLD, no outbound registry requests or absence-of-hits inference','fetched_html_count':5,'pdf_count':0})
(D/'failures.md').write_text('''# Failures and stopped routes

Executed source-bridge check for 359327: join(K2,2K2) fails the literal neighborhood condition at its two universal vertices, alpha=2. The source paragraph therefore has not cleared the exact MathDB statement. Preserve this failed check; no further sweep.

360679: n=k=2 gives a trivial stronger-wording failure only; it does not defeat equality of maxima. Missing absolute-value and primitive-root conventions matter. No credit. 358388 fixed versus n-dependent coupling wording is parked; no rigorous new stochastic theorem claimed.

Five permitted arXiv HTML fetches succeeded. Zero MathDB requests, zero PDF downloads, no HTTP failures or guard failures. No forbidden APIs, browser/preview, TLS bypass, private headers, messages, uploads or publication. All outbound requests used only generic User-Agent and Accept headers.

The current proof registry is unavailable: HOLD. AIM/Kourovka/EGRES/AIProofWatch, DMGT TLS, ProjectEuclid challenge, ResearchGate403 and OEIS A274199/internal403 stay parked without retry or alternate-route fishing. No closest successor bodies were fetched: no target survived screening for promotion. Incomplete definitions are unresolved, never counted as complete reviews. No upstream verify.py was executed. No children, git, shared edits, Lean or manuscript changes.

Process limits: initial inventory/queue display was truncated by output limits; relevant literal rows and selected mathematical passages were read subsequently. Extraction includes unused site scripts/styles as text; they were never executed. No scientific inference relies on them. Integrity PASS will not imply math/novelty PASS.
''')
(D/'SUMMARY.md').write_text(f'''# Sol r610 breadth screening

Reviewed all **50 assigned literal records** from exact r609 queue-r610.json/reserved-ids-r610.json. **{counts['complete']} complete self-contained mathematical statement reviews**; {50-counts['complete']} definition-dependent, scope-ambiguous or incomplete records retain those flags. Zero proposals, zero credit. Root-only reconciliation would move the reported literal baseline 6,183 to 6,233; this lane changes no shared coverage. Counts remain 9 additional / 39 total / next 40.

Independent integrity checks bind the r609 manifest/receipt, exact payload, direct original/copy pairs, all twenty original r301 corpus chunks and eight frozen inputs in place. All three current fifty-ID reservations are disjoint from each other, baseline coverage and protected IDs. Corpus line locations, exact UTF8 statements, statement hashes and canonical record hashes are retained per row. The routing queue's 8,000 rows remain metadata only. r304 exclusions/history and r363 Cayley decision were bound/read; current adjudications are preserved. Context ID overlap: {inter}.

Five arXiv v1 HTML bodies fetched with generic headers and bound before extraction; text derivatives bound before reading. Seven records received selected primary passage readings. 357497 is source-refuted by the reflected-tree proof, with no new credit. 359290 has only a source report of resolution in [6], not that proof body. 359291's nearby theorem has an extra generalized-pyramid exclusion. 359327's short body was read, but its proposed graph failed the exact literal predicate in an executed finite check. 360679's all-maximizer wording differs from maximum equality; the n=k=2 observation supplies no qualifying outcome. 358388/358389 remain model/coupling HOLD.

No full dependency, closest-successor or current-registry clearance; registry unavailable means HOLD. No substantial proof investment or repeated sweep. Records reporting public resolutions were not upgraded to proof-body audits. Read dispositions.json, source-coverage.json and failures.md for per-row limits.

Run the independent **read-only** verifier under the fixed helper guard with OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 and python3 -B. verify.sh provides the exact command. It exits nonzero on any mismatch. manifest.json covers every lane payload including verifier and scripts, excluding only itself and final-verification-receipt.json. Separate receipt records the manifest SHA256/size and bounded hash/size/extra-file rejection tests. Integrity is not math or novelty acceptance.
''')
print(dict(counts));print('context overlap',inter)
