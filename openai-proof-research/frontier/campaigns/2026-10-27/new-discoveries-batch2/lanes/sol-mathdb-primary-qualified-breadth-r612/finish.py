import pathlib,json,hashlib,datetime,collections
P=pathlib.Path(__file__).parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r611'
def j(p):return json.loads(p.read_text())
def write(n,x):(P/n).write_text(json.dumps(x,ensure_ascii=False,sort_keys=True,indent=2)+'\n')
def h(x):return hashlib.sha256(x).hexdigest()
notes={}
for line in (P/'review-notes.tsv').read_text().splitlines():
 id,c,q,d,n=line.split('\t');notes[int(id)]=(c,q,d,n)
rows=j(P/'literal-records.json');assert len(notes)==len(rows)==50
coverage={361167:('2312.09482','Conjecture4.11, Remark4.12; Theorem4.6 proof and Corollary4.10 proof, selected Section4 definitions','Reference [23] classification not independently audited'),362720:('2404.07670','TableI phi9, SectionV Definition3 recurrence/modulus, Conjecture2 and its proof paragraph; selected error-correction discussion','Other deletion-correction proofs and references not fully audited'),363495:('2406.07109','Conjecture21 and immediately preceding numerical discussion','No full dependency audit; source [20] rank-one theorem not fetched'),363346:('2406.00139','Introduction definitions, Conjecture1 and entire Theorem4.1 proof (Section4 before4.1 examples)','Rest of paper not comprehensively read; no formal replay')}
ds=[]
for x in rows:
 r=x['record'];id=r['mathdb_id'];c,q,d,n=notes[id]
 ds.append({'mathdb_id':id,'title':r['title'],'canonical_url':r['canonical_url'],'corpus_chunk':x['corpus_chunk'],'corpus_line':x['corpus_line'],'statement_utf8':r['statement'],'statement_utf8_sha256':h(r['statement'].encode()),'canonical_record_sha256':h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()),'statement_completeness':r['statement_completeness'],'source_scope_flags':{k:v for k,v in r.items() if 'scope' in k or 'complete' in k},'technical_statement_class':c,'complete_self_contained_statement':c=='complete','quantifier_scope_review':q,'disposition':d,'technical_review':n,'source_url':r['source_url'],'source_body_coverage':coverage[id][1] if id in coverage else 'No primary body read; literal corpus statement screening only','whole_body_read':False,'full_dependency_audit':False,'source_internal_checked':id in coverage,'successor_body_read':False,'current_registry_cleared':False,'novelty_status':'HOLD; no global absence inference','discovery_credit':0})
write('dispositions.json',ds);write('proposals.json',[])
write('source-coverage.json',{'records':[{'mathdb_id':id,'version_url':'https://arxiv.org/html/'+v[0]+'v1','body_coverage':v[1],'dependency_limit':v[2],'whole_body_read':False,'successor_bodies_read':0} for id,v in coverage.items()],'primary_bodies_selected':4,'whole_papers_comprehensively_read':0,'registry':'Unavailable by task restriction; not queried; HOLD','search_matches_are_not_proof':True,'sources_for_other_records':'Literal corpus only; no freshness or public-resolution claim'})
write('search-log.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'tool':'web search; no browser','queries':['site:arxiv.org "linear intersection pairs" conjecture Li Shi Ling','site:arxiv.org "Naisargik" Helberg','site:arxiv.org "symmetric" "rank-completing" "double" pencils','site:arxiv.org "Fu" "Tang" "parity" "inequalities" partitions','site:arxiv.org/abs/ "On Naisargik Images" "2025"','site:arxiv.org "real symmetric" "random eigenvalues" "multiplicity" "rank-completing"','site:arxiv.org/abs/ "Guenda" "conjecture" "intersection" "2025"'],'results':['https://arxiv.org/abs/2406.00139','https://arxiv.org/abs/1705.10067','https://arxiv.org/abs/2404.07670','https://arxiv.org/abs/2204.00905'],'second_search_results':[],'interpretation':'Bounded discovery only. No closest successor body established or read; empty results do not clear prior art. Stop rather than repeated fishing.'})
# Reconcile full bound administrative structures without treating them as technical proof.
res=j(I/'reserved-ids-r612.json');ids=set(res['ids']);ae=j(L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json');hd=j(L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json')
def allids(x):
 if isinstance(x,dict):
  for k,v in x.items():
   if k in ['mathdb_id','related_mathdb_id'] and isinstance(v,int):yield v
   else:yield from allids(v)
 elif isinstance(x,list):
  for y in x:yield from allids(y)
assert not ids&set(allids(ae)) and not ids&set(allids(hd))
write('prior-context-check.json',{'accepted_families':ae['accepted_family_count'],'accepted_associated_id_overlap':sorted(ids&set(allids(ae))),'historical_id_overlap':sorted(ids&set(allids(hd))),'cayley_decision_read':True,'current_adjudications_read':True,'ledger_counts':{'additional':9,'total':39,'next':40},'no_target_promoted':True,'note':'Exact family scope remains binding; lack of an ID overlap is not family-level novelty clearance.'})
write('failures.json',{'http_failures':[],'stopped_routes':['No source-faithful general Helberg recurrence bridge developed after n<=7 checks','No closest successor body located by bounded queries; no clearance inferred','Pencil all-eigenvalues literal shortcut stopped as source-scope correction','Other incomplete or definition-dependent statements not promoted'],'parked_access':['MathDB429: zero requests','OEIS A274199/internal403: zero requests','AIM/Kourovka/EGRES/AIProofWatch','DMGT TLS','ProjectEuclid challenge','ResearchGate403','Google/GitHub APIs/raw/codeload/diff','ScienceDirect','current proof registry unavailable'], 'deviations':['Initial full-record display exceeded output limit. Subsequently redisplayed all omitted statement ranges using compact statement-only views. No review credit inferred from truncated metadata output.'],'resource_failures':[],'negative_tests':'See negative-tests.json; no originals mutated','novelty':'HOLD for all records'})
counts=collections.Counter(d['technical_statement_class'] for d in ds)
(P/'SUMMARY.md').write_text('''# Sol breadth r612

Reviewed all **50 assigned literal records**, with exact UTF-8 statements, original chunk/line locations and canonical record hashes in dispositions.json. This is literal technical screening, not whole-body or full-corpus proof coverage. Baseline remains **6,233** reported reviews; routing 8,000 metadata rows earns zero review credit. No shared coverage or counts changed.

**0 proposals; 0 discovery credit.** Campaign counts remain 9 additional /39 total /next40. Current registries unavailable: every novelty gate HOLD.

Technical classifications: '''+json.dumps(dict(counts))+'''. Original completeness/scope flags are preserved separately; metadata “full” has not been upgraded to self-contained technical completeness.

Four selected primary bodies read, all arXiv v1 HTML, with byte bindings before extraction and text bindings before searching. No PDF was used. Source-internal exclusions: 361167 is explicitly refuted for binary codes (Conjecture4.11/Remark4.12, Corollary4.10); 363346 is already proved in Theorem4.1, whose complete injection proof was read. These are posted-result exclusions, not new proof certification. Pencil363495 has a material source-scope issue: the double-multiplicity clause concerns random eigenvalues; a simple prescribed eigenvalue is not a discovery.

Helberg362720: exact exhaustive checks for n=1..7 and every maximizing residue confirm source phi9 images equal individual binary residue classes. This is not a universal proof. The source's “Proof” paragraph for Conjecture2 reports finite data. No concrete nonroutine full-scope mechanism survived screening, so no brief is manufactured. Successor searches returned no inspected closest successor body; that is an unresolved gate, not absence evidence.

Integrity: intake exact payload, direct original/copy pairs, all20 original corpus chunks and8 frozen inputs checked in place. Three active50-record reservations are mutually disjoint, outside6233 coverage and protected IDs. r304 exclusions/history and r363 Cayley decision bound before use. Original source snapshots are flat references; no historical trees or corpus copied. The runnable verifier checks payload exactness, original bindings, corpus lines/canonical hashes, reservation disjointness and hash/size/extra-file rejection. Integrity PASS is not mathematical or novelty PASS.

All scripts run via the unchanged fixed helper guard with512MiB AS/groupRSS, CPU210s, wall230s. Zero MathDB requests, no forbidden routes, no external messages, no child agents, no git, Lean, manuscript or credit changes. HTTP requests used generic headers. Failures and stopped routes are retained in failures.json. See source-coverage.json for precise reading limits, source-provenance.json for UTC/URL/version/bytes, and final-verification-receipt.json for final seal.
''')
print(dict(counts))
