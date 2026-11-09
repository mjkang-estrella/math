import pathlib,json,hashlib,itertools,datetime
L=pathlib.Path(__file__).resolve().parent
def save(n,v): (L/n).write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n')
def digest(b):return hashlib.sha256(b).hexdigest()
notes={int(a):(b,c) for a,b,c in (line.rstrip('\n').split('\t',2) for line in (L/'notes.tsv').open())}
rows=json.loads((L/'literal-records.json').read_text());out=[]
missing={404986,405888,315920,316165,316182,316195,316202,316341,316406,316574,316731,316801,317423,317441,317776,318078,318507,318671,319175,319407}
for x in rows:
 r=x['record'];i=r['mathdb_id'];d,n=notes[i]
 out.append({'mathdb_id':i,'title':r['title'],'statement':r['statement'],'statement_utf8_sha256':digest(r['statement'].encode()),'canonical_record_sha256':x['canonical_record_sha256'],'corpus_path':x['corpus_path'],'corpus_line_1based':x['line'],'source_url_record':r['source_url'],'disposition':d,'technical_disposition':n,'scope_flags':{'literal_record_read':True,'self_contained_mathematical_statement':i not in missing,'all_record_quantifiers_screened':True,'selected_primary_passage_read':i in {317193,318548,319095},'whole_primary_body_read':False,'selected_successor_proof_body_read':i==317193,'local_full_scope_route_developed':i==318548,'full_dependency_audit':False,'current_registry_cleared':False,'novelty_cleared':False,'mathematical_PASS':False},'accepted_credit':0})
assert len(out)==len(notes)==50
save('dispositions.json',out);save('proposals.json',[])
pairs=0
for m in range(9):
 def heights(v):return tuple(z for bit in v for z in ((0,1,2,1) if bit else (0,1,0,1)))+(0,)
 vs=list(itertools.product((0,1),repeat=m));hs={v:heights(v) for v in vs};assert len(set(hs.values()))==len(vs)
 for a in vs:
  for b in vs:
   assert tuple(map(min,hs[a],hs[b]))==hs[tuple(map(min,a,b))]
   assert tuple(map(max,hs[a],hs[b]))==hs[tuple(map(max,a,b))];pairs+=1
save('bounded-checks.json',{'executed':True,'check':'UDUD/UUDD Boolean-to-Dyck block injection and pointwise min/max for every pair of bitstrings of lengths 0..8','pairs':pairs,'result':'PASS','limit':'finite check of an elementary block mechanism only; no novelty or general lattice theorem certified','planned_searches_executed':False})
coverage=[{'mathdb_id':317193,'primary':'0803.2901v1 Conjecture1.1, text lines125-155; graph/eigenvalue definitions selected','successor':'1207.3878v1 Theorems1.4-1.7 lines110-182 and Section5 lines697-740','scope':'exact weak endpoint Theorem1.7 proof and local dominance proof read; Lemmas4.6/4.7 and shifted-Schur dependencies not audited; v1 strict comparison has equality caveats, not used as a new certified theorem','whole_body':False}, {'mathdb_id':318548,'primary':'0905.3764v1 Section2.1/2.2 path order and Birkhoff statement, Section3.1 type(a,b), Section3.3 Conjecture3.11 lines440-461','scope':'selected definitions and source-internal representation statement read; elementary block route only. No successor proof body clearance; routine adaptation suffices to stop.','whole_body':False}, {'mathdb_id':319095,'primary':'0910.1956v1 Conjecture1.1 lines100-124; Theorem1.3 lines285-295; Section10.4 lines3143-3169','scope':'exact source proof passage read; variational principle and measure theorem accepted as cited dependencies without proof audit; extracted font spacing defective but formula/quantifiers legible','whole_body':False}]
save('source-coverage.json',coverage)
failures={'inherited_parked':'MathDB429; AIM/Kourovka/EGRES/AIProofWatch; DMGT TLS; ProjectEuclid challenge; ResearchGate403; OEIS A274199/internal403; r578 HTML404/author certificate failure/Christensen-Hovey timeout. None retried or bypassed.','registry':'Current proof registry unavailable: HOLD for all fifty; no absence-of-hits inference.','local_failures':['Initial sha256sum/wc glob encountered four frozen directories; preserved partial stdout inventories, then complete direct-path bindings verified via bind.py.','Initial full fifty-statement stdout was truncated; missing middle 316089..317423 read in bounded followups. No truncated output counted as full reading.','Some source locator output was truncated; relevant passage reads followed.','Search results incidentally included ScienceDirect/ResearchGate indexed snippets; no such pages requested or used as primary proof evidence.'], 'access':{'MathDB_requests':0,'new_HTTP_failures':0,'browser_requests':0,'bypasses':0},'stopped_routes':['No finite graph sweep for315993 before prior-body clearance.','No odious-prime sieve before restoration of316406.','Dyck construction stopped at routine classical adaptation; no discovery investment.','Derangement successor v1 has strict-comparison equality caveats; no independent general proof certification claimed.'],'limits':'Every Python/helper computation under unchanged fixed helper_guard.py; 512MiB AS/groupRSS,CPU210s,wall230s; no limit failures.'}
save('failures.json',failures)
refs=json.loads((L/'flat-bindings.json').read_text());seen={r['path'] for r in refs}
for p in [L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py']:
 b=p.read_bytes();refs.append({'path':str(p),'sha256':digest(b),'size':len(b)})
for r in json.loads((L/'source-provenance.json').read_text()):
 for q in [r,r.get('derivative',{})]:
  if 'path' in q and q['path'] not in seen: refs.append({k:q[k] for k in ('path','sha256','size')});seen.add(q['path'])
save('flat-bindings.json',refs)
save('prior-context-check.json',{'bound_before_read':True,'r304':'Accepted families and historical dispositions inspected as administrative screening leads; no assigned ID overlap in record-association fields claimed from substring hits. Small ID32 substring hits not an exclusion.','r363':'364119 excluded as source adaptation; no change.','r595':'Adjudications read and preserved. Protected IDs unchanged;372522 proof-gap ruling retained;344924,386396,387650 restoration judgments untouched outside assignment.','counts':'9 additional /39 total /next40 unchanged','reservation_check':'Three sets of50 pairwise disjoint, outside5833 reviewed records and protected IDs; Claude r504 and Sol r594 untouched.'})
