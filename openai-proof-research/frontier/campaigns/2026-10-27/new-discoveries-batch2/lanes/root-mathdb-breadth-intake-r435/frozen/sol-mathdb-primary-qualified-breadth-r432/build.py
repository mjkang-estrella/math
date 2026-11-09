import pathlib,json,hashlib,collections
O=pathlib.Path(__file__).resolve().parent;L=O.parent
load=lambda p:json.loads(p.read_text())
rows={int(x.split('\t')[0]):x.rstrip('\n').split('\t')[1:] for x in (O/'assessments.tsv').open()};rs=load(O/'records.json');loc={x['mathdb_id']:x for x in load(O/'record-locations.json')};assert len(rows)==50
ranges={'4539':[(1475,1610)],'4791':[(298,366),(430,491)],'4798':[(2290,2350)],'4800':[(1674,1815)],'11129':[(640,680)],'11134':[(350,415)],'11136':[(203,245),(2050,2132)],'hultman':[(230,310)]}
ex=[]
for key,spans in ranges.items():
 p=O/'sources'/(key+'.txt');lines=p.read_text().splitlines(keepends=True)
 for a,b in spans:ex.append({'file':str(p.relative_to(O)),'first_line':a,'last_line':b,'text':''.join(lines[a-1:b]),'inspection':'read in this screen; dependencies not closed'})
(O/'source-excerpts.json').write_text(json.dumps(ex,ensure_ascii=False,indent=2)+'\n')
primary={396801:'4539',396802:'4539',396803:'4539',396808:'4791',396810:'4791',396812:'4791',396925:'4798',396950:'4800',397255:'11129',397284:'11134',397303:'11136',397325:'11136'}
ds=[]
for r in rs:
 i=r['mathdb_id'];status,scope,reason=rows[i]
 ds.append({'mathdb_id':i,'title':r['title'],'literal_statement':r['statement'],'literal_statement_sha256':loc[i]['statement_sha256'],'canonical_record_sha256':loc[i]['canonical_sha256'],'canonicalization':'json.dumps(record,sort_keys=True,ensure_ascii=False,separators=(comma,colon)), UTF-8','source_url':r['source_url'],'original_record_location':loc[i],'scope_quantifiers':scope,'disposition':status,'reason_and_mechanism_obstacle':reason,'evidence_level':'cached_full_literal_statement_read','primary_level':'selected_report_body_read' if i in primary else 'not_inspected_HOLD_source_clearance','primary_file':'sources/'+primary[i]+'.pdf' if i in primary else None,'proof_level':'characterization proof Theorem 3.2, Lemmas 3.1/3.3 and example read; dependencies open' if i==396925 else ('report theorem or algorithm explanation read; full proof not inspected' if i in primary else 'not_inspected'),'successor_level':'author-hosted Hultman manuscript body read; version not independently pinned to latest' if i==396925 else 'not_cleared','registry_level':'HOLD_current_registry_not_obtained','prior_cleared':False,'dependency_closure':False,'new_certificate':None,'bounded_check_executed':'literal full statement and scope screen; selected body applicability comparison' if i in primary else 'literal full statement and quantifier/mechanism screen only','next_check_planned_not_executed':'No investment recommended. Primary/proof/current registry gates required before any hypothesis proposal.','accepted_credit':0})
(O/'dispositions.json').write_text(json.dumps(ds,ensure_ascii=False,indent=2)+'\n');(O/'proposals.json').write_text('[]\n')
# Administrative reconciliation is scoped to the fifty IDs; no scientific claims inherited from summaries.
a=load(next(L.glob('*r304'))/'accepted-exclusions.json');h=load(next(L.glob('*r304'))/'historical-dispositions.json')
ids={r['mathdb_id'] for r in rs}
# Extract numeric record IDs explicitly present as keys or mathdb_id fields.
def ids_in(x):
 out=set()
 if isinstance(x,dict):
  for k,v in x.items():
   if str(k).isdigit():out.add(int(k))
   if k in ('mathdb_id','mathdb_related_id') and isinstance(v,int):out.add(v)
   out|=ids_in(v)
 elif isinstance(x,list):
  for v in x:out|=ids_in(v)
 return out
matches={'accepted':sorted(ids&ids_in(a)),'historical':sorted(ids&ids_in(h))}
assert not matches['accepted'] and not matches['historical']
prov={'lane':O.name,'date':'2026-10-31','assignment':'root-mathdb-breadth-intake-r431','baseline_reported_reviews':2183,'active_r430_reservation_count':50,'statement_reviews':50,'selected_primary_report_body_reviews':len(primary),'full_dependency_closures':0,'new_briefs':0,'mathdb_requests':0,'current_registry':'not obtained: HOLD; no novelty claim','administrative_matches':matches,'r363_exclusion':364119,'counts_unchanged':{'additional':9,'total':39,'next':40},'scientific_limits':'Downloads, selected report-body inspection, proof-body inspection and dependency closure are distinct. No whole-corpus technical review claimed. No new computations, sweeps, formalization or manuscripts.'}
(O/'provenance.json').write_text(json.dumps(prov,indent=2)+'\n')
(O/'search-evidence.json').write_text(json.dumps({'date':'2026-10-31','queries':['Moser union free subfamily 2 sqrt m Fox Lee Sudakov theorem','Bousfield equivalence stable module category finite group support classification','inversion arrangement regions Bruhat interval Hultman theorem'],'leads':['https://arxiv.org/abs/1012.3127','https://arxiv.org/abs/1010.0515','https://annals.math.princeton.edu/2011/174-3/p06'],'status':'search leads only; no current registry clearance; author Hultman body downloaded separately'},indent=2)+'\n')
counts=collections.Counter(d['disposition'] for d in ds)
(O/'SUMMARY.md').write_text('''# r432 bounded fifty-record screen

Read exactly the fifty assigned full literal cached statements. Baseline 2,183 reported reviews and the fifty r430 active reservations are disjoint; exclusions checked. Queue metadata was used only for assignment. Original SHA256 and sizes were frozen before scientific reading, including r431 manifest/direct originals, r301 manifest and all twenty original chunks (using bytes), r304 accepted/history, and r363 exclusion. Flat references only; no corpus snapshots or upstream verifiers.

Zero hypothesis briefs. Nine records are retired at a public-statement level, one at a selected public-proof level, and one as a routine module-syzygy adaptation. These are evidence-qualified triage dispositions, not claims that every cited proof has been replayed. Hultman's Theorem 3.2 characterization, Lemmas 3.1/3.3 and source-internal example were read; cited dependencies remain open. The union-free report already states stronger exact/general bounds; the support-theory report already characterizes Bousfield equivalence. The remaining records are parked with specific full-scope obstacles or held for missing source/successor scope. See dispositions.json for exact quantifiers and applicability bridges.

Selected sections from seven primary report PDFs and one author manuscript were inspected (12 assigned records have selected primary-body review). No latest-version clearance, full dependency closure, current proof-registry clearance, or novelty is asserted. Missing current registry is HOLD throughout. The author union-free PDF returned 404; report statements suffice only for statement-level retirement. No source access gap is classified as hardness. All inherited denied routes remain parked.

Zero MathDB requests; no browser, forbidden hosts, GitHub routes, messages, uploads or publication. No new certificate or costly sweep. Counts remain **9 additional / 39 total / next 40**. This screen does not establish whole-corpus coverage.

Verification: from this lane's directory run the packet helper_guard.py with python3 -B verify.py, setting OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1. verify.py independently reads and checks originals, chunk manifests, assignment/disjointness, canonical/literal hashes, excerpts, and exact payload set. Only manifest.json and final-receipt.json are excluded by exact relative paths. The final receipt reports the sealed-payload check.

Disposition counts: '''+json.dumps(dict(counts),sort_keys=True)+'\n')
print(json.dumps(dict(counts)))
