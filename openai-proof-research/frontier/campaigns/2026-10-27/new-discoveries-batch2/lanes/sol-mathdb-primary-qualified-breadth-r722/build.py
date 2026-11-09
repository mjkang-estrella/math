import pathlib,json,hashlib,collections
D=pathlib.Path(__file__).resolve().parent;L=D.parent
load=lambda p:json.loads(p.read_text())
def write(n,z):(D/n).write_text(json.dumps(z,ensure_ascii=False,indent=2)+'\n')
rows=load(D/'literal-records.json');a={}
for line in (D/'assessments.tsv').read_text().splitlines():
 i,c,r,t=line.split('\t');a[int(i)]=(c,r,t)
assert len(a)==50 and set(a)=={x['mathdb_id'] for x in rows}
coverage={381364:dict(primary='1708.06790v1 Conjecture1.1; Lemmas2.1-2.3,3.1; Theorem3.2 and proof read',lines=[[195,245],[260,455]],proof='selected construction and theorem proof body; external matroid dependencies not independently replayed',status='RETIRE_PUBLIC_SOURCE_COUNTEREXAMPLE'),381674:dict(primary='2206.04290v1 Theorem3,Conjecture2; Section3 Lemmas3.1-3.3 and selected proof',lines=[[350,380],[700,855]],proof='local Capelli/norm reduction read; LMFDB integral points and modular tables not replayed',status='PARK_FULL_SCOPE_OBSTRUCTION'),382479:dict(primary='2603.23228v1 Definitions2.1,2.2,3.2; Proposition3.1 proof; Conjecture5.3',lines=[[270,490],[690,865],[1752,1775],[2240,2325]],proof='selected local definitions and zero-layer proof; no full star/top dependency replay',status='HOLD_SOURCE_COMPANIONS')}
out=[]
for x in rows:
 i=x['mathdb_id'];c,r,t=a[i];z=x['record'];s=coverage.get(i)
 out.append(dict(mathdb_id=i,corpus_path=x['corpus_path'],corpus_line=x['line'],literal_line_sha256=x['literal_line_sha256'],canonical_record_sha256=x['canonical_record_sha256'],statement=z['statement'],statement_utf8_sha256=hashlib.sha256(z['statement'].encode()).hexdigest(),classification=c,classification_reason=r,quantifier_scope=r,technical_assessment=t,disposition=s['status'] if s else ('HOLD_MISSING_SCOPE' if c!='complete' else 'PARK_NO_FULL_SCOPE_ROUTE'),source_url=z['source_url'],source_version=(s['primary'].split()[0] if s else None),primary_passage_read=bool(s),primary_scope=s,whole_primary_body_read=False,local_proof_read=i in [381364,381674,382479],full_dependency_audit=False,closest_successor_body_read=False,current_registry='HOLD unavailable; zero MathDB requests',prior_cleared=False,accepted_credit=0))
write('dispositions.json',out);write('proposals.json',[])
write('bounded-calculations.json',dict(executed=[dict(mathdb_id=381364,source='1708.06790v1 Lemma2.2 (published construction)',internal_q=7,t=6,forbidden_uniform_minor='U_2,13',target_q=11,rank=3,line_count=7**2+(7+1)*6*5//2,claimed_bound=(11**3-1)//(11-1),strict_violation=169>133,credit=0)],not_executed=['No fifty-row computational proof search','No cubic modular table or integral-point replay','No partition graph enumeration or proof']))
write('source-coverage.json',dict(records=50,classification_counts=dict(collections.Counter(x['classification'] for x in out)),literal_review_only=47,selected_primary_passages=3,whole_primary_bodies=0,full_dependency_audits=0,closest_successor_bodies=0,registry='HOLD',details=coverage,limit='Search/abstract/metadata are not proof-body clearance. Cubic all-m and graph companion overlap remain open obligations; no substantial hypothesis investment or promotion.'))
f=load(L/'sol-mathdb-primary-qualified-breadth-r718/failures.json')
f['r722_failed_checks']=['prepare.py first reservation test double-counted own set: AssertionError len(sets)==3; corrected to active list once and reran PASS.','An irrelevant nonexistent sed path produced no content; no source read from that path.']
f['r722_deviations']=['Initial full-record print truncated; recovered all assigned statements in bounded display, first8 present in initial output and remaining8:30,30:50. No unassigned scientific records displayed.','Context print too broad and truncated; exact adjudications and Cayley decision were visible; no omitted ledger text claimed read.','No source-successor body search performed: no proposal promoted and no full-scope route established.']
f['adjudications']='r721: retire338290/339564/372627;park337963;exclude338366 modulo text/figure reconstruction defects and unread journal bodies;Cayley364119 excluded. Solr720 and HELD Clauder628 reservations preserved.'
f['new_http_failures']=[];f['mathdb_requests']=0;f['external_requests']=3
write('failures.json',f)
refs=load(D/'flat-bindings.json')
def bind(p):
 b=p.read_bytes();return dict(path=str(p),size=len(b),sha256=hashlib.sha256(b).hexdigest())
for p in [L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json']:
 refs.append(bind(p))
for n in ['accepted-exclusions.json','historical-dispositions.json']:
 assert (L/'root-mathdb-accepted-exclusions-r304'/n).read_bytes()==(L/'pi-mathdb-full-corpus-inventory-r301/frozen/root-mathdb-accepted-exclusions-r304'/n).read_bytes()
# Inspect exact assigned-ID membership only, without expanding historical trees.
e=load(L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json');h=load(L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json')
write('exclusion-checks.json',dict(accepted_lookup_matches={str(i):e['mathdb_lookup'][str(i)] for i in a if str(i) in e['mathdb_lookup']},historical_scope_keys=list(h),cayley_decision='root-mathdb-cayley-review-intake-r363/DECISION.md',adjudications='root-mathdb-breadth-intake-r721/adjudications.json',promotion=False))
refs=list({x['path']:x for x in refs}.values());write('flat-bindings.json',refs)
print(collections.Counter(x['classification'] for x in out))
