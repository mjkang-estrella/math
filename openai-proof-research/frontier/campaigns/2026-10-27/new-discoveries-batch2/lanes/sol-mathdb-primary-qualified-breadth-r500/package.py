import pathlib,json,hashlib,datetime,re
O=pathlib.Path(__file__).resolve().parent
J=lambda p:json.loads(p.read_text())
def put(n,x):(O/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def sha(b):return hashlib.sha256(b).hexdigest()
notes={int(t[0]):t[1:] for t in [v.split('\t',2) for v in (O/'technical-notes.tsv').read_text().splitlines()]};assert len(notes)==50
sources=J(O/'source-provenance.json'); by={s['url'].rsplit('/',1)[-1]:s for s in sources}
# Only passage scopes actually examined; no whole-body review inferred from retained bytes.
patterns={'2203.14842':['Definition 1.','Conjecture 4.'],'2203.17221':['Conjecture 5.','Remark 4.2.'],'2204.02740':['Conjecture 3.2.'],'2204.04684':['Conjecture 2.2.'],'2204.05287':['Conjecture 5.'],'2204.06101':['Theorem 8.','Conjecture 2.'],'2204.07638':['Theorem 1.2.','Theorem 2.2.'],'2204.07972':['Conjecture 1.2.'],'2204.08218':['Conjecture 1.8'],'2204.09884':['possible isolated vertices'],'2204.12012':['Conjecture 1.1','Theorem 1.2'],'2205.05530':['ConjectureP4.3.','Conjecture 5.3.'],'2205.03965':['Conjecture 1.4.'],'2205.04398':['Theorem 1.1.'],'2206.00594':['Conjecture 1.3.'],'2206.04260':['Conjecture 2 (','Conjecture 3 (','Conjecture 4 ('],'2206.15307':['Conjecture 1.'],'2206.15414':['Theorem 3.','Corollary 5.'],'2207.02271':['Definition 4.2.'],'2207.03941':['Conjecture 27'],'2207.10545':['Conjecture 1.'],'2207.14210':['Theorem 2'],'2208.06630':['Conjecture 1.','(iii) After'],'2208.08506':['Theorem 3.5.'],'2208.12209':['false for general'],'2209.08946':['Conjecture 1 (','We construct a family'],'2209.09221':['Conjecture 10.1.'],'2210.13286':['Theorem 1.3.','Proof of Theorem 1.3.']}
passages=[]
for a,terms in patterns.items():
 lines=(O/by[a]['text']).read_text().split('\n')
 for term in terms:
  hits=[i for i,x in enumerate(lines) if term in x]
  if hits:
   i=hits[0];b=max(0,i-2);e=min(len(lines),i+12);passages.append({'source':a,'file':by[a]['text'],'line_start':b+1,'line_end':e,'text':'\n'.join(lines[b:e]),'scope':'selected passage; no complete body/dependency claim'})
put('primary-passages.json',passages)
rows=[]
for x in J(O/'assigned-records.json'):
 r=x['record'];a=r['source_url'].rsplit('/',1)[-1];d,reason=notes[r['mathdb_id']];loc=[{'file':p['file'],'line_start':p['line_start'],'line_end':p['line_end']} for p in passages if p['source']==a]
 rows.append({'ID':r['mathdb_id'],'literal':r['statement'],'chunk':x['chunk'],'line':x['line'],'statement_utf8_sha256':sha(r['statement'].encode()),'canonical_record_sha256':sha(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()),'source_url':r['source_url'],'canonical_url':r['canonical_url'],'disposition':d,'technical_reason':reason,'evidence_levels':{'record':'all literal statement and quantifiers read','primary':'selected passages read' if loc else 'retained primary; no exact body review claimed','primary_locators':loc,'whole_primary_body_read':False,'proof':'2204.07638 section 2 proof read; external dependencies not audited' if r['mathdb_id']==354294 else 'no complete target proof independently replayed','successor':'2210.13286 Theorem 1.3 and selected rank/support proof passages read' if r['mathdb_id'] in [355686,355687] else 'no complete successor search/proof audit','dependencies':'incomplete; no formal replay','registry':'HOLD; zero MathDB requests; inherited 429; no current registry clearance'},'duplicate_prior_status':'public source match/subsumption or scope issue as specified in technical_reason; no global novelty claim','accepted_credit':0,'prior_cleared':False,'source_scope_cleared':False})
assert len(rows)==50;put('dispositions.json',rows);put('proposals.json',[])
put('coverage.json',{'baseline_reported_reviews':3683,'assigned_statements_read':50,'additional_accepted':0,'potential_reported_review_union_after_root_integration':3733,'root_integration_performed':False,'qualified_briefs':0,'other_active_breadth_reservations':0,'active_hypothesis_ids':[338290,337963],'counts':{'additional':9,'total':39,'next':40},'source_scope':'selected passages only; retained PDFs are not whole-body/proof review','mathdb_requests':0,'current_registry':'HOLD'})
put('source-coverage.json',{'retained_pdfs':len(sources),'assigned_distinct_primaries':len(sources)-1,'successor':'https://arxiv.org/pdf/2210.13286','selected_passage_sources':len(patterns),'whole_bodies_reviewed':0,'complete_independent_dependency_audits':0,'formal_proofs':0,'registry_cleared':False,'reading_scope':'Literal records all fifty; source-specific selected passages only. 354294 source section 2 proof read without dependency audit; 356157 construction not full maximality proof; successor rank invariant only selected proof passages. Others retained or passages as per rows. No claim of exhaustive successor search.'})
put('failures.json',{'workflow_deviations':[{'stage':'first inspection','failure':'Printed unrelated baseline coverage records before intake validation; output truncated. Violates requested display/timing discipline. Cannot be retroactively repaired by later matching hashes. Subsequent reads restricted to assigned records and frozen administrative adjudications.'},{'stage':'display output','failure':'Several primary/search outputs truncated; no unread portions counted as proof/body review. Retained complete bytes are available, but retention is not review.'}],'network_failures':[s for s in sources if s.get('status')=='failure'],'inherited_holds':['MathDB 429: zero requests','DMGT TLS','ProjectEuclid challenge','ResearchGate403','AIM-Kourovka-EGRES','AIProofWatch'],'restricted_routes_used':False,'upstream_verifiers_executed':False,'guard_limits':{'address_space_MiB':512,'CPU_seconds':210,'wall_seconds':230},'no_complete_candidate_lost':True})
# One exact arithmetic witness, deliberately rejected as omitted-domain convention.
A=[[0,1,0],[1,0,0],[0,0,0]]
assert sum(sum(v) for v in A)//2==1
assert all(sum(A[i][k]*A[j][k] for k in range(3))==0 for i in range(3) for j in range(i+1,3) if A[i][j])
put('cheap-checks.json',{'354351':{'adjacency':A,'edge_count':1,'characteristic_polynomial':'lambda*(lambda-1)*(lambda+1)','spectral_radius':1,'booksize':0,'not_complete_bipartite':'nonempty complete bipartite graph has no isolated vertex','source_convention':'2204.09884 explicitly ignores isolated vertices','conclusion':'literal domain defect only; accepted_credit=0'},'finite_evidence_used_as_universal_proof':False})
# Exact historical intersection only; never display unrelated entries.
ids=set(notes);hist=[]
for p in sorted((O/'frozen/root-mathdb-accepted-exclusions-r304').glob('*.json')):
 data=p.read_text();hits=[i for i in ids if re.search(r'(?<!\d)'+str(i)+r'(?!\d)',data)];hist.append({'path':str(p.relative_to(O)),'assigned_id_mentions':hits})
put('history-intersection.json',hist)
# Extend flat original references, but no recursion through historical binding files.
refs=J(O/'flat-bindings.json')
for p in [O.parents[6]/'AGENTS.md'] if False else []:pass
for p in [O.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',pathlib.Path('openai-proof-research/AGENTS.md'),O.parent.parent/'AGENTS.md']:
 refs.append({'path':str(p.resolve()),'size':p.stat().st_size,'sha256':sha(p.read_bytes())})
put('flat-bindings.json',list({r['path']:r for r in refs}.values()))
put('adjudications-carried.json',J(O/'frozen/root-mathdb-abelianisation-retirement-intake-r499/adjudications.json'))
print('packaged',len(rows),'dispositions;',len(sources),'PDFs; historical assigned-ID mentions',sum(len(h['assigned_id_mentions']) for h in hist))
