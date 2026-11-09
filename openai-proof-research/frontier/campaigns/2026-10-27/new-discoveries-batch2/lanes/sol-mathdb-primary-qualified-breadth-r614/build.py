from pathlib import Path
import json,hashlib,collections
L=Path(__file__).parent;I=L.parent/'root-mathdb-breadth-intake-r613'
def write(n,d): (L/n).write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
rows=json.loads((L/'literal-records.json').read_text());reviews={}
for line in (L/'reviews.tsv').read_text().splitlines():
 i,f,q,r=line.split('\t');reviews[int(i)]=(f,q,r)
assert len(reviews)==50
out=[]
for x in rows:
 d=x['record'];i=d['mathdb_id'];f,q,r=reviews[i]
 out.append({'mathdb_id':i,'title':d['title'],'corpus_chunk':x['chunk'],'corpus_line':x['line'],'exact_utf8_statement':d['statement'],'statement_utf8_sha256':hashlib.sha256(d['statement'].encode()).hexdigest(),'canonical_record_sha256':x['canonical_record_sha256'],'literal_record_review':True,'complete_statement':f=='C','incomplete_record':f=='I','missing_definitions':f=='M','ambiguous_scope':f=='A','quantifiers_and_scope':q,'individual_disposition':r,'primary_passage_read':i in [370667,370733,372430],'whole_body_read':False,'local_full_scope_proof':False,'full_dependency_audit':False,'source_url':d['source_url'],'source_version':'v1' if i in [370667,370733,372430] else 'not checked','current_registry_cleared':False,'prior_cleared':False,'accepted_credit':0})
write('dispositions.json',out);write('proposals.json',[])
coverage=[]
for i,a,lines,internal,objection in [
(370667,'2510.00251',[ [146,195],[450,525],[699,734],[850,878] ],'Definition1.1, Theorem1.2 and Lemma2.1 proof; final unnumbered conjecture.','The a!=b linear independence argument has diagonal a-b=0 on target and cannot bound diagonal maxima. Referenced numerical visualization [10] not fetched; no successor body or composite-modulus prior clearance.'),
(370733,'2510.02008',[[200,263],[627,854]],'Conjecture1.1, Proposition3.3 statement, Lemma3.4 proof, Theorem3.5 proof.','Oyengo dissertation Section1.6 not read. Existing n=0 mod4 theorem bounds a subsequence, which does not logically refute unboundedness over all n; no all-n result claimed.'),
(372430,'2601.03891',[[190,225],[1168,1340]],'Strong domination/stability definition, Theorem3.10 and its proof, Corollary3.11, Example3.12, Conjecture3.13.','Undefined critical set remains. Theorem3.10 proof says likely changes rather than proving it; its connectivity step also confuses <=p with <p. No reliance on that theorem, no fresh theorem/counterexample promoted.')]:
 coverage.append({'mathdb_id':i,'file':a+'.txt','url':'https://arxiv.org/html/'+a+'v1','selected_line_ranges_read':lines,'source_internal_results':internal,'objection_and_limit':objection,'whole_body_coverage':False,'full_dependencies':False,'closest_prior_body_clearance':False,'successor_body_clearance':False})
write('source-coverage.json',{'literal_record_reviews':50,'complete_statements':sum(x['complete_statement'] for x in out),'flags':dict(collections.Counter(reviews[i][0] for i in reviews)),'selected_primary_records':3,'primary_readings':coverage,'all_other_records':'Literal statements only; no primary source or prior-body claim.','registry':'HOLD; current registry unavailable; zero requests; absence of hits not evidence.','routing_metadata':'8000 routing rows are metadata only, not technical coverage.','restoration_flags':'Inherited coverage retained upstream; no restoration assignments created.'})
# Inspect full small flat administrative contexts after binding, without copying trees.
contexts=[]
for name in ['accepted-exclusions.json','historical-dispositions.json']:
 p=L.parent/'root-mathdb-accepted-exclusions-r304'/name;data=json.loads(p.read_text());raw=json.dumps(data)
 contexts.append({'path':str(p),'assigned_id_string_matches':[i for i in reviews if str(i) in raw],'limit':'Administrative scope comparison only; not a public proof-body audit.'})
write('context-check.json',{'baseline':6283,'intake':'r613','active_lanes':['claude r602','sol r612','sol r614'],'r610':'completed/reconciled, not active','campaign_counts':[9,39,40],'r304':contexts,'r363':'Read bound DECISION.md: Cayley364119 source-adaptation exclusion retained.','adjudications':'r613 retirement338290/339564/372627 and park337963 retained; no protected IDs assigned.'})
(L/'failures.md').write_text('''# Limits and stopped routes

No failed HTTP fetches in this lane. Three primary HTML v1 fetches used generic headers; bytes were bound before extraction and text derivatives bound before searches. No PDFs used. No MathDB requests, registry queries, Google/GitHub API/raw/codeload/diff, ScienceDirect, browser, TLS bypass, account actions, messages or publication.

Inherited 429 MathDB and unavailable current proof registry remain HOLD. Parked AIM/Kourovka/EGRES/AIProofWatch, DMGT TLS, ProjectEuclid challenge, ResearchGate403 and OEIS A274199/internal403 routes were not retried. No negative novelty inference.

No complete proof, dependency audit, whole-body audit or successor-body clearance. All 50 literals reviewed individually; metadata full tags do not determine our complete-statement count. Primary restoration is not a new assignment. No substantial hypothesis merits separate delegation. Town checks are finite evidence only; source-supplied polynomial subclass results cannot be promoted to all n. Stability source has incomplete definitions and nonproof language; no repair counted.

One initial record display exceeded tool output bounds; statements were re-read in compact batches. This was an output truncation, not corpus loss. No guard failure or resource-limit change. No upstream verifier executed. No original or shared file changed. No mathematical PASS is implied by integrity verification.
''')
c=sum(x['complete_statement'] for x in out)
(L/'SUMMARY.md').write_text(f'''# Breadth screening

Screened all 50 assigned literal records from r613 queue-r614.json and reserved-ids-r614.json. Complete statements: {c}; all other rows retain separate incomplete, missing-definition or ambiguous-scope flags in dispositions.json. Baseline remains 6,283 reported literal reviews, not full technical corpus coverage. Root may reconcile these 50 disjoint additions; this worker edits no shared coverage.

Zero hypothesis briefs and zero credit. Three selected primary passages with nearby internal results read (370667,370733,372430); zero whole-body or full-dependency audits and zero successor/prior-body clearances. Exact town maximum-clique calculations at n=1..8,k=2..8 (56 parameter pairs) found no monotonicity violation; this supplies no all-parameter route. Polynomial source already contains an ellipse-bound subclass theorem, and the stability source leaves a critical definition unresolved.

Integrity checks independently cover the exact intake payload, direct original/copy pairs, all 20 original corpus chunks and eight frozen inputs against the r301 manifest, itself bound by r613. All three reservations are pairwise disjoint and avoid baseline/protected IDs. Literal statements and canonical JSON hashes are independently replayed. Flat references only; no copied historical tree or corpus.

Current registry, source scope and novelty remain HOLD. Access restrictions and inherited stopped routes retained. No Lean, manuscript, ledger or credit changes. Run ./verify.sh for read-only integrity checks under the fixed guard. Final receipt distinguishes integrity from scientific eligibility.
''')
print('built',len(out),'complete',c)
