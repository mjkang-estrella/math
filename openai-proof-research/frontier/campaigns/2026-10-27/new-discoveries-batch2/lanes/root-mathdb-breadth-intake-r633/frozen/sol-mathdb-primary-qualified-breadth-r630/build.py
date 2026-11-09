from pathlib import Path
import json,hashlib,datetime
from fractions import Fraction
D=Path(__file__).resolve().parent;I=D.parent/'root-mathdb-breadth-intake-r629'
def load(p):return json.loads(p.read_text())
def dump(n,x):(D/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
reviews={}
for l in (D/'reviews.tsv').read_text().splitlines():
 i,c,s,r=l.split('\t');reviews[int(i)]=(c,s,r)
assert len(reviews)==50
sources={388181:['cooper'],388184:['cooper'],388232:['eremenko'],388251:['eremenko'],388666:['topp43'],388675:['topp60'],388682:['topp70','yaoyao'],388798:['kapovich','baker-riley'],388799:['kapovich','baker-riley']}
extra={388675:('PARK_NO_FULL_ROUTE','Primary TOPP60 entire short entry read: n=3 two-move result is already known; no n>=4 full-scope mechanism established. Bounded successor search returned this primary page; no absence-of-prior inference.'),388682:('HOLD_SCOPE_PRIOR','Primary TOPP70 recovers equally spaced cone definition and incoming shortest-edge pruning, then undirected distances. Li-Zhan ESA2016 Theorem2 proves YY_(2k) is a spanner for each k>=42; final proof combination read. This defeats a new existence-of-suitable-cone-count result; does not answer all integer cone counts. Full dependency audit and odd-cone successor body not read.'),388798:('HOLD_PRIOR_CONTEXT','Kapovich p18 Problem66 is a surface Kleinian representation question; preceding context and Remark27 identify a claimed Mj solution. Baker-Riley general subgroup obstruction cannot be substituted for this narrower representation. Claimed complete Mj body not read.'),388799:('REJECT_PUBLISHED_THEOREM_MATCH','Kapovich p18 Problem67 matches general hyperbolic-subgroup question. Baker-Riley author PDF dated August13,2013, Theorem1 gives hyperbolic G and rank3 free H with no Cannon-Thurston map. Read theorem, construction setup and final proof on pp6-7, including escaping H geodesics whose G geodesics pass through identity. Standard identification of equivariant boundary maps with inclusion extension via attracting fixed-point density is not independently audited here. Published theorem is a decisive screening prior objection, not a fresh proof or complete dependency audit.')}
out=[]
for x in load(D/'literal-records.json'):
 r=x['record'];i=r['mathdb_id'];c,s,n=reviews[i]
 if i in extra:s,z=extra[i];n+=' '+z
 out.append({'mathdb_id':i,'canonical_url':r['canonical_url'],'corpus_chunk':x['chunk'],'corpus_line':x['line'],'statement_utf8':r['statement'],'statement_utf8_sha256':hashlib.sha256(r['statement'].encode()).hexdigest(),'canonical_record_sha256':x['canonical_record_sha256'],'metadata_completeness_unmodified':r['statement_completeness'],'reviewed_scope':c,'disposition':s,'technical_review_quantifiers_and_obstruction':n,'source_name_literal':r['source_name'],'source_url_literal':r['source_url'],'source_passages_read':sources.get(i,[]),'primary_body_review':False,'whole_successor_body_read':False,'local_proof':False,'full_dependency_audit':False,'current_registry_cleared':False,'prior_cleared':False,'accepted_credit':0})
dump('dispositions.json',out);dump('proposals.json',[])
# Necessary area identity only: no packing certificate inferred.
tests=[]
for N in [1,2,3,10,100]:
 s=sum((Fraction(1,k*(k+1)) for k in range(1,N+1)),Fraction());assert s==Fraction(N,N+1)
 tests.append({'N':N,'area':str(s),'tail_area':str(Fraction(1,N+1))})
dump('bounded-checks.json',{'executed':'exact rational telescoping area checks; no packing or density search','checks':tests,'not_executed':['centroid controllability search','prime/persistence/reverse-add sweeps','Lean/formal proof'],'proof_limit':'Only necessary total-area bookkeeping; no full-scope certificate.'})
# Independent reservation checks.
cov=load(I/'coverage-delta.json');res=load(I/'active-breadth-reservations.json');seen=set();protected=set(load(I/'reserved-ids-r630.json')['protected_ids'])
assert len(cov)==6633
for r in res:
 s=set(r['ids']);assert len(s)==50 and not(s&seen) and not(s&set(map(int,cov))) and not(s&protected);seen|=s
assert set(reviews)==set(load(I/'reserved-ids-r630.json')['ids'])
prior={}
for name in ['accepted-exclusions.json','historical-dispositions.json']:
 p=D.parent/'root-mathdb-accepted-exclusions-r304'/name
 data=load(p);prior[name]={'top_level_keys':list(data) if isinstance(data,dict) else None,'literal_id_mentions':[i for i in reviews if str(i) in p.read_text()]}
dump('context-check.json',{'coverage_baseline':6633,'active_sets':3,'each_size':50,'pairwise_disjoint':True,'disjoint_coverage_and_protected':True,'focused_hypothesis':None,'accepted_counts':[9,39,40],'r304_check':prior,'r363':'DECISION.md bound/read; published equal-maximum Cayley witness excludes364119','r629':'338290/339564/372627 retired;337963 parked;338366 excluded with text/figure reconstruction and unread-journal limitations;338408 parked endpoint objection'})
dump('source-coverage.json',{'literal_record_reviews':50,'individual_dispositions':50,'hypothesis_briefs':0,'full_primary_bodies':0,'full_successor_bodies':0,'full_dependency_audits':0,'local_full_scope_proofs':0,'selected_primary_record_ids':list(sources),'whole_short_primary_entries':[388666,388675,388682],'successor_selected_proof_passages':[388682,388799],'registry':'unavailable HOLD; zero MathDB requests','routing_8000_credit':0})
print('Built',len(out),'dispositions; zero proposals; reservation checks passed')
