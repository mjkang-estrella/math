import pathlib,json,hashlib,collections,datetime
from fractions import Fraction
D=pathlib.Path(__file__).resolve().parent;L=D.parent;I=L/'root-mathdb-breadth-intake-r649'
def put(n,x):(D/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
reviews={}
for line in (D/'reviews.tsv').read_text().splitlines():
 i,c,r,t=line.split('\t');reviews[int(i)]=(c,r,t)
rows=json.loads((D/'literal-records.json').read_text());assert len(reviews)==len(rows)==50
out=[]
for x in rows:
 r=x['record'];i=r['mathdb_id'];c,reason,technical=reviews[i]
 if i==396003:technical='Cited primary p2455 Question1 is immediately answered YES by Proposition1: even some induced f_m isomorphism implies f isomorphism. Exact rendered page51 inspected after binding. No proof of Proposition1 is supplied on that page; public statement defeats a new proposal, without claiming dependency audit.'
 if i==396076:technical=technical.replace('Theorem1','Theorem3');technical+=' The original OWR p2807 itself states Theorem1 |K|>=q^n/n!. Dvir section1.1 supplies the full-scale polynomial proof; no worldwide novelty claim or independent dependency replay.'
 if i in [395713,396011]:technical+=' The read Theorem1.1 is stated for divisors M; reduction from arbitrary ideals has not been independently sourced here. Retain HOLD on that bridge, rather than claiming complete theorem-body clearance. Returned PDF bears v1 header but internal date November27,2024; exact bytes pinned, chronology not cleared.'
 if i==395743:technical+=' OWR p1237 explicitly says Theorem1 resolves the intended slowly-growing-factor problem, with density (1-epsilon_k)2^k ln(k)/k. Full algorithm/probability proof is not in the selected passage and was not audited.'
 out.append({'mathdb_id':i,'chunk':x['chunk'],'line':x['line'],'statement':r['statement'],'statement_utf8_sha256':hashlib.sha256(r['statement'].encode()).hexdigest(),'canonical_record_sha256':x['canonical_record_sha256'],'source_url':r['source_url'],'source_name':r['source_name'],'quantifier_scope':r['statement'],'completeness_classification':c,'completeness_reason':reason,'technical_disposition':technical,'disposition':'EXCLUDE_PUBLISHED_STATEMENT' if i in [396003,396076] else 'HOLD_OR_PARK','accepted_credit':0,'current_registry_cleared':False,'whole_primary_body_read':False,'full_dependency_audit':False,'evidence_level':'selected_primary_passage_and_local_successor_proof' if i==396076 else 'selected_primary_passage' if i in [396003,395743] else 'selected_successor_theorem_and_local_proof' if i in [395713,396011] else 'literal_statement_only'})
put('dispositions.json',out);put('proposals.json',[])
checks=[]
for k in range(2,9):
 z=(1-Fraction(1,2**k))**(k*2**k);assert 2*z<1;checks.append({'k':k,'clauses_per_variable':k*2**k,'exact_first_moment_factor_below_one':2*z<1})
put('bounded-checks.json',{'executed':checks,'interpretation':'For fixed k and omega(k)=k^2, E[number satisfying assignments]=(2*(1-2^-k)^(k*2^k))^n tends to zero. General proof uses 1-x<=exp(-x), giving factor<=2exp(-k)<1 for k>=1. Quantifier/wording issue only; zero credit. No source problem is promoted.'})
spec=[('ems4086.txt',2405,2437,[396003]),('ems3473.txt',528,578,[395743]),('ems4135.txt',863,896,[396076]),('dvir.txt',85,115,[396076]),('acc.txt',39,70,[395713,396011]),('acc.txt',1312,1334,[395713,396011])]
passages=[]
for name,a,b,ids in spec:
 text=(D/name).read_text().splitlines();passages.append({'file':name,'lines':[a,b],'ids':ids,'text':'\n'.join(text[a-1:b])})
put('selected-passages.json',passages)
put('source-coverage.json',{'literal_records':50,'selected_original_primary_ids':[395743,396003,396076],'selected_successor_ids':[395713,396011,396076],'whole_primary_bodies':0,'full_dependency_audits':0,'local_proof_coverage':{'dvir':'section1.1 Theorem3 proof read, not entire paper dependency audit','acc':'Theorem1.1 and section9 proof read; Theorem1.5 dependencies and ideal-to-divisor bridge not audited','jet':'Proposition1 statement adjacent to question, proof not supplied'},'visuals':[{'file':'jet-primary-page.png','pdf_page':51,'printed_page':2455,'binding':'image-binding.json','viewed_after_binding':True}],'registry':'HOLD unavailable; zero MathDB requests; no absence-of-hits inference','metadata_only_prior_risks':'Other prior suspicions explicitly remain HOLD; no proof-body clearance from titles or abstracts.'})
put('failures.json',{'new_access_failures':[],'new_computation_failures':[],'inherited_stopped_routes':['MathDB429','AIM/Kourovka/EGRES/AIProofWatch parked','DMGT TLS','ProjectEuclid challenge','ResearchGate403','OEIS A274199/internal403 r542','academic.oup.com DOI10.1093/imrn/rnz305 Cloudflare403 r618','author Gorenstein PDF TLS r642'],'registry':'unavailable HOLD','deviations':['Initial raw record output exceeded tool display budget; corrected by a compact statement-only display of every assigned row. No omitted record was replaced.'],'338366':'excluded with published-object text/figure reconstruction caveats and unread-journal limitation; unchanged','338408':'parked unchanged','access':'No MathDB, Google, GitHub, ScienceDirect, browser, TLS bypass, contact or publication requests; all direct HTTP uses generic Python-urllib/3 header.'})
counts=collections.Counter(x['completeness_classification'] for x in out)
put('context-check.json',{'baseline':7133,'counts':{'additional':9,'total':39,'next':40},'classification_counts':dict(counts),'r304':'accepted families and historical administrative context loaded; no assigned id matches a structured mathdb_id exclusion','r363':'364119 published Cayley witness excluded; preserved','r649':'338290/339564/372627 retired;337963 parked;338366 exclusion and338408 park retained','no_shared_writes':True,'scientific_acceptance':False})
print(dict(counts))
