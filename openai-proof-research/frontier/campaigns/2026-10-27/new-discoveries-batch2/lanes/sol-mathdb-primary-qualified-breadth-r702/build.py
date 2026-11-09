import pathlib,json,hashlib,math,collections
from fractions import Fraction
D=pathlib.Path(__file__).parent;I=D.parent/'root-mathdb-breadth-intake-r701'
def load(p):return json.loads(p.read_text())
def write(n,x):(D/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
reviews={}
for line in (D/'reviews.tsv').read_text().splitlines():
 a=line.split('\t');assert len(a)==5;reviews[int(a[0])]=a[1:]
rows=load(D/'literal-records.json');assert len(reviews)==len(rows)==50
body={335749:{'primary':'335749.txt lines67-140: definitions and Conjecture2.2','successor':'335749-successor.txt lines20-345: Theorem2, Proposition1 and their proof bodies, basis change and sl2 determinant argument','whole_body_read':False,'dependency_audit':False,'bridge':'Put N=binomial(n,2), a_i=number of rank-i permutations, a_-1=0. Successor det is product_i((N-k-i)!/(k-i)!)^(a_i-a_(i-1)). Divide by (N-2k)!^a_k. Telescoping cancels i=k term and leaves product_i<k((N-k-i)/(k-i))^a_i. Weighted matrix products are transposes of U powers.'},336787:{'primary':'336787.txt lines50-87,132-198,344-415: Definition3, Conjecture6, Theorems7,9,17,23, Lemmas15,16,20-22 and selected proof bodies','successor':'Not needed to exclude a new proof of the assertion already proved in its own primary source; no global successor clearance','whole_body_read':False,'dependency_audit':False,'limits':'Lemmas18,19 interior induction, appendix near-modular tables and external Theorem7 exclusion proof not independently replayed.'},339244:{'primary':'339244.txt lines1438-1495,1560-1593: polynomial definition, Theorem6.1, Lemma6.2, Corollary6.3, Table3, ComputationalFact6.5 and Conjecture6.6','successor':'Not sought: literal k<=4 defect is already explicit in primary Table3; no claim to resolve k>=5','whole_body_read':False,'dependency_audit':False}}
out=[]
for e in rows:
 r=e['record'];id=r['mathdb_id'];c,reason,quant,assessment=reviews[id]
 disp='HOLD_SCOPE' if c!='complete' else 'HOLD_NO_FULL_SCOPE_ROUTE'
 if id in [335396,336515,337349]:disp='NO_PROPOSAL_LITERAL_REPORTS_KNOWN_THEOREM_BODY_UNCHECKED'
 if id in [335749,336787]:disp='NO_PROPOSAL_PRIMARY_OR_SUCCESSOR_THEOREM'
 if id in [335027,335480,336861,339244]:disp='NO_CREDIT_DOMAIN_OR_WORDING_OBJECTION'
 out.append({'mathdb_id':id,'chunk':e['chunk'],'line':e['line'],'statement_utf8':r['statement'],'statement_sha256':hashlib.sha256(r['statement'].encode()).hexdigest(),'canonical_record_sha256':e['canonical_sha256'],'classification':c,'classification_reason':reason,'quantifiers':quant,'technical_assessment':assessment,'disposition':disp,'source_url_from_record':r['source_url'],'source_coverage':body.get(id,{'primary':'literal record only; primary body not fetched/read','successor':'unread','whole_body_read':False,'dependency_audit':False}),'registry':'HOLD unavailable; zero direct MathDB requests','novelty_cleared':False,'credit':0})
write('dispositions.json',out);write('proposals.json',[])
counts=collections.Counter(e['classification'] for e in out)
write('coverage-accounting.json',{'baseline_literal_reviews':8433,'assigned_literal_reviews':50,'provisional_total_if_root_integrates_only_this_lane':8483,'routing_rows_metadata_only':10000,'classification_counts':dict(counts),'replacements':0,'proposals':0,'current_registry_cleared':False,'credit_added':0,'campaign_counts_unchanged':'9 additional /39 total /next40'})
checks=[]
for n in range(2,9):
 N=n*(n-1)//2;a=[1]
 for j in range(1,n+1):
  b=[0]*(len(a)+j-1)
  for i,v in enumerate(a):
   for s in range(j):b[i+s]+=v
  a=b
 for k in range((N+1)//2):
  lhs=Fraction(1)
  for i in range(k+1):lhs*=Fraction(math.factorial(N-k-i),math.factorial(k-i))**(a[i]-(a[i-1] if i else 0))
  lhs/=math.factorial(N-2*k)**a[k];rhs=Fraction(1)
  for i in range(k):rhs*=Fraction(N-k-i,k-i)**a[i]
  assert lhs==rhs;checks.append([n,k])
# Explicit coefficient products for the four domain-defect cases, no factoring library.
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return c
ph6=[1,-1,1];ph10=[1,-1,1,-1,1];ph12=[1,0,-1,0,1];facts=[ph6,ph10,mul(ph6,ph12),mul(ph10,ph12)]
for k,f in enumerate(facts,1):
 v=[0]*(2*k+1)
 for j,x in [(0,1),(1,-1),(k,1),(2*k-1,-1),(2*k,1)]:v[j]+=x
 assert v==f
write('bounded-calculations.json',{'executed':{'determinant_normalization_bridge':{'pairs':checks,'all_equal_exact_rationals':True,'not_a_matrix_determinant_recomputation':True},'339244':{'k':list(range(1,5)),'coefficient_products':facts,'quotient':1,'credit':0}},'analytic_observations':{'335480':'Constant map f=0 on [0,1] is globally nonexpanding. At x=0, for every R>0 choose y=min(R/2,1/2)>0; image distance0 differs from y. This is a wording defect only.','335027':'h=0 makes Y^2=Z^3 singular at (0,0), all t.'},'not_executed':'No unbounded proof, independent formal replay, current registry check or large enumeration.'})
write('source-coverage.json',{'individual_primary_passage_reviews':3,'downloaded_pdfs':4,'text_derivatives':4,'per_id':body,'global':'All50 literal statements reviewed; no whole source body or full dependency or registry clearance. Remaining47 primary bodies unread.'})
old=load(I/'frozen/sol-mathdb-primary-qualified-breadth-r698/failures.json')
write('failures.json',{'inherited':old,'new_http_failures':[],'deviations':['First combined literal/context print truncated; all50 reread using assigned-only ranges0:10,10:30,30:50.','Semantic disjointness check completed after initial literal reading although hashes of all inputs and all28 inventory entries were bound and checked before scientific reading. Earlier commentary disjointness assertion preceded the explicit semantic script; actual check passes.','Initial web searches had site:arxiv.org in query but no domains filter; search provider returned MathDB and ResearchGate indexed snippets plus other sites. No direct request/open to either site, no snippet relied upon as proof; required zero MathDB requests interpreted as zero direct endpoint requests. This index exposure is disclosed.','Administrative context print emitted oversized ledger/history summaries and truncated; no unassigned scientific review credit.','Draft two-point constant-map observation was wrong because discrete maps are locally isometric; corrected to compact interval before final dispositions. No proposal based on error.'],'stopped_routes_preserved':old['stopped_routes_preserved'],'registry':'HOLD; no absence-of-hits inference','guard':'All Python/helper computations fixed helper_guard.py:512MiB AS/groupRSS CPU210 wall230; no raising or cap evasion','338366':'Excluded with explicit text/figure reconstruction and unread-journal limitations unchanged.','actions':'No children, git, shared edits, Lean, manuscript, credit, contact or publication.'})
(D/'SUMMARY.md').write_text('''# r702 breadth screening\n\nExactly 50 assigned literal records reviewed, no replacements, zero proposals and zero credit. Classification counts: '''+str(dict(counts))+'''. The baseline remains 8,433 reported literal reviews; 10,000 routing rows are metadata, not coverage. Integration of this lane alone would yield 8,483; sibling reservations remain untouched. Campaign counts remain 9 additional /39 total /next40.\n\nIndependent integrity checks cover the intake exact payload and all direct original/copy pairs, all20 original r301 chunks and all8 frozen inputs, the bound inventory manifest, assignment/reservation, coverage and pairwise/protected disjointness. All scientific reads followed the 28 inventory checks. Semantic reservation checking was later than first literal reading; this and oversized/truncated early prints are disclosed in failures.json. No upstream verifier executed.\n\n335749 is defeated for discovery by Hamaker–Pechenik–Speyer–Weigandt arXiv1812.00321v1 Theorem2, with actual proof bodies read and exact normalization bridge checked. 336787 is already addressed by its own primary arXiv1708.01849v1 Theorems7,9,23; selected proof bodies read, full dependencies not replayed. 339244 has k<=4 quotient1 already explicit in primary arXiv1805.05207v1 Table3: a domain defect, no credit. These are three primary-passage reviews, not whole-body or dependency clearance. The remaining47 primary bodies are unread.\n\nEvery disposition retains exact UTF8 statement, corpus chunk/line, canonical record SHA256, independent scope classification/reason, quantifiers and individual technical obstruction. No complete new full-scope mechanism survived. Finite certificates for instances, known theorems and wording repairs were not promoted. Primary PDF bytes were hashed before extraction and derivatives bound before search/read. No PDF visual review.\n\nCurrent proof registry remains unavailable/HOLD. Four versioned arXiv PDFs fetched successfully with generic headers. Web search returned unrequested indexed MathDB/ResearchGate snippets despite site terms; no direct request/open to those sites, no use as proof. All inherited stopped routes remain parked, including r578 failures, r642 TLS and both r684 v2 404s. See failures.json for exact inherited evidence and deviations. Integrity PASS is neither mathematical nor novelty PASS.\n\nRun ./verify.sh for independent read-only verification; final-verification-receipt.json binds manifest.json. No shared files, reservations, Lean, manuscripts, indexes, ledgers or credit changed.\n''')
print(dict(counts),len(checks))
