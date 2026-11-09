import json,pathlib,hashlib,collections
O=pathlib.Path(__file__).resolve().parent; L=O.parent
load=lambda p:json.loads(p.read_text())
def dump(n,x):(O/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
rows=load(O/'literal-records.json');a={}
for line in (O/'assessments.tsv').read_text().splitlines():
 i,c,r,q,d,t=line.split('\t');a[int(i)]=(c,r,q,d,t)
assert len(a)==50 and set(a)=={r['id'] for r in rows}
source_ids={'2510.23200':[371158,371159,371160],'2604.02475':[374014],'2603.02698':[373411],'2604.21187':[374345],'2601.06208':[372482]}
coverage=[{'arxiv_id':'2510.23200v1','ids':source_ids['2510.23200'],'passages_read':[[274,503],[1150,1187],[1479,1559],[2137,2210]],'scope':'Selected question/definition/theorem and Section5.4 proof sketch; not whole body. Theorem5.1 p>=5 scope only; hypergeometric machinery and all local lemmas not replayed. Higher-order CM definitions only partial.','source_internal_result':'Remark2.2; Theorem5.1; Theorem5.2','full_dependency_audit':False},
{'arxiv_id':'2604.02475v1','ids':[374014],'passages_read':[[210,310],[758,802]],'scope':'Exact Conjecture1.1/Theorem1.2, error-bound Theorem1.3 and entire Section3 proof. Section2 derivation not read or audited; finite checks reported by author not independently replayed.','source_internal_result':'Theorem1.2 exactly subsumes target; Theorem1.3 is explicit dependency.','full_dependency_audit':False},
{'arxiv_id':'2603.02698v1','ids':[373411],'passages_read':[[414,470],[1422,1524]],'scope':'Definitions, Conjecture1.9, Theorem1.10, all of Section3.2 including Lemmas3.1/3.2 and complete short proof. Not whole manuscript or external lemma source bodies.','source_internal_result':'Theorem1.10 exactly matches arbitrary-field/projective-dimension scope. Wedge independence proof covers the full stated parameters.','full_dependency_audit':False},
{'arxiv_id':'2604.21187v1','ids':[374345],'passages_read':[[205,275],[706,720]],'scope':'Definition of Ramsey-good/double saturation, Theorem1.1 and Conjecture2. Selected result/statement passages; no complete manuscript or Section3 proof audit.','source_internal_result':'Theorem1.1 addresses R(4,t), not this R(3,t) family; method similarity alone is no routine-subsumption bridge.','full_dependency_audit':False},
{'arxiv_id':'2601.06208v1','ids':[372482],'passages_read':[],'scope':'Keyword-selected lines on Conjecture1.3 and Section4.1 finite verification, not continuous primary-question passage or proof-body clearance. Literal map alone screened.','source_internal_result':'Finite verification through6.5 million is not a termination theorem.','full_dependency_audit':False}]
dump('source-coverage.json',{'sources':coverage,'whole_bodies_read':0,'current_registry':'HOLD unavailable; zero MathDB requests','closest_successor_bodies_cleared':False,'successor_limit':'Only five explicit v1 primary HTML bodies fetched; no latest-version or external-successor clearance. No promoted hypothesis or substantial proof investment.','search_matches_are_not_proof_clearance':True})
dis=[]
for x in rows:
 r=x['record'];c,reason,q,d,t=a[x['id']]
 primary=next((s for s in coverage if x['id'] in s['ids']),None)
 dis.append({'mathdb_id':x['id'],'title':r['title'],'classification':c,'classification_reason':reason,'literal_statement_utf8':r['statement'],'statement_utf8_sha256':hashlib.sha256(r['statement'].encode()).hexdigest(),'canonical_record_sha256':x['canonical_record_sha256'],'corpus_chunk':x['chunk'],'corpus_line':x['line'],'quantifier_scope':q,'disposition':d,'technical_assessment':t,'source_url_as_recorded':r['source_url'],'source_version_read':primary['arxiv_id'] if primary else None,'evidence':{'literal_record_read':True,'primary':primary['scope'] if primary else 'Not read; corpus statement only. Source existence and current status not independently asserted.','whole_source_body_read':False,'local_proof': 'Full source Section3.2 read' if x['id']==373411 else ('Source Section3 proof read, dependency Theorem1.3 unaudited' if x['id']==374014 else ('Source Section5.4 proof sketch read' if x['id']==371158 else 'No complete local proof read')),'full_dependency_clearance':False,'successor_clearance':False,'current_registry_clearance':False},'promotion':False,'credit':0})
dump('dispositions.json',dis);dump('proposals.json',[])
f=load(L/'sol-mathdb-primary-qualified-breadth-r714/failures.json');f['new_http_failures']=load(O/'fetch-failures.json');f['new_failed_checks']=[]
f['deviations']=['Initial combined literal/context display exceeded tool output budget; all fifty assigned statements subsequently read in bounded display ranges0:8,8:25,25:50. No unassigned literal statements were displayed.','Initial bound context display included more historical/admin-summary text than needed and truncated; recovered targeted adjudications, r363 decision and assignment-specific exclusions with context.py. No omitted material claimed read.','Five v1 primary bodies fetched; no external-successor or current registry clearance. Collatz primary only keyword-selected, not a complete primary-question/body review. No PDF operations.','Negative tests inject byte/size/name faults in the independent read-only verifier; no file or original mutation.']
f['adjudications']='r717 preserved: retire338290/339564/372627;park337963;338366 excluded with explicit text/figure reconstruction defects and unread-journal limitations; r363 Cayley364119 excluded. Reservations of Solr716 and held Clauder628 untouched.'
dump('failures.json',f)
counts=dict(collections.Counter(x['classification'] for x in dis))
summary=f'''# r718 independent breadth handback

Exactly 50/50 assigned literal records read and individually assessed; no replacements. Classification: {json.dumps(counts)}. Exact UTF8 statements, statement hashes, canonical record hashes and original corpus chunk/line are in dispositions.json and literal-records.json.

Zero hypothesis briefs, zero new full-scope proofs, zero credit. Baseline 8,833 remains the intake's literal-review count; this lane contributes fifty disjoint reported statement assessments for root reconciliation (potential 8,883), not full technical corpus coverage. The 10,000 routing rows remain metadata only. Counts remain 9 additional /39 total /next40.

Primary evidence: five versioned arXiv HTML sources retained and hashed before parsing; derivatives hashed before content reading. Three have selected theorem/proof passages: 373411 is exactly source Theorem1.10, with complete local wedge-independence proof read; 374014 is source Theorem1.2, with its concluding proof read but explicit-error dependency unaudited; 371158 is source Theorem5.1 for p>=5, with an explicitly incomplete hypergeometric proof sketch. The last does not clear p2/3 or the complete dependency chain. These give no new credit. 374105 and373763 only have literal reported known refutations, not independent proof-body clearance.

For374345 the primary Conjecture2 and exact double-saturation definitions were read. One executed t17/n75 check gives zero triangles and common-neighbor witnesses for all58 nonneighbors of vertex0; translation proves edge-addition saturation for that instance only. Independence upper bound, edge-deletion saturation and all-odd-t route remain absent. The source's R(4,t) theorem is not a bridge. No expanded sweep or hypothesis promotion.

Integrity checks: intake exact file set/hashes, all direct original/copy pairs, original r301 inventory manifest, all20 original corpus chunks and8 frozen inputs in place, flat original references, all three reservation sets versus8,833 covered and protected IDs, assignment exactness, and literal/canonical hashes. No upstream verifier executed. All helpers use the fixed512MiB AS/groupRSS,CPU210s,wall230s guard and single-thread environment. verify.sh runs the independent read-only verifier; final receipt records normal and bounded negative-test exits and exact manifest hash/size. Integrity PASS is not mathematics or novelty PASS.

Current registry unavailable => HOLD. Latest versions, external closest-successor bodies and full dependencies remain uncleared; no absence-of-hits inference. All stopped routes, including exact r578/r684 failures, r642 TLS, OEIS403 and OUP403, are preserved in failures.json without retry. Zero MathDB requests. No browser, git, shared/index/ledger/NEXT, manuscript, Lean, credit, sibling or upstream writes. Solr716 and held Clauder628 reservations preserved. No child agents.

Limits and display deviations are retained in failures.json. Final payload excludes only manifest.json and final-verification-receipt.json from its manifest.
'''
(O/'SUMMARY.md').write_text(summary)
print('built',len(dis),counts,'proposals',0)
