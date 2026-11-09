import pathlib,json,hashlib,collections,datetime
P=pathlib.Path(__file__).resolve().parent;L=P.parent
j=lambda p:json.loads(p.read_text())
h=lambda b:hashlib.sha256(b).hexdigest()
def write(n,x):(P/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
# Bind required ledger/admin context already recorded, then inspect structurally.
ledger=j(L.parent/'ledger.json');prior=j(L.parent/'prior-campaign-context.json')
exc=j(L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json');hist=j(L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json');decision=(L/'root-mathdb-cayley-review-intake-r363/DECISION.md').read_text()
write('context-check.json',{'ledger_read':True,'prior_context_read':True,'accepted_family_count':exc['accepted_family_count'],'historical_entries_read':len(hist['previous_excluded']),'r363_decision_read':True,'r641_adjudications_read':True,'authority':'r641 baseline 6933 literal reviews, not full technical corpus coverage; 9 additional /39 total /next40','excluded_338366':'Published object reconstructed modulo two text/figure defects; journal bodies unread; no explicitly named prior refutation established. Zero credit.','338408':'parked endpoint correction objection','338290_339564_372627':'retired per current adjudications','337963':'parked; source/prior substantive HOLD'})
rows={}
for line in (P/'reviews.tsv').read_text().splitlines():
 i,category,quantifiers,note=line.split('\t');rows[int(i)]={'independent_scope_classification':category,'quantifiers':quantifiers,'technical_disposition':note}
assert len(rows)==50
# Select exact relevant sections only; omit participant rosters and unrelated search hits.
spec=[('ems1190','Question. Are all Artin',-1600,3300),('ems1190','Strongly exceptional sequences of line bundles on toric varieties',0,11000),('ems1274','Theorem 4. The Tame',-1200,1800),('ems1386','Uniformly cross intersecting families',0,10000),('ems1452','6, 21, 4',-900,3300),('ems1453','Isomorphism of Complete Local Noetherian Rings and Strong',0,2100),('ems1453','Conjecture 3. Each group',-800,1700),('ems1394','Theorem [8, 10]',-2200,1700),('hille-perling-v1','Theorem 4.1:',0,4400),('powers-v1','Theorem 1 Let q',-600,2400)]
passages=[]
for name,term,before,after in spec:
 s=(P/(name+'.txt')).read_text();k=s.find(term,12000 if name=='ems1190' and term.startswith('Strongly') else 0)
 if k<0:continue
 a=max(0,k+before);b=min(len(s),k+after)
 z=s[a:b];z=z.split('Participants')[0];z=z.split('Reporter:')[0]
 passages.append({'file':name+'.txt','start_utf8_character':a,'end_utf8_character':a+len(z),'passage':z})
write('selected-passages.json',passages)
updates={393845:('RETIRE_SOURCE_INTERNAL_ANSWER','ems1190.txt','Printed p470: question followed by Yoshino six-dimensional algebra K[x,y,z]/(x^2,yz,y^2-xz,z^2-yx), using failure of CM right approximation and preceding lemma. Actual local answer passage read; Yoshino proof dependency unread.'),393852:('RETIRE_PUBLISHED_COUNTEREXAMPLE','hille-perling-v1.txt','arXiv math/0602258v1 Theorem4.1 and full local exclusion proof read; F2 blown up three times gives rank7 smooth complete toric surface with no length7 strong line sequence. Earlier cohomology classification/table not independently replayed; primary report cites same counterexample. No claim that rank alone implies categorical fullness.'),393973:('RETIRE_PUBLISHED_THEOREM','powers-v1.txt','arXiv0909.4639v1 Theorem1 and Corollary1 explicitly prove all finitely generated profinite groups and q. Selected theorem/corollary body; finite-group proof dependencies not audited.'),393992:('RETIRE_SOURCE_STATED_THEOREM','ems1274.txt','Printed p1520 Definition3 and Theorem4 assert exactly the equivalence and cite Hajir-Maire; dependency theorem bodies unread.'),394264:('RETIRE_SOURCE_STATED_THEOREM','ems1394.txt','Printed p3333 defines virtual hyperbolicity and states exact N>=4 existence theorem [8,10]; cited construction bodies unread.'),394296:('RETIRE_KNOWN_NONEXISTENCE_REPROOF','ems1452.txt','Printed pp56-57 explicitly reports prior computer nonexistence proof for (6,21,4), and outlines conceptual reduction using quadratic composition. A new explanatory proof is ineligible under assignment; earlier cited proof not audited.'),394210:('PARK_NO_FULL_SCOPE_ROUTE','ems1386.txt','Printed pp2919-2920 define exact intersections, prove/report sufficiently-large-ell bound, and explicitly ask all ell. Cases ell0,1 already known internally. Executed exhaustive family check n<=4: no obstruction. Does not imply all-n for remaining ell; no successor body cleared.'),394321:('PARK_NO_FULL_SCOPE_ROUTE','ems1453.txt','Printed p106: general rings have Gabber counterexamples but explicitly not domains; positive algebraic-residue-field case also given. Neither settles literal domain question. Incompatible truncation isomorphisms block naive inverse limit.'),394334:('PARK_NO_FULL_SCOPE_ROUTE','ems1453.txt','Printed pp132-133 Conjecture3 and Proposition4 read: rank2 non-solvability forces finite/infinite centralizer contrast. Proposition is partial, not a proof of solvability; no direct contradiction established.')}
ds=[]
for f in j(P/'literal-records.json'):
 r=f['record'];i=r['mathdb_id'];d={'mathdb_id':i,'corpus_chunk':f['corpus_chunk'],'corpus_line':f['corpus_line'],'statement_utf8':r['statement'],'statement_utf8_sha256':h(r['statement'].encode()),'canonical_record_sha256':h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()),'source_url':r['source_url'],'record_references':r['references'],**rows[i],'literal_review_complete':True,'accepted_credit':0,'current_registry_cleared':False,'whole_body_review':False,'full_dependency_audit':False,'prior_cleared':False,'disposition':'HOLD_INCOMPLETE' if rows[i]['independent_scope_classification']=='incomplete' else 'PARK_NO_BOUNDED_ROUTE','source_evidence':{'level':'literal_record_only','local_proof_read':False}}
 if i in updates:
  status,file,note=updates[i];d.update(disposition=status);d['source_evidence']={'level':'selected_primary_or_successor_passage','file':file,'assessment':note,'local_proof_read':i==393852}
 ds.append(d)
write('dispositions.json',ds);write('proposals.json',[])
c=collections.Counter(d['independent_scope_classification'] for d in ds)
write('source-coverage.json',{'literal_records':50,'independent_scope_categories':dict(c),'selected_question_theorem_or_answer_passage_records':len(updates),'literal_only_records':50-len(updates),'whole_bodies':0,'full_dependency_audits':0,'selected_local_prior_proofs':1,'proposals':0,'credit':0,'registry':'Unavailable per assignment; HOLD, not searched or inferred absent','uncredited_routing_metadata_rows':8000,'primary_report_pages':['OWR2006/08 pp469-470,489-491','OWR2006/25 pp1467-1468,1520','OWR2006/48 pp2919-2920','OWR2007/01 pp56-57','OWR2007/02 pp106,132-133','OWR2006/56 pp3332-3334'],'limits':'Downloaded entire reports but read only selected passages; full report text extraction is not body review.'})
write('source-provenance.json',{'fetches':j(P/'fetch-provenance.json'),'all_downloads_and_derivatives_bound_before_reading':True,'search_leads_only':[{'url':'https://arxiv.org/abs/math/0602258','role':'Located actual versioned PDF, theorem read'},{'url':'https://arxiv.org/abs/0909.4639','role':'Located actual versioned PDF, theorem/corollary read'},{'url':'https://myweb.uoi.gr/abeligia/vGorenstein_final.pdf','role':'TLS failure; not read, no retry'}],'version_limits':'OWR published report versions at exact EMS download routes; arXiv v1 pinned; journal counterparts of successor PDFs unread.'})
(P/'failures.md').write_text('''# Limits and stopped routes

No MathDB requests; existing HTTP429 HOLD unchanged. No Google/GitHub API/raw/codeload/diff, ScienceDirect, browser, preview, TLS bypass, accounts, contact or publication operations.

Author Gorenstein PDF failed certificate verification. Stopped without retry or alternate route. Primary OWR report independently already supplies an answer. First PDF link parser found no .pdf suffix: no HTTP failure; corrected parser used explicit citation_pdf_url once. No blocked endpoint was retried.

Initial administrative display was excessively broad and truncated; no mathematical conclusion used its omitted material. Exact intake and direct pairs were subsequently independently checked before corpus content. Selected-passages search initially included table-of-contents/unrelated hits and public participant-list text; final curated passages omit these. No private data were sent outbound. PDF contact rosters are intrinsic public source bytes, not external communications. All helpers including administrative snippets ran under unchanged fixed guard; no resource-limit failures.

Current proof registry unavailable: HOLD. Primary local report answers are not full dependency audits. TLS-failed author body, journal successor bodies and most external prior bodies remain unread. Search snippets used only as routing leads. No absence-of-hits inference.

Retain parked AIM/Kourovka/EGRES/AIProofWatch, DMGT TLS, ProjectEuclid challenge, ResearchGate403, OEIS A274199/internal403, DOI10.1093/imrn/rnz305 academic.oup.com403 challenge; no requests/retries to these routes. 338366 excluded modulo text/figure reconstruction defects and unread journal bodies;338408 parked.338290/339564/372627 retired;337963 parked.

No full-scope new candidate survived screening. 394210 finite checks are instances only; 394321 inverse-limit shortcut stopped at compatibility; 394296 is already-known nonexistence. No Lean/manuscript/credit changes.
''')
(P/'SUMMARY.md').write_text(f'''# Breadth screening r642

Reviewed exactly the 50 reserved literal records, retaining every incomplete row and making no replacements. Independent mathematical scope: {dict(c)}. Literal review is not mathematical completeness, primary-body clearance, or novelty PASS.

Nine records received selected question/theorem/answer passage checking; 41 remain literal-only. One prior local proof read (Hille-Perling Theorem4.1); zero whole-body or full-dependency audits. Old answers/theorems exclude 393845,393852,393973,393992,394264;394296 requests an explanatory reproof of known nonexistence and is uncredited. Remaining records stay HOLD/PARK with individual quantifiers and reasons in dispositions.json. No proposals and zero credit.

For394210 the primary uses exact intersection cardinality. Executed exhaustive Boolean-family optimization for n=1..4,ell=0..n (14 parameter pairs): all satisfy the bound; no general proof or novelty implied. For394321 the primary explicitly distinguishes Gabber's non-domain counterexamples from the domain problem; incompatible finite-level isomorphisms obstruct the naive inverse-limit argument. No substantial hypothesis is recommended.

Integrity checks bind the exact r641 payload, its original/copy pairs, original r301 inventory manifest, all20 original corpus chunks and8 frozen inputs in place, reservations, literal UTF8 and canonical record hashes. Three sets of50 are disjoint from baseline6933 and protected IDs. No corpus/tree copying. Routing8000 metadata rows uncredited. Baseline6933 is reported literal reviews, not full technical coverage; campaign9additional/39total/next40 unchanged. r640 continues and Claude r628 remains HELD untouched.

TLS failure on author Gorenstein PDF stopped; no bypass/retry. All named access holds retained. Current registry unavailable and all global novelty gates HOLD. See failures.md for parser/output-selection deviations and evidence limits. Integrity PASS does not imply math/novelty PASS.

Run ./verify.sh for independent read-only verification under the fixed guard. Manifest covers verifier and all payloads, excluding only itself and final-verification-receipt.json. Final receipt records exact manifest hash/size and bounded hash/size/extra-file rejection tests.
''')
print(dict(c))
