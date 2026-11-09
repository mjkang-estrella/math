import pathlib,json,hashlib,collections,datetime,itertools
O=pathlib.Path(__file__).resolve().parent
rows={int(a):[b,c,d] for a,b,c,d in (line.rstrip('\n').split('\t') for line in (O/'reviews.tsv').open())};assert len(rows)==50
out=[]
primary={394996:('ems1795.txt',[20],'Printed p688: unconditional target; ERH result and a remaining prime-power/Pratt-tree obstruction. No proof body of Ford-Luca read.'),395017:('ems1961.txt',[10,11],'Printed pp806-807: divisor antichain passage, weighted probability context and Sperner discussion. Whole report not read.'),395102:('ems1973.txt',[7],'Printed p1543: explicitly distinguishes length from bit length; report dependency only.'),395103:('ems1973.txt',[7,8],'Printed pp1543-1544: Corollary E explicitly assumes faithful; next conjecture prints the unqualified statement. No corrected universal assertion adopted.'),395106:('ems1973.txt',[12,13,14],'Printed pp1548-1550: Theorem3 says Ore holds in general; proof strategy and computational base discussed, full dependency paper not read.'),395111:('ems1973.txt',[24],'Printed p1560: reports affirmative odd-prime algebra-group result; typesetting of orbit equality is unreliable; no proof body audited.'),395120:('ems2040.txt',[18,19],'Printed pp1620-1621: counting function explicitly counts active supports; Theorem1 and its entire short additive proof read.')}
for w in json.loads((O/'literal-records.json').read_text()):
 r=w['record'];a=r['mathdb_id'];cl,reason,assessment=rows[a]
 d={'mathdb_id':a,'canonical_url':r['canonical_url'],'title':r['title'],'statement_utf8':r['statement'],'statement_sha256':hashlib.sha256(r['statement'].encode()).hexdigest(),'canonical_record_sha256':w['canonical_record_sha256'],'corpus_chunk':w['chunk'],'corpus_line':w['line'],'classification':cl,'classification_reason_and_quantifiers':reason,'technical_assessment':assessment,'disposition':'HOLD_NO_FULL_SCOPE_ROUTE' if cl=='complete' else 'HOLD_LITERAL_SCOPE','accepted_credit':0,'primary_source_url':r['source_url'],'primary_passage':None,'whole_body_read':False,'local_proof_established':False,'full_dependency_audit':False,'successor_body_clearance':False,'current_registry':'HOLD unavailable; zero MathDB requests','novelty_cleared':False}
 if a in primary:
  f,pages,coverage=primary[a];d['primary_passage']={'file':f,'pdf_pages':pages,'coverage':coverage,'version':'publisher 2008 report'}
 if a in [395017,395106,395120]:d['disposition']='EXCLUDE_CLASSICAL_OR_SOURCE_PROVED';d['local_proof_established']=a==395120
 if a==395111:d['disposition']='HOLD_REPORTED_KNOWN_RESULT_BODY_UNAUDITED'
 if a==395103:d['disposition']='EXCLUDE_CLASSICAL_MISSING_SCOPE_OBSTRUCTION'
 if a==394996:d['technical_assessment']+=' Actual printed p688 explicitly retains an enormous-effective-threshold gap in the unconditional route; stop rather than a finite sweep.'
 out.append(d)
(O/'dispositions.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n');(O/'proposals.json').write_text('[]\n')
coverage={'literal_reviews':50,'baseline_reported_literal_reviews':7033,'potential_reconciled_total':7083,'not_shared_coverage_update':True,'classifications':dict(collections.Counter(d['classification'] for d in out)),'primary_passage_records':sorted(primary),'primary_report_files':4,'whole_bodies_read':0,'full_dependencies_audited':0,'successor_bodies_read':0,'registry_cleared':False,'proposals':0,'accepted_credit':0,'source_passage_notes':{str(a):dict(zip(['file','pdf_pages','coverage'],v)) for a,v in primary.items()}}
(O/'source-coverage.json').write_text(json.dumps(coverage,indent=2)+'\n')
checks={'executed':[{'id':395162,'operation':'3*17-7*7','result':3*17-7*7,'meaning':'single prime-entry determinant witness; not infinitude'},{'id':395017,'operation':'exact rank coefficients of chains of lengths 2,3,4','coefficients':[sum(sum(t)==j for t in itertools.product(range(2),range(3),range(4))) for j in range(7)],'meaning':'parameter sanity check only; classical SCD bridge is the substantive exclusion'}],'not_executed':['No finite sweep for Carmichael lambda','No H2 cochain computation; classical elementary-abelian cohomology obstruction is a theoretical observation','No Lean or manuscript work']}
(O/'bounded-checks.json').write_text(json.dumps(checks,indent=2)+'\n')
failures={'new_access_failures':[],'parked_untouched':['MathDB429 and current registry','r642 author Gorenstein TLS','AIM/Kourovka/EGRES/AIProofWatch','DMGT TLS','ProjectEuclid challenge','ResearchGate403','OEIS A274199/internal403 r542','DOI10.1093/imrn/rnz305 academic.oup.com403 r618'],'stopped_routes':['No promising full-scope original mechanism survived; no successor fishing or parameter sweeps'],'process_deviations':['An initial display of intake manifest/bindings was truncated; verified complete bytes and then used bounded structural displays. First scientific bulk display truncated; separately reread first16 literal rows. All50 literals ultimately displayed/read.','Primary context page display included neighboring report material; no unrelated MathDB literal was decoded for review.'],'limits':['No live registry clearance','No whole-report or full dependency audit','No novelty PASS from source metadata, search results, integrity or open labels']}
(O/'failures.json').write_text(json.dumps(failures,indent=2)+'\n')
flat=json.loads((O/'flat-bindings.json').read_text());
for e in json.loads((O/'source-provenance.json').read_text()):
 if 'path' in e:
  p=O/e['path'];b=p.read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256']
(O/'SUMMARY.md').write_text('''# r646 breadth handback

Exactly 50 assigned literal records screened independently; no replacement rows, no hypotheses proposed, no discovery credit. Baseline remains 7,033 reported literal reviews; this lane offers 50 additional reviews for root reconciliation (potential 7,083), without claiming technical coverage of the entire corpus. Counts remain 9 additional / 39 total / next 40. Claude r628 remains held and uncounted; r644 untouched.

All intake exact payloads and 87 direct original/copy pairs verified without upstream verifier execution. All 20 original r301 corpus chunks and eight frozen inputs checked in place against its bound inventory. Three reservations disjoint from baseline and protected IDs. Flat references only; no corpus or historical tree copies.

Classification totals: '''+json.dumps(coverage['classifications'])+'''. Each disposition preserves the exact UTF8 literal, canonical JSON record hash, statement hash and original chunk/line, plus individual scope and technical reasons. Complete means self-contained formulation, not proved or novel.

Four 2008 publisher reports fetched with generic headers; PDF bytes bound before extraction, text derivatives bound before searches. Selected passages read for seven records, no whole-body/dependency or successor-body clearance. Ore's report states the full theorem with a proof strategy; the Euler-target theorem includes its entire short proof. The divisor-antichain target is a classical product-of-chains application. Missing-scope cohomology, percolation endpoints and empty Allen-Cahn level sets cannot earn credit. Carmichael's report leaves a substantial unconditional prime-chain obstruction; no finite sweep justified. No substantial original full-scope route survived to warrant a proposal or further successor search.

Current registry remains unavailable and HOLD. All inherited stopped routes remain untouched, including Gorenstein TLS, OEIS403 and OUP403. 338366 remains excluded with text/figure reconstruction and unread-journal caveats; 338408 remains parked. Other current adjudications preserved.

See dispositions.json, source-coverage.json, source-provenance.json, bounded-checks.json and failures.json for exact limits. verify.sh runs a read-only independent verifier under the fixed guard. Integrity PASS is not mathematical acceptance or novelty PASS. No shared coverage, ledger, Lean, manuscript, git or external mutation.
''')
print(coverage['classifications'])
