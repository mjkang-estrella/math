import pathlib,json,hashlib,datetime,math,collections
P=pathlib.Path(__file__).parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r693'
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
def w(n,o):(P/n).write_text(json.dumps(o,ensure_ascii=False,indent=2)+'\n')
notes={}
for line in (P/'reviews.tsv').read_text().splitlines():
 ident,cl,reason,note=line.split('\t');notes[int(ident)]=(cl,reason,note)
rows=j(P/'literal-records.json');assert len(notes)==len(rows)==50
out=[]
for x in rows:
 r=x['record'];ident=r['mathdb_id'];cl,reason,note=notes[ident]
 out.append({'mathdb_id':ident,'chunk':x['chunk'],'line':x['line'],'statement_utf8':r['statement'],'statement_sha256':h(r['statement'].encode()),'canonical_record_sha256':h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()),'classification':cl,'classification_reason':reason,'quantifier_scope':reason,'technical_assessment':note,'final_disposition': 'EXCLUDE_CLASSICAL_ADAPTATION' if ident==319684 else 'EXCLUDE_KNOWN_PRIMARY_THEOREM' if ident==320327 else 'HOLD_SOURCE_SCOPE_OR_NO_FULL_ROUTE','complete_self_contained_statement':cl=='complete','accepted_credit':0,'current_registry_cleared':False,'source_url':r['source_url'],'source_evidence': 'selected_primary_passages_and_local_proof' if ident==320327 else 'selected_primary_passages' if ident in [319684,320415] else 'literal_corpus_only','full_dependency_audit':False,'successor_body_clearance':False})
w('dispositions.json',out);w('proposals.json',[])
# Small exact check of the residue construction; proof is separate from this check.
a={0:1,1:6,2:3,3:4};checks=[]
for n in range(4,101):
 u,v=(1,4) if n==5 else (a[n%4],n-a[n%4]);assert u>0 and v>0 and u+v==n
 for t in [u,v]:assert not any(k*k+l*l==t for k in range(1,math.isqrt(t)+1) for l in range(1,math.isqrt(t)+1))
 checks.append([n,u,v])
w('bounded-calculations.json',{'executed':'Exact integer check n=4..100, each representation and positive-square nonrepresentability independently enumerated','checks':checks,'proof':'For n mod4=0,1,2,3 choose a=1,6,3,4. For n>=4 except5, b=n-a is positive and congruent3 mod4, hence not a sum of two squares. The constants1,3,4,6 are not sums of two positive squares. At5 use1+4. This is a short classical adaptation, not a discovery proposal.','schur_check':'No computation or proof claimed; negative-real-zero product/PF route remains an unverified routine objection.'})
w('source-coverage.json',{'literal_reviews':50,'classifications':dict(collections.Counter(d['classification'] for d in out)),'primary':{'319684':'arXiv1003.3509v1 selected Section4.2 lines1569-1602; positive-integer convention line157; no whole-body or dependency audit','320415':'arXiv1009.4225v1 lines1-100 and255-340, including local proved row/column positivity and Section3 question; no whole-body or successor audit','320327':'arXiv1008.4749v1 lines1-155,506-535,778-806, question, Corollary18 and its proof, Theorem14 proof endpoint; not whole-body or full dependency audit'},'successors':'No successor body cleared; no substantial hypothesis investment or proposal. Known primary theorem already defeats320327.','registry':'Current proof registry unavailable, HOLD; no requests and no absence-of-hits inference','routing_rows':10000,'routing_is_review_coverage':False,'baseline_literal_reviews':8233,'potential_reconciled_literal_total':8283,'full_technical_corpus_coverage':False})
w('failures.json',{'new_http_failures':[],'stopped_routes_preserved':['MathDB429:zero requests','r578 inherited failures unchanged; bound historical failure references retained','r642 Gorenstein author PDF TLS','r684 two arXiv v2 HTTP404 fetches','OEIS A274199/internal HTTP403 r542','DOI10.1093/imrn/rnz305 academic.oup.com403 Cloudflare r618','AIM/Kourovka/EGRES/AIProofWatch parked','DMGT TLS','ProjectEuclid challenge','ResearchGate403','Google/GitHub APIs/raw/codeload/diff/ScienceDirect/browser/preview/TLS bypass prohibited'], 'limitations':['Initial combined record/context tool output was truncated; all50 statements subsequently reread in two bounded assigned-only excerpts. Administrative acceptance context reread in compact structured form.','No current registry availability; no novelty PASS.','338366 remains excluded with explicit text/figure reconstruction and unread-journal limitations; no new deductions about it.'],'resource_guard':'Fixed512MiB AS/groupRSS,CPU210s,wall230s; all Python under helper_guard; no raised/split limits','replacements':0})
counts=collections.Counter(d['classification'] for d in out)
(P/'SUMMARY.md').write_text(f'''# r694 breadth handback

Exactly 50 assigned literal records reviewed; no replacements. Classification: {dict(counts)}. Baseline8,233 is literal review coverage; root may reconcile to8,283. The10,000 routing rows are metadata only. No full-corpus or complete technical-audit claim.

Zero proposals and zero credit. 319684 has a complete elementary residue construction (executed check4..100); this short classical adaptation is excluded. 320327 is already established by Huh's primary Corollary18; selected proof passages were read, not the full dependency chain. 320415 retains a classical total-positivity objection without proof or successor-body clearance. Every other row has an individual scope and technical disposition in dispositions.json.

Three primary arXiv v1 PDFs fetched with generic headers; bytes bound before extraction and text derivatives bound before reading. Source coverage records exact selected passages. No whole-body, successor-body, full dependency or live registry clearance is claimed. No promising new full-scope mechanism survived screening, so no substantial hypothesis investment was made.

Intake exact payload and40 original/copy pairs checked independently without running upstream verify.py. All20 original corpus chunks and8 frozen inputs passed before mathematical reading; bindings are flat and no corpus/history copy was made. All150 reservations remain disjoint from8,233 covered IDs and protected IDs; Claude r628 and Sol r692 reservations unchanged. Required r304 exclusions and r363 Cayley decision retained; current adjudications retire338290/339564/372627 and park337963. Counts remain9 additional/39 total/next40.

No MathDB request; no stopped route retried. No new HTTP failure. Current registry unavailable remains HOLD. Earlier r578 failures, r642 TLS, r684 v2 404s, OEIS403 and OUP403 remain stopped. 338366 stays excluded with reconstruction/unread-journal limits. Initial oversized tool output truncated; all50 scientific literals were reread in two bounded excerpts. Integrity PASS is not mathematical or novelty PASS.

Run ./verify.sh for independent read-only verification. Manifest excludes only itself and final-verification-receipt.json. Receipt records manifest SHA256+size and bounded negative hash/size/extra-file tests.
''')
# Compact context inspection, no adjacent unassigned scientific text.
for name in ['accepted-exclusions.json','historical-dispositions.json']:
 o=j(L/'root-mathdb-accepted-exclusions-r304'/name)
 print(name, json.dumps(o,ensure_ascii=False)[:22000])
print('CLASSIFICATIONS',dict(counts))
