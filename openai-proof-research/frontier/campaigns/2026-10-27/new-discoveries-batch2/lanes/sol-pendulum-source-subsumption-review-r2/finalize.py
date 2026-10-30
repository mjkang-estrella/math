import pathlib,json,hashlib,datetime,re
O=pathlib.Path(__file__).parent; B=O.parent.parent
def digest(p):
 d=p.read_bytes();return {'bytes':len(d),'sha256':hashlib.sha256(d).hexdigest()}
def write(n,d):(O/n).write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
guard=B/'lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
assert digest(guard)['sha256']=='825ee0d48177cd12354cdbf36fd36b61f0503ff3241356a7bf638ee0bc49fa45'
support=O/'support';support.mkdir(exist_ok=True)
for name,p in [('ancestor-AGENTS.md',B.parents[3]/'AGENTS.md'),('batch-AGENTS.md',B/'AGENTS.md'),('candidate-DECISION.md',O.parent/'root-r166-preliminary-freeze-r1/DECISION.md'),('preliminary-DECISION.md',O.parent/'root-pendulum-preliminary-adoption-r1/DECISION.md')]:
 # Ancestor root selected explicitly below to avoid ambiguity in parent arithmetic.
 if name=='ancestor-AGENTS.md':p=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/AGENTS.md')
 (support/name).write_bytes(p.read_bytes())
receipts=[json.loads(s) for s in (O/'retrievals.jsonl').read_text().splitlines()]
scopes={
 'costa.html':'Author homepage and dated update; publication/CV links',
 'costa-publications.html':'Complete mathematics publication list; target-related journal entry and date',
 'costa-cv.pdf':'English CV publication entry 6 and thesis-supervision entries 6/8; remaining CV not audited',
 'cholesteric-publisher.html':'System14-15; eq24/26/27/33-34; section4.4 including Conjecture1; separate branch discussion; references; complete Appendix47-50; publisher chronology',
 'cholesteric.pdf':'Same relevant equations and statement checked against extracted version-of-record PDF, printed pp656,659-660,670-672',
 'glasgow-record.html':'Complete repository record, author list, DOI, dates, accepted-version status',
 'schaaf.pdf':'Printed pp1-6,22-27,45-51,91-97: definitions, Theorem1.1.1/Prop1.1.2, Def1.4.1/Thm1.4.2 full proof, examples1.5.1-3, Prop2.1.1/Thm2.1.2-3, section3.3 including Thm3.3.1-2 proofs and counterexample',
 'smoller-ch13.pdf':'Second edition chapter13 sectionD printed pp185-190 complete, attribution p191; rest of chapter not audited',
 'rivulets.pdf':'Introduction pendulum citation; section3.2 eq3.9; sections3.3-3.5 Props1-4; AppendixA.1-A.4 complete; no complete whole-paper audit',
 'cholesteric-crossref.json':'Exact DOI metadata and references incl Korman/Lorvanhxay',
 'openalex-cholesteric.json':'Indexed identity and locations only, not primary theorem evidence',
 'citing-work.json':'One returned indexed citation and location, not exhaustive literature census',
 'schaaf.html':'Book metadata, edition and table of contents',
 'smoller-book.html':'Second-edition metadata and chapter13 URL',
 'korman-biblio.json':'Correct DOI10.1142/8308 identity only',
 'korman-openlibrary.json':'Bibliographic record only; no fulltext',
 'schaaf-biblio.json':'Correct DOI discovery only',
 'smoller-biblio.json':'Returned chapter14 identity only; table of contents then selected chapter13',
 'lorvan-search.json':'One indexed result, not thesis body',
 'lorvan-cv.html':'Portuguese CV retained only; not substantive clearance',
}
coverage=[]
for r in receipts:
 x=dict(r);x['coverage']=scopes.get(r['name'],'No scholarly clearance: failed, interstitial, irrelevant, or wrong guessed bibliographic route')
 if 'sha256' in r:assert digest(O/'research'/r['name'])=={'bytes':r['bytes'],'sha256':r['sha256']}
 coverage.append(x)
write('body-coverage.json',coverage)
write('failures.json',{'new':[{'command':'Initial native pwd && rg --files ... | head -80','deviation':'Inventory preceded freeze verification; no candidate scientific content read. Native bounded reads were allowed, but literal before-any-action ordering was not met.'},{'command':'rg ... copies/candidate/pendulum* | head -20','error':'No such file or directory: sources were under sources/; native read only.'},{'command':'research.py requests recorded in retrievals.jsonl','failures':[r for r in receipts if 'error' in r],'notes':'Google interstitials and irrelevant Bing hotel results not credited. Wrong AMS volume unrelated; wrong WorldScientific8558 and initial Schaaf DOI guessed before exact metadata; wrong EJDE path404. No blocked route retried.'},{'command':'guarded output extraction of journal and broad matching contexts','qualification':'One display truncated (11744 tokens); not treated as full-document reading. Exact focused journal statement/formulas and appendix contents separately inspected; coverage restricted accordingly.'}],'inherited':'copies/preliminary/failures.json, copies/candidate/http.jsonl, copies/candidate/discovery.md preserved verbatim','guard_qualification':'All Python and network/extraction/hash/check processes guarded; native reads/apply_patch only outside guard. Some inline guard receipts retained only in conversation tool transcript.'})
write('provenance.json',{'reviewer':'solo source/subsumption review r2','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'local_date':'2026-10-29','recommendation':'HOLD formal/manuscript investment and acceptance','source_scope':'PASS numberedConjecture1 all phi in(0,pi/2), squared ordinate z in[0,2] only','mathematics':'Inherited PASS plus independent preliminary closed-endpoint supplement; no new bridge/check','publication_history':'Positively identified changed-title published mathematical successor DOI10.1007/s13370-020-00851-9; source claim remains conjecture in actual version-of-record body','substantive_eligibility':'HOLD: no complete classical subsumption bridge established and no novelty proof inferred from no-match','credit':0,'counts':{'additional':9,'total':39,'next':40},'guard':{'path':str(guard.resolve()),**digest(guard),'AS_bytes':536870912,'group_RSS_bytes':536870912,'CPU_seconds':210,'wall_seconds':230,'nominal_sample_seconds':0.04,'environment':{'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1','PYTHONDONTWRITEBYTECODE':'1'},'limits_raised':False,'continuous_peak_guarantee':False},'new_network_receipts':'retrievals.jsonl','exact_body_coverage':'body-coverage.json','fixed_prior':{'omega':'2b143c68ca72fcaccfe71d6233cb2c6db4c8c059','openai':'4eaee87548250b2682affda7d05d947c05554bae','HEAD_refresh':False,'delta':'22commits/11 returned patches topic-screened only','old_300_path_gaps_retained':True,'global_semantic_clearance':False},'restrictions':{'writes_only_assigned_lane':True,'children':0,'git':0,'shared_count_edits':0,'Lean':0,'manuscripts':0,'messages_posts_uploads_browser_tabs':0},'process_receipts':'search1..9-guard.log retained; inline guard receipts and initial verification/finalization receipts in tool transcript','manifest_convention':'Every final payload file except finalmanifest.json and manifest-verification.json is hashed; verification receipt separately records manifest hash.'})
checks=[]
for label,freeze,root,count in [('candidate','root-r166-preliminary-freeze-r1','sol-fresh-source-discovery-r166',57),('preliminary','root-pendulum-preliminary-adoption-r1','sol-pendulum-time-map-preliminary-review-r1',100)]:
 m=O.parent/freeze/'review-freeze.json'; assert m.read_bytes()==(O/(label+'-freeze.json')).read_bytes(); d=json.loads(m.read_text());assert len(d['files'])==count;base=(O.parent/root).resolve();rows=[]
 for f in d['files']:
  p=pathlib.Path(f['path']);q=O/'copies'/label/p.relative_to(base);expected={'bytes':f['bytes'],'sha256':f['sha256']};assert digest(p)==expected and digest(q)==expected;rows.append({'original':str(p),'copy':str(q.relative_to(O)),**expected})
 checks.append({'set':label,'pass':True,'files':rows,'freeze':digest(m)})
write('after-freeze.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'checks':checks,'helper_guard_unchanged':True})
rows=[{'path':str(p.relative_to(O)),**digest(p)} for p in sorted(O.rglob('*')) if p.is_file() and p.name not in ['finalmanifest.json','manifest-verification.json']]
write('finalmanifest.json',{'root':str(O.resolve()),'files':rows})
for r in rows:assert digest(O/r['path'])=={'bytes':r['bytes'],'sha256':r['sha256']}
write('manifest-verification.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':len(rows),'all_match':True,'manifest':digest(O/'finalmanifest.json'),'original_and_copy_freezes':'57+100 PASS before/after','guard_unchanged':digest(guard)})
print(json.dumps({'payload_files_verified':len(rows),'freeze_candidate':57,'freeze_preliminary':100,'all_pass':True}))
