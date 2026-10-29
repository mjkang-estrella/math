from pathlib import Path
import json,hashlib,datetime,shutil
L=Path(__file__).resolve().parent;P=L.parent
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
f=json.loads((L/'review-freeze.json').read_text());src=Path(f['source_lane']);rows={}
for p,h in f['files'].items():
 assert H(src/p)==h,p
 assert H(L/'copy'/p)==h,p
 rows[p]={'original':h,'own_copy':h,'match':True}
(L/'after.json').write_text(json.dumps({'verified_originals':len(rows),'verified_own_copies':len(rows),'files':rows},indent=2))
for p in ['root-arcsinh-review-adjudication-r1/REVIEW-DECISION.md','pi-gamma-perspective-review-r2/review.md','sol-fresh-source-discovery-r82/sources/dewitt.html','sol-fresh-source-discovery-r89/sources/bajnok-vor.txt']:
 q=L/'context'/p;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(P/p,q)
prov={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'assignment':'sol-mmpp-classical-boundary-review-r3','disposition':'HOLD overall; substantive PASS; no Lean/paper investment until historical holds cleared','credit':0,'counts':[8,38],'candidate_freeze':H(L/'review-freeze.json'),'before_after_original_and_own_copies':55,'helper_guard_source':str(P/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'),'helper_guard_sha256':H(L/'helper_guard.py'),'limits':{'AS_MiB':512,'sampled_group_RSS_MiB':512,'CPU_seconds':210,'wall_seconds':230,'nominal_sample_ms':40,'BLAS_threads':1},'executed_helpers':['prepare.py','checks.py','finalize.py'],'source_body_mode':'Own copies of cached actual extracted primary bodies; no fresh PDF bytes claimed. Source provenance HTTP and hashes inherited in context/sol-mmpp-historical-prior-review-r2/{http,provenance}.json. This review does not claim fresh reauthentication of original source bytes.','live_search':{'date':'2026-10-29','queries':['Cox process sinusoidal intensity Palm interarrival stochastic order stationary waiting time counterexample','Markov modulated Poisson stochastic order Asanjarani Nazarathy counterexample periodic intensity'],'new_primary_leads':[{'url':'https://digicoll.lib.berkeley.edu/record/113268/files/math_s6_v3_article-22.pdf','result':'403 Forbidden; body unavailable; stopped without retry'},{'url':'https://meetings.ams.org/math/jmm2024/meetingapp.cgi/Paper/25556','result':'502 Bad Gateway; body unavailable; no retry'}],'resolution_found':False,'limit':'Bounded lead search, not semantic or priority clearance'},'registry':{'Omega':'d2b0ee6e958cf646530d3476088494e349570b46','OpenAI':'7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a','status':'Inherited dated heads, new small delta body read; no new current-head refresh; r94 300-file cap incomplete'},'remaining_body_holds':['Liu-Neuts DOI10.1080/15326349108807202','2026moment DOI10.1016/j.peva.2026.102562','Cox-Lewis sinusoidal passage','AMS2024 domination abstract scope','cookbook','authenticated thesis PDF identity/full-thesis search'],'actions':{'children':False,'git':False,'shared_edits':False,'candidate_edits':False,'browser':False,'accounts_contacts_posts_uploads':False,'Lean_or_paper':False}}
(L/'provenance.json').write_text(json.dumps(prov,indent=2))
# This receipt excludes itself and the final execution log/guard, which are produced afterward.
exclude={'evidence-hashes.json','MANIFEST.sha256','finalize.log','finalize.guard.json'}
files={str(p.relative_to(L)):H(p) for p in sorted(L.rglob('*')) if p.is_file() and str(p.relative_to(L)) not in exclude}
(L/'evidence-hashes.json').write_text(json.dumps({'files':files,'excluded_self_and_execution_receipts':sorted(exclude)},indent=2))
print('55 originals and 55 own copies unchanged; evidence hashes finalized')
