from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent;B=L.parent
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(65536):h.update(b)
 return h.hexdigest()
fresh=json.loads((L/'fresh-coverage.json').read_text())
old=json.loads((L/'inherited-screen.json').read_text())
context={}
for n in ['NEXT.md','ledger.json','AGENTS.md','prior-campaign-context.json']:
 p=B.parent/n;context[str(p)]={'before_as_read':old['context'][str(p)],'after_sha256':sha(p),'drift':sha(p)!=old['context'][str(p)]['sha256']}
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'reviewer':'Solo GPT-6.1 Sol high/default speed; no children','recommendation':'FAIL_SUBSTANTIVE_STRICT_ROUTINE_ADAPTATION','root_owns_decision':True,'no_acceptance_or_credit_action':True,'gates':{'freeze':'PASS_103_LISTED_PLUS_DESCRIPTOR_104','published_source':'PASS','exact_math':'PASS_176_ENTRIES','formal_endpoint':'PASS','portable_replay':'PASS_31_ACTUAL_DECLARATIONS','legacy_replay':'FAIL_HISTORICAL_NEXT_CONTEXT','rebuild':'PASS_BYTE_IDENTICAL','visual':'PASS_ALL_THREE_PAGES','pdf_marker':'HOLD_HISTORICAL_PROCEDURAL_EXCEPTION','historical_prior':'PASS_BOUNDED','fresh_prior':'PASS_BOUNDED_FIXED_HEAD','substantive':'FAIL_STRICT_ROUTINE_ADAPTATION'},'hashes':{'pdf':sha(L/'extracted/paper.pdf'),'zip':sha(L/'rebuilt.zip'),'inner':sha(L/'extracted/source-only.zip'),'audit':sha(L/'fresh-replay/logs/FullAudit.log'),'helper_guard':sha(B/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py')},'fresh_registry':{'omega':fresh['head'],'openai':fresh['openai_head'],'interval_count':len(fresh['intervals']),'initial_cap_closed_by_single_commit_file_pagination':379,'bounded_HEAD_rounds':1,'actual_bodies_fetched':len(fresh['bodies'])},'context_separate_from_candidate_integrity':context,'access_limits':['Jevtic primary body unread after inherited403; not retried or used as theorem evidence.','Selective baseline semantics; no worldwide priority guarantee.','No fresh403/429/challenge; fixed HEAD only.'],'failures_preserved':['Legacy NEXT mismatch','Historical PDF marker AS failure','Initial relative response path error in evidence-first-failure.log','Initial300-file cap in first-refresh-failure.json and network.log; closed by pagination','Diagnostic KeyError on nonexistent head_commit, recorded in tool output','Some console excerpts truncated; bounded source/evidence reads determine findings'],'resources':{'helper_AS_groupRSS_MiB':512,'CPU_s':210,'wall_s':230,'helper_sample_ms':40,'BLAS':1,'Lean_j':1,'Lean_M':2700,'Lean_groupRSS_MiB':2800,'Lean_sample_ms':45},'artifacts':{str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['provenance.json','final-manifest.json']}}
(L/'provenance.json').write_text(json.dumps(out,indent=2)+'\n')
(L/'final-manifest.json').write_text(json.dumps({str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name!='final-manifest.json'},indent=2)+'\n')
print(json.dumps({'recommendation':out['recommendation'],'freeze_observed_files':len(json.loads((L/'freeze-after.json').read_text())),'fresh_intervals':len(fresh['intervals']),'context_drift':{p:v['drift'] for p,v in context.items()}}))
