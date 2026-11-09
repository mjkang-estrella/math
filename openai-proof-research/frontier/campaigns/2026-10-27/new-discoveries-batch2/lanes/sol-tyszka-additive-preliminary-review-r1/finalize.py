from pathlib import Path
import datetime,hashlib,json
O=Path(__file__).resolve().parent
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
utc=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
freeze=json.loads((O/'input-freeze.json').read_text())
for r in freeze['scientific']:
    assert h(Path(r['original']))==r['sha256']==h(O/r['copy']),r
    (O/r['copy']).chmod(0o444)
sources=[]
for lane,name,url,version,coverage in [
 ('sol-wide-mechanism-scout-r217','inputs/tyszka.pdf','https://arxiv.org/pdf/math/0702558','math/0702558v86; 4 December 2009','Conjectures 3/4/5, Observation3, Theorems11/12, Lemma4 actual bodies'),
 ('sol-wide-mechanism-scout-r217','work/1108.4078v2.pdf','https://arxiv.org/pdf/1108.4078v2','v2 4 May 2012; v1 20 August 2011','entire extracted primary body, fourteen pages'),
 ('claude-tyszka-subgroup-full-r1','work/dl/12-bfrt-pdf/bfrt.pdf','https://www.ams.org/journals/proc/1989-105-04/S0002-9939-1989-0955458-1/S0002-9939-1989-0955458-1.pdf','Proc AMS105(4), April1989, pp844-846','entire three-page body; independently re-extracted cached failed-run PDF')]:
    p=O/'inputs'/lane/name
    sources.append(dict(copy=str(p.relative_to(O)),sha256=h(p),url=url,version=version,actual_read=coverage))
provenance={'utc':utc(),'sources':sources,'fresh_http':'http.jsonl','inherited_http':['inputs/sol-wide-mechanism-scout-r217/http.jsonl','inputs/claude-tyszka-subgroup-full-r1/work/http.jsonl'],'input_bindings':'input-freeze.json','administration':'Snapshots only; no scientific premise depends on mutable live ledger/NEXT. Embedded inherited bindings are provenance only.','failed_claude_status':'User reports FAILED at API rate limit; partial artifacts preserved, no verified delivery asserted.','limits':['No original target journal body','No exhaustive public proof-registry/citer/history clearance','r217 denied AMS route not retried; cached failed-run different successful route read only','Initial unguarded inventory deviation recorded in FAILURES.md'],'scope':'Independent review; root alone adjudicates; no Lean/manuscript investment'}
(O/'provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')
(O/'review.json').write_text(json.dumps({'utc':utc(),'recommendation':'EXCLUDE_ROUTINE_CLASSICAL_BRIDGES','source':'PASS actual arXiv endpoints; journal correspondence unread','math':'PASS with explicit square BFRT/Cramer clarification','substantive':'FAIL eligibility via complete bridges in review.md','novelty':'Bounded only; no explicit earlier full arbitrary-G/residual endpoint asserted','formal_feasibility':'Feasible in principle; no formal endpoint/replay performed','checks':'check-results.json','failed_claude_delivery_verified':False},indent=2)+'\n')
excluded=['finalmanifest.json','verification-receipt.json']
manifest={'utc':utc(),'explicit_exclusions':excluded,'files':{str(p.relative_to(O)):h(p) for p in sorted(O.rglob('*')) if p.is_file() and str(p.relative_to(O)) not in excluded}}
(O/'finalmanifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'status':'final writes complete','files':len(manifest['files']),'scientific_bindings':len(freeze['scientific'])}))
