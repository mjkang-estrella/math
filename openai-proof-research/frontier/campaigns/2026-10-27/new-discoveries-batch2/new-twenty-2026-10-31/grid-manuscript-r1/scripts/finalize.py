from pathlib import Path
import json,hashlib,shutil,datetime
D=Path.cwd(); B=D.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
b=json.loads((D/'hashes/inputs-before.json').read_text()); a={p:sha(Path(p)) for p in b}; changes=[p for p in b if a[p]!=b[p]]
assert all(p.endswith('/grid-fidelity-r1/REVIEW.md') for p in changes)
old=D/'inputs/grid-fidelity-r1/REVIEW.md'; hist=D/'inputs/grid-fidelity-r1/REVIEW-initial.md'
if changes and not hist.exists(): shutil.copyfile(old,hist)
for p in [B/'grid-fidelity-r1/REVIEW.md',B/'grid-fidelity-r1/review.json',B/'grid-parent-final-r1/replay-result.json',B/'grid-parent-final-r1/registry-refresh.json']:
 if p.exists():
  q=D/'inputs'/p.relative_to(B); q.parent.mkdir(exist_ok=True,parents=True); shutil.copyfile(p,q)
status={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'fidelity_review_present':(B/'grid-fidelity-r1/REVIEW.md').exists(),'fidelity_json_present':(B/'grid-fidelity-r1/review.json').exists(),'root_replay_result_present':(B/'grid-parent-final-r1/replay-result.json').exists(),'registry_refresh_present':(B/'grid-parent-final-r1/registry-refresh.json').exists(),'credit':0}
assert not status['fidelity_json_present'] and not status['root_replay_result_present'],'New final records arrived: read and integrate before packaging'
(D/'root-status.json').write_text(json.dumps(status,indent=2)+'\n')
(D/'hashes/inputs-after.json').write_text(json.dumps(a,indent=2)+'\n')
(D/'receipts/input-integrity.json').write_text(json.dumps({'files':len(b),'all_immutable_inputs_unchanged':True,'all_inputs_including_active_review_unchanged':a==b,'supplier_updated_optional_inputs':changes,'note':'The active fidelity review appended an auditor diagnostic note. Initial and final copies are preserved; no other lane was edited. Initial prose orientation preceded baseline, so no before-first-read claim.'},indent=2)+'\n')
latest={str(B/'grid-fidelity-r1/REVIEW.md'):sha(B/'grid-fidelity-r1/REVIEW.md')}; (D/'hashes/optional-final-before.json').write_text(json.dumps(latest,indent=2)+'\n')
copy={str(p.relative_to(D)):{'original':str(B/p.relative_to(D/'inputs')),'sha256':sha(p)} for p in (D/'inputs').rglob('*') if p.is_file()}
copy['inputs/grid-fidelity-r1/REVIEW-initial.md']['original']=str(B/'grid-fidelity-r1/REVIEW.md')+' (initial snapshot)'
(D/'SOURCE-COPIES.json').write_text(json.dumps(copy,indent=2)+'\n')
p=D/'paper.md'; s=p.read_text(); needle='The four inherited negative controls are intended to fail:'
new='The fidelity review adds that auditor imports emit deprecation warnings despite the requested warningAsError flag and successful exit status. Here “strict” denotes the actual flags and successful checks, not a warning-free transcript. '
if new not in s:s=s.replace(needle,new+'\n\n'+needle)
p.write_text(s); (D/'PROOF.md').write_text('# Consolidated ordinary proof - DRAFT\n\nZero accepted credit.\n\n'+s.replace('---PAGE---','\n'))
print(status)
