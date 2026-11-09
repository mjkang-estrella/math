import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,shutil
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';R=P/'shoe-pair-discrepancy-formal-independent-review-sol-r6';F=P/'shoe-discrepancy-root-final-r7'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def save(q,d):
 assert not q.exists(),str(q)
 q.parent.mkdir(parents=True,exist_ok=True);q.write_text(json.dumps(d,indent=2)+'\n')
assert not F.exists() and json.loads((P/'ledger.json').read_text())['accepted_new']==55
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
m=json.loads((R/'SHA256-MANIFEST.json').read_text());files=m['files'];assert len(files)==1108 and all(sha(R/n)==v for n,v in files.items())
frozen=json.loads((R/'frozen-inputs.json').read_text());assert len(frozen)==2120
for n,v in frozen.items():
 assert 'cmdrr-five-three-formal-independent-review-sol-r6' not in n and 'expanded-corpus-r439' not in n
 assert sha(Path(n))==v
after=json.loads((R/'frozen-after.json').read_text());assert after['count']==2120 and after['mismatches']==[]
term=json.loads((R/'TERMINAL-EXCLUSIONS.json').read_text());assert term['manifest_sha256']==sha(R/'SHA256-MANIFEST.json')
terminal='receipt/1794124776289240226_terminal_manifest.json';tj=json.loads((R/terminal).read_text());assert tj['exit']==0 and tj['group_members_left']==[]
assert sha(R/terminal)==term['terminal_receipt_sha256'] and sha(Path(tj['log']))==term['terminal_log_sha256']==tj['log_sha256']
display='audit/displays/receipt-display-1794124780046725404.json';actual_display=json.loads((R/display).read_text())
assert {k:v for k,v in actual_display.items() if k!='time_ns'}=={k:v for k,v in term['final_display_record'].items() if k!='time_ns'}
terminal_precision_correction=dict(declared_path='audit/displays/receipt-display-1794124780046725400.json',actual_path=display,actual_sha256=sha(R/display),declared_time_ns=str(term['final_display_record']['time_ns']),actual_time_ns=str(actual_display['time_ns']),scope='Exact final-display filename/time transcription differs by4ns; all other fields and receipt/log hashes match. Root records the actual filename/hash separately without altering original manifest/declaration; no proof/build/audit bytes affected. Numeric transcription is consistent with large-integer precision loss.')
review=json.loads((R/'review.json').read_text())['324571'];assert review['technical_pass'] and not review['accepted'] and review['credit']==0
assert sha(R/'FINAL-REVIEW.md')==review['report_sha256']
rep=json.loads((R/'results/strict-replay-evidence.json').read_text());assert len(rep)==28
receipts=[]
for n in [n for n in files if n.startswith('receipt/') and n.endswith('.json')]+[terminal]:
 j=json.loads((R/n).read_text());assert j['group_members_left']==[] and Path(j['log']).resolve().is_relative_to(R) and sha(Path(j['log']))==j['log_sha256']
 receipts.append(dict(path=n,sha256=sha(R/n),label=j['label'],exit=j['exit'],guard=j.get('guard'),group_members_left=j['group_members_left']))
for row in rep:
 mod=row['module'];assert sha(R/'src'/f'{mod}.lean')==row['source']==row['extracted']==sha(R/'replay/src'/f'{mod}.lean')
 assert sha(R/'build'/f'{mod}.olean')==row['olean'] and sha(R/'replay/build'/f'{mod}.olean')==row['replay_olean']
 for phase in ['lean_','leanchecker_','replay_lean_','replay_checker_']:
  v=row[phase];q=R/v['receipt'];assert sha(q)==v['receipt_sha256'];j=json.loads(q.read_text());assert j['exit']==0 and j['log_sha256']==v['log_sha256']
  lp=j['env']['LEAN_PATH'].split(':');assert lp[0]==str(R/('replay/build' if phase.startswith('replay') else 'build')) and all('/2026-10-14/formal/.lake/packages/' in x for x in lp[1:])
  if phase in ['lean_','replay_lean_']:assert all(x in j['argv'] for x in ['-j1','-M3500','-DwarningAsError=true'])
audit=json.loads((R/'audit/own-closures.json').read_text());origin=json.loads((R/'audit/origin-validation.json').read_text())
assert audit['complete'] and not audit['unsafe'] and set(audit['axioms'])=={'propext','Classical.choice','Quot.sound'}
assert audit['root_count']==259 and audit['node_count']==29367 and len(audit['closures'])==17
assert collections.Counter(audit['root_classes'].values())=={'core':242,'control':17}
assert origin['whole_environment_count']==428468 and origin['production_roots_exact']==259 and origin['all_reachable_origins_match']
assert audit['closures']['Shoe.source_strict_universal_supremum']['count']==29263 and audit['closures']['Shoe.countable_color_strict_universal_supremum']['count']==29308
assert all(not x['unsafe'] and set(x['axioms'])<=set(audit['axioms']) and x['count']==len(x['closure']) for x in audit['closures'].values())
record=dict(utc=now,mathdb_id=324571,review_lane=str(R),manifest_files_verified=len(files),manifest_sha256=sha(R/'SHA256-MANIFEST.json'),manifest_mismatches=[],frozen_verified=len(frozen),frozen_mismatches=[],frozen_after=after,terminal_exclusions=term,terminal_exclusions_file_sha256=sha(R/'TERMINAL-EXCLUSIONS.json'),terminal_display_precision_correction=terminal_precision_correction,receipts=receipts,receipt_count=len(receipts),receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in receipts)),strict_checks=28,kernel_checks=28,separate_source_only_replay_strict=28,separate_source_only_replay_checkers=28,review=review,
 audit_summary=dict(core_roots=242,control_roots=17,union_nodes=29367,environment=428468,endpoint_counts={k:v['count'] for k,v in audit['closures'].items()},axioms=audit['axioms'],unsafe=[]),
 root_status='INDEPENDENT_TECHNICAL_PASS_VERIFIED__REPORTING_FIXES_AND_ROOT_ACCEPTANCE_PENDING',
 root_scope='Documentary integrity/receipt verification and orchestration only, no mathematical/compiler execution',credit=0,accepted_new=55,target_new=60,previous_accepted=39)
save(P/'shoe-pair-discrepancy-formal-independent-review-parent-integration-sol-r6.json',record)
F.mkdir();(F/'source').mkdir();(F/'output/pdf').mkdir(parents=True);(F/'tmp/pdfs').mkdir(parents=True);(F/'qa').mkdir();(F/'evidence').mkdir()
save(F/'evidence/independent-pass-receipts.json',record)
save(F/'evidence/PRODUCTION-ORDER.json',[r['module'] for r in rep])
save(F/'evidence/PRODUCTION-HASHES.json',{r['module']:r['source'] for r in rep})
for src,rel in [(R/'FINAL-REVIEW.md','evidence/FINAL-REVIEW.md'),(R/'review.json','evidence/review.json'),(R/'PINS.json','evidence/PINS.json'),(R/'results/strict-replay-evidence.json','evidence/strict-replay-evidence.json'),(R/'audit/origin-validation.json','evidence/origin-validation.json')]:shutil.copyfile(src,F/rel)
save(ROOT/'shoe-final-r7-integrity-ready.json',dict(utc=now,lane=str(F),review=str(R),manifest_verified=len(files),frozen_verified=len(frozen),proof_modules=28,root_report_only=True,acceptance_pending=True))
print(json.dumps(dict(final_lane=str(F),manifest=len(files),frozen=len(frozen),receipts=len(receipts),exits=record['receipt_exit_counts'],modules=28,technical_pass=True)))
