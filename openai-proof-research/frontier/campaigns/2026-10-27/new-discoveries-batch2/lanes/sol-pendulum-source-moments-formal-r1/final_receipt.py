import pathlib,json,subprocess,sys
from audit_tools import sha,audit,dependencies
R=pathlib.Path(__file__).resolve().parent
run=subprocess.run([sys.executable,str(R/'verify_inputs.py')],capture_output=True,text=True)
assert run.returncode==0,run.stderr
assert sha(R/'helper_guard.py')==sha(R.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py')
receipt=json.loads((R/'EXTRACTED/replay-receipt.json').read_text())
assert receipt['status']=='MANDATORY_COMPONENT_SOURCE_ONLY_REPLAY_PASS'
assert receipt['archive_sha256']==sha(R/'component-source.zip')==sha(R/'component-source-repeat.zip')
manifest=json.loads((R/'manifest.json').read_text())
for n,h in manifest.items():assert sha(R/n)==sha(R/'EXTRACTED'/n)==h,n
assert audit(R)==receipt['declarations']==audit(R/'EXTRACTED')
assert dependencies(R)==json.loads((R/'dependency-hashes.json').read_text())
for m in ['Defs','Substitution','Moments','Source','FullAudit']:
 assert (R/'logs'/f'{m}.log').read_bytes()==(R/'EXTRACTED/logs'/f'{m}.log').read_bytes(),m
out={'status':'MANDATORY_COMPONENT_DELIVERED','full_SourceClaim_proved':False,'credit':0,'counts_unchanged':'9 additional /39 total; next40','mathematical_modules':4,'actual_declarations':len(receipt['declarations']),'all_flags_false':True,'standard_three_axioms_only':True,'fresh_source_only_replay':True,'deterministic_archive_sha256':sha(R/'component-source.zip'),'originals_at_delivery':json.loads(run.stdout),'helper_guard_matches_designated':True,'source_and_audit_logs_byte_identical_to_fresh_replay':True,'hashed_upstream_olean_and_companion_files':len(dependencies(R))}
(R/'FINAL-RECEIPT.json').write_text(json.dumps(out,indent=2)+'\n')
(R/'originals-after.json').write_text(run.stdout)
print(json.dumps(out,indent=2))
