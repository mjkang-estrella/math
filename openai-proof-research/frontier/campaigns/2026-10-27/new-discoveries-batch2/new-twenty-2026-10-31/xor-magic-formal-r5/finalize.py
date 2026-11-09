from pathlib import Path
import hashlib,json,re,zipfile,subprocess,os
r=Path(__file__).resolve().parent
receipt=json.loads((r/'fresh-replay/logs/replay-receipt.json').read_text());assert receipt['status']=='pass'
manifest=json.loads((r/'source-manifest.json').read_text())
assert all(hashlib.sha256((r/p).read_bytes()).hexdigest()==h==hashlib.sha256((r/'fresh-replay'/p).read_bytes()).hexdigest() for p,h in manifest.items())
before=json.loads((r/'receipts/input-before.json').read_text());after={}
for p,h in before.items():
 assert hashlib.sha256((r.parent/p).read_bytes()).hexdigest()==h
 assert hashlib.sha256((r/'inputs'/p).read_bytes()).hexdigest()==h
 after[p]=h
(r/'receipts/input-after.json').write_text(json.dumps(after,indent=2)+'\n')
inherited={p.name:p for p in (r/'inputs/xor-magic-formal-r4c/formal').glob('*.lean')}
inherited.update({p.name:p for p in (r/'inputs/xor-magic-formal-r4b/formal').glob('*.lean')})
assert all(p.read_bytes()==(r/'formal'/n).read_bytes() for n,p in inherited.items())
audit=json.loads((r/'fresh-replay/logs/full-audit-summary.json').read_text())
refusal=subprocess.run(['python3','-I',str(r/'fresh-replay/replay.py')],capture_output=True,text=True)
assert refusal.returncode and 'Refusing a packet containing existing oleans' in refusal.stderr
(r/'receipts/existing-olean-refusal.txt').write_text(refusal.stdout+refusal.stderr)
active=[];ancestors=set();ancestor=os.getpid()
while ancestor>1:
 ancestors.add(ancestor)
 try:ancestor=int(Path(f'/proc/{ancestor}/stat').read_text().split(') ')[1].split()[1])
 except (FileNotFoundError,ProcessLookupError):break
for proc in Path('/proc').iterdir():
 if not proc.name.isdigit() or int(proc.name) in ancestors:continue
 try:
  if not str((proc/'cwd').resolve()).startswith(str(r)):continue
  args=(proc/'cmdline').read_bytes().split(b'\0')
  exe=Path(args[0].decode()).name if args else ''
  script=Path(args[1].decode()).name if len(args)>1 else ''
  if exe in ['lean','leanchecker'] or script in ['replay.py','bounded.py','build.py']:active.append(int(proc.name))
 except (FileNotFoundError,ProcessLookupError,PermissionError):pass
assert not active,active
(r/'receipts/no-background-jobs.json').write_text(json.dumps({'status':'pass','active_jobs':active},indent=2)+'\n')
mods=json.loads((r/'modules.json').read_text());proof=list(audit['by_module']);new=[m for m in proof if m+'.lean' not in inherited]
validation={'status':'pass','strict_builds':len(mods),'leanchecker_runs':len(mods),'negative_controls':receipt['negative_controls'],'proof_modules':len(proof),'all_local_declarations':audit['declarations'],'audited_declaration_occurrences':audit['declaration_occurrences'],'new_proof_modules':new,'new_declarations':sum(audit['by_module'][m] for m in new),'inherited_modules_byte_identical':len(inherited),'inputs_unchanged_and_copies_identical':len(before),'peak_sampled_private_rss_bytes':max(x['sampled_private_rss_bytes'] for x in receipt['receipts']),'longest_bounded_call_seconds':max(x['wall_seconds'] for x in receipt['receipts']),'resource_guard_kills':sum(x['exit']<0 for x in receipt['receipts']),'source_extraction_hash_identity':True,'no_background_jobs':True}
assert validation['resource_guard_kills']==0
(r/'receipts/final-validation.json').write_text(json.dumps(validation,indent=2)+'\n')
results={'status':'COMPLETE_ENDPOINT_PACKET_PENDING_ROOT_ACCEPTANCE','credit':0,'root_accepted':False,'final_theorems':[{'name':'XorMagic.corrected_all','statement':'∀ n : ℕ, 4 ≤ n → XorMagic.CorrectedAt n','proved':True},{'name':'XorMagic.not_printed_each_ge_four','statement':'∀ n : ℕ, 4 ≤ n → ¬ XorMagic.PrintedAt n','proved':True}],'reexports':['XorMagic.printed_not_all','XorMagic.printed_not_positive'],'connectivity_free_obstruction':'XorMagicFinal.no_closed_top_four_any','declaration_counts':audit,'validation':validation,'remaining_formal_gaps':[],'acceptance_limits':['root acceptance pending','prior-art and manuscript qualifications from root ruling remain'],'allowed_axioms':['propext','Classical.choice','Quot.sound'],'network_requests':0,'resource_caps':{'cpus':2,'private_rss_bytes':6*1024**3,'cpu_seconds':120,'wall_seconds':140,'address_space_bytes':64*1024**3,'MALLOC_ARENA_MAX':2}}
(r/'results.json').write_text(json.dumps({'372205':results},indent=2)+'\n')
with (r/'SUMMARY.md').open('a') as f:
 f.write(f'\nFresh extracted sanitized strict replay passed: {len(mods)} builds, {len(mods)} leanchecker runs, {audit["declarations"]} local declarations fully audited, and {len(receipt["negative_controls"])} negative controls rejected. All {len(inherited)} inherited modules are byte-identical, and all {len(before)} bound source inputs and copies match their initial hashes. Peak private RSS: {validation["peak_sampled_private_rss_bytes"]} bytes. Longest bounded call: {validation["longest_bounded_call_seconds"]:.3f} seconds. No guard kills or background jobs remain. Existing-olean refusal and extracted source hash identity passed.\n')
# Keep proof sources and portable replay, never compiled output.
with zipfile.ZipFile(r/'xor-magic-r5-source.zip','w',zipfile.ZIP_DEFLATED) as z:
 for name in manifest:z.write(r/name,name)
 for name in ['source-manifest.json','SUMMARY.md','GAPS.md','results.json','REPRODUCE.md','statement-correspondence.md','TASK.txt']:
  z.write(r/name,name)
 for p in (r/'receipts').glob('*'):
  if p.is_file() and p.name!='packet-sha256.txt':z.write(p,str(p.relative_to(r)))
 for p in (r/'fresh-replay/logs').glob('*'):
  if p.is_file():z.write(p,'validation-logs/'+p.name)
 for p in (r/'replay-attempt1/logs').glob('*'):
  if p.is_file():z.write(p,'validation-attempt1-logs/'+p.name)
 for p in (r/'logs').glob('*'):
  if p.is_file():z.write(p,'development-logs/'+p.name)
with zipfile.ZipFile(r/'xor-magic-r5-source.zip') as z:
 assert not any('.olean' in p for p in z.namelist())
 for p,h in manifest.items():assert hashlib.sha256(z.read(p)).hexdigest()==h
(r/'receipts/packet-sha256.txt').write_text(hashlib.sha256((r/'xor-magic-r5-source.zip').read_bytes()).hexdigest()+'  xor-magic-r5-source.zip\n')
print(json.dumps(validation,indent=2))
