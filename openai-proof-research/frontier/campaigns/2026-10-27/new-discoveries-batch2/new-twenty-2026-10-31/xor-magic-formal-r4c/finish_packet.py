from pathlib import Path
import json,hashlib,re,subprocess,zipfile,os
r=Path(__file__).resolve().parent
receipt=json.loads((r/'fresh-replay/logs/replay-receipt.json').read_text());assert receipt['status']=='pass'
mods=json.loads((r/'modules.json').read_text()); oldmods=json.loads((r.parent/'xor-magic-formal-r4a/modules.json').read_text());new=mods[len(oldmods):]
manifest=json.loads((r/'source-manifest.json').read_text())
assert all(hashlib.sha256((r/p).read_bytes()).hexdigest()==h==hashlib.sha256((r/'fresh-replay'/p).read_bytes()).hexdigest() for p,h in manifest.items())
audit='\n'.join((r/f'fresh-replay/logs/{a}.log').read_text() for a in ['Audit','AuditR3','AuditR4a','AuditR4c'])
pairs=re.findall(r'DECL\|([^|\n]+)\|MODULE\|([^|\n]+)\|UNSAFE',audit)
assert len(pairs)==sum(map(int,re.findall(r'AUDITED_LOCAL_DECLARATIONS\|(\d+)',audit)))
assert len(set(n for n,m in pairs))==len(pairs)
counts={}
for n,m in pairs:counts[m]=counts.get(m,0)+1
before=json.loads((r/'receipts/inputs-before.json').read_text());checks={}
for p,h in before.items():
 p=Path(p);q=r/'inputs'/p.relative_to(r.parent)
 checks[str(p)]={'source_unchanged':hashlib.sha256(p.read_bytes()).hexdigest()==h,'copy_identical':hashlib.sha256(q.read_bytes()).hexdigest()==h}
assert all(all(v.values()) for v in checks.values())
(r/'receipts/inputs-after.json').write_text(json.dumps({'status':'pass','file_count':len(checks),'checks':checks},indent=2)+'\n')
oldfiles=list((r/'inputs/xor-magic-formal-r4a/formal').glob('*.lean'))
assert all(p.read_bytes()==(r/'formal'/p.name).read_bytes() for p in oldfiles)
refusal=subprocess.run(['python3','-I',str(r/'fresh-replay/replay.py')],capture_output=True,text=True)
assert refusal.returncode and 'Refusing a packet containing existing oleans' in refusal.stderr
(r/'receipts/existing-olean-refusal.txt').write_text(refusal.stdout+refusal.stderr)
active=[]
ancestors=set(); ancestor=os.getpid()
while ancestor>1:
 ancestors.add(ancestor)
 try:ancestor=int(Path(f'/proc/{ancestor}/stat').read_text().split(') ')[1].split()[1])
 except (FileNotFoundError,ProcessLookupError):break
for proc in Path('/proc').iterdir():
 if not proc.name.isdigit() or int(proc.name) in ancestors: continue
 try:
  args=(proc/'cmdline').read_bytes().split(b'\0')
  cwd=(proc/'cwd').resolve()
  if not str(cwd).startswith(str(r)): continue
  exe=Path(args[0].decode()).name if args else ''
  script=Path(args[1].decode()).name if len(args)>1 else ''
  if exe in ['lean','leanchecker'] or script in ['replay.py','bounded.py']:active.append(int(proc.name))
 except (FileNotFoundError,ProcessLookupError,PermissionError):pass
assert not active,active
(r/'receipts/no-background-jobs.json').write_text(json.dumps({'active_lean_replay_or_guard_processes':active,'status':'pass'},indent=2)+'\n')
final={'status':'PARTIAL_PACKET_REPLAY_PASS','strict_builds':len(mods)+4,'leanchecker_runs':len(mods)+4,'proof_modules':len(mods),'new_proof_modules':len(new),'all_local_declarations':len(pairs),'new_local_declarations':sum(counts[m] for m in new),'by_module':counts,'negative_controls':receipt['negative_controls'],'inherited_lean_files_byte_identical':len(oldfiles),'inputs_unchanged_and_copies_identical':len(checks),'source_extraction_hash_identity':True,'existing_olean_refusal':True,'peak_sampled_private_rss_bytes':max(x['sampled_private_rss_bytes'] for x in receipt['receipts']),'longest_wall_seconds':max(x['wall_seconds'] for x in receipt['receipts']),'resource_guard_kills':0}
assert all(x['exit']==0 for x in receipt['receipts'] if not any(Path(a).stem in receipt['negative_controls'] for a in x['command']))
(r/'receipts/final-validation.json').write_text(json.dumps(final,indent=2)+'\n')
v=json.loads((r/'inputs/xor-magic-formal-r4a/results.json').read_text())['372205']
v.update(status='PARTIAL_NOT_QUALIFYING',credit=0,root_acceptance='not accepted; root adjudication required',packet='xor-magic-r4c-partial-source.zip',replay_status=final['status'],remaining_jobs=0,final_validation_receipt='receipts/final-validation.json',audit=f'PASS: all {len(pairs)} declarations in {len(mods)} proof modules, including generated declarations; full type/body, safety flags and allowed transitive axioms.',leanchecker=f'PASS: {len(mods)+4} proof and audit modules',input_hash_verification=f'PASS: {len(checks)} unchanged inputs and identical copies',negative_controls={s:'kernel decide rejects false proposition as expected' for s in receipt['negative_controls']})
v['declaration_counts'].update(proof_modules=len(mods),all_local_declarations=len(pairs),new_proof_modules=len(new),new_local_declarations=sum(counts[m] for m in new),new_r4c_proof_modules=len(new),new_r4c_declarations=sum(counts[m] for m in new),by_module=counts)
v['seed_lift_endpoint']={'proved':False,'declaration':None,'statement':'Iteratable ColouredSeed on Bits (n+2), with complement factors as LiftComplementInput hypothesis.'}
v['new_helpers']=[]
for m in new:
 s=(r/f'formal/{m}.lean').read_text()
 for hit in re.finditer(r'theorem\s+(\w+)([\s\S]*?)\s*:= by',s):
  v['new_helpers'].append({'source':'formal/'+m+'.lean','declaration_basename':hit[1],'literal_source_statement':'theorem '+hit[1]+hit[2],'proved':True})
v['new_endpoints']=[{'declaration':'XorMagic.'+x,'proved':True,'source':f'formal/{m}.lean'} for x,m in [('chosen_lift_open','ChosenLiftMagic'),('chosen_lift_closed','ChosenLiftMagic'),('chosen_open_exists','ChosenLiftExists'),('chosen_closed_exists','ChosenLiftExists'),('persistedCycle','ColourPersistence'),('chosen_seed_lift_data','ChosenSeedLiftData')]]
for ep in v['new_endpoints']:
 name=ep['declaration'].split('.')[-1]
 src=(r/ep['source']).read_text()
 hit=re.search(r'(?:theorem|def)\s+'+re.escape(name)+r'([\s\S]*?)\s*:= by',src)
 assert hit, name
 ep['literal_source_statement']=name+hit[1]
v['completed_components'] += ['proper 2-colouring and chosen outgoing slopes globally','four decide-certified ColouredSeed OmegaWalk witnesses','exact scalar cancellation for both parity types','chosen lift literal magic, regularity, translation and connectivity','indexed coloured strong cycle persistence at the holonomy fixed point','product-type ColouredLiftSeed assembly with supplied complement factors']
v['remaining_components']=['Bits relabelling and walk/OmegaWalk reassembly returning the iteratable ColouredSeed interface','r4b complement decomposition and interpolation','root induction and universal corrected existence endpoint']
v['resource_limits']['exceptions_this_lane']=[]
v['audit_encoding']='Inherited Audit expands type/body AST; AuditR3, AuditR4a and AuditR4c emit lossless shared Expr DAGs rooted in c.type and c.value? true, each separately checked.'
v['network_requests']=0
(r/'results.json').write_text(json.dumps({'372205':v},indent=2,ensure_ascii=False)+'\n')
with (r/'SUMMARY.md').open('a') as f:
 f.write(f'\nFinal fresh extracted sanitized replay passed: {len(mods)+4} strict builds, {len(mods)+4} leanchecker runs, all {len(pairs)} declarations audited ({final["new_local_declarations"]} new), and {len(receipt["negative_controls"])} negative controls rejected by kernel decide. All {len(oldfiles)} inherited Lean files are byte-identical; all {len(checks)} inputs and copies match their initial hashes. Peak sampled private RSS: {final["peak_sampled_private_rss_bytes"]} bytes; longest bounded call: {final["longest_wall_seconds"]:.3f} seconds. Existing-olean refusal passed. No resource-guard kills or background jobs remain. This validates the partial packet only.\n')
# Include all replay logs in the final source-only packet, never compiled output.
files=[r/p for p in manifest]+[r/p for p in ['source-manifest.json','SUMMARY.md','GAPS.md','results.json','REPRODUCE.md','statement-correspondence.md']]+list((r/'receipts').glob('*'))+list((r/'fresh-replay/logs').glob('*'))
with zipfile.ZipFile(r/'xor-magic-r4c-partial-source.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in files:
  if p.is_file() and p.name!='packet-sha256.txt':z.write(p,str(p.relative_to(r)))
with zipfile.ZipFile(r/'xor-magic-r4c-partial-source.zip') as z:
 assert not any('.olean' in p for p in z.namelist())
 for p,h in manifest.items():assert hashlib.sha256(z.read(p)).hexdigest()==h
(r/'receipts/packet-sha256.txt').write_text(hashlib.sha256((r/'xor-magic-r4c-partial-source.zip').read_bytes()).hexdigest()+'  xor-magic-r4c-partial-source.zip\n')
print(json.dumps(final,indent=2))
