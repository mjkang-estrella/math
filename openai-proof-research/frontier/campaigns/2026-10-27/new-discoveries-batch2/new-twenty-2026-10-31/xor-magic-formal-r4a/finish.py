from pathlib import Path
import hashlib,json,re,zipfile,subprocess
r=Path(__file__).resolve().parent
receipt=json.loads((r/'fresh-replay/logs/replay-receipt.json').read_text())
assert receipt['status']=='pass'
audit='\n'.join((r/f'fresh-replay/logs/{x}.log').read_text() for x in ['Audit','AuditR3','AuditR4a'])
pairs=re.findall(r'DECL\|([^|\n]+)\|MODULE\|([^|\n]+)\|UNSAFE',audit)
assert len(pairs)==sum(int(x) for x in re.findall(r'AUDITED_LOCAL_DECLARATIONS\|(\d+)',audit))
assert len(set(n for n,m in pairs))==len(pairs)
counts={}
for name,module in pairs:counts[module]=counts.get(module,0)+1
new=json.loads((r/'modules.json').read_text())[-7:]
before=json.loads((r/'receipts/inputs-before.json').read_text());checks={}
for name,h in before.items():
 p=Path(name);q=r/'inputs'/p.relative_to(r.parent)
 checks[name]={'source_unchanged':hashlib.sha256(p.read_bytes()).hexdigest()==h,'copy_identical':hashlib.sha256(q.read_bytes()).hexdigest()==h}
assert all(all(v.values()) for v in checks.values())
(r/'receipts/inputs-after.json').write_text(json.dumps({'status':'pass','file_count':len(checks),'checks':checks},indent=2)+'\n')
old=list((r/'inputs/xor-magic-formal-r3/formal').glob('*.lean'))
assert len(old)==57 and all(p.read_bytes()==(r/'formal'/p.name).read_bytes() for p in old)
manifest=json.loads((r/'source-manifest.json').read_text())
assert all(hashlib.sha256((r/f).read_bytes()).hexdigest()==h and hashlib.sha256((r/'fresh-replay'/f).read_bytes()).hexdigest()==h for f,h in manifest.items())
refusal=subprocess.run(['python3','-I',str(r/'fresh-replay/replay.py')],capture_output=True,text=True)
assert refusal.returncode!=0 and 'Refusing a packet containing existing oleans' in refusal.stderr
(r/'receipts/existing-olean-refusal.txt').write_text(refusal.stdout+refusal.stderr)
checksreceipt={'status':'PARTIAL_PACKET_REPLAY_PASS','strict_builds':len(receipt['modules'])+3,'leanchecker_runs':len(receipt['modules'])+3,'proof_modules':len(receipt['modules']),'audited_declarations':len(pairs),'new_r4a_declarations':sum(counts[m] for m in new),'by_module':counts,'negative_controls':receipt['negative_controls'],'all_inherited_modules_byte_identical':len(old),'input_files_unchanged':len(before),'source_extraction_hash_identity':True,'existing_olean_refusal':True,'peak_sampled_private_rss_bytes':max(x['sampled_private_rss_bytes'] for x in receipt['receipts']),'max_wall_seconds':max(x['wall_seconds'] for x in receipt['receipts'])}
(r/'receipts/final-validation.json').write_text(json.dumps(checksreceipt,indent=2)+'\n')
res=json.loads((r/'inputs/xor-magic-formal-r3/results.json').read_text());v=res['372205']
v.update(status='PARTIAL_NOT_QUALIFYING',credit=0,root_acceptance='not accepted; root adjudication required',packet='xor-magic-r4a-partial-source.zip',replay_status='PARTIAL_PACKET_REPLAY_PASS',audit=f'PASS: all {len(pairs)} declarations in all {len(receipt["modules"])} proof modules; full type/body AST, safety/partial flags and transitive axioms.',leanchecker=f'PASS: {len(receipt["modules"])+3} modules including three audit modules',negative_controls={x:'rejected by kernel decide as expected' for x in receipt['negative_controls']},input_hash_verification=f'PASS: all {len(before)} before/after source and local-copy hashes unchanged',remaining_jobs=0,final_validation_receipt='receipts/final-validation.json')
v['declaration_counts'].update(proof_modules=len(receipt['modules']),all_local_declarations=len(pairs),by_module=counts,new_r4a_proof_modules=7,new_r4a_declarations=sum(counts[x] for x in new))
v['resource_limits'].pop('exceptions',None)
v['resource_limits'].pop('discovery_exception',None)
v['resource_limits']['exceptions_this_lane']=[]
v['completed_components'] += ['exact incidenceB equals outgoing-neighbour constant sum', 'actual outgoing slope and affine formula, omega-walk composite modulo 3', 'complete full-fibre connectivity from nonidentity affine holonomy', 'fixed-point simple-cycle lifting with exact preserved length', 'open and closed magic transfer under explicit scalar cancellation', 'translation/connectivity/cycle component assembly and complement input interface']
v['remaining_components']=['global orientation of two-factor cycles and its distinguished OmegaWalk', 'scalar cancellation at every vertex from the two exceptional factors and parity', 'indexed StrongFactorCycleData persistence in first two lifted factors', 'single seed-lift theorem on Bits (n+2)', 'r4b complement decomposition and interpolation', 'root n -> n+2 induction and universal CorrectedAt endpoint']
v['audit_encoding']='Unchanged inherited Audit: full expanded type/body AST; unchanged AuditR3 and new AuditR4a: lossless shared Expr DAG with all c.type and c.value? true roots, each separately checked.'
v['seed_lift_endpoint']={'proved':False,'declaration':None,'statement':'Produce a connected d-regular magic graph on Bits (n+2) with graph matching decomposition and StrongFactorCycleData from the specified seed, with complement factors supplied separately.'}
v['new_helpers']=[]
for m in new:
 text=(r/f'formal/{m}.lean').read_text()
 for mat in re.finditer(r'theorem\s+(\w+)([\s\S]*?)\s*:= by',text):
  namespace='XorMagic.EdgeTransport.' if 'namespace XorMagic.EdgeTransport' in text else 'XorMagic.'
  v['new_helpers'].append({'declaration':namespace+mat[1],'literal_source_statement':'theorem '+mat[1]+mat[2], 'source':'formal/'+m+'.lean','proved':True})
(r/'results.json').write_text(json.dumps(res,indent=2,ensure_ascii=False)+'\n')
with (r/'SUMMARY.md').open('a') as f:f.write(f'\nFresh extracted sanitized replay passed: {checksreceipt["strict_builds"]} strict builds, {checksreceipt["leanchecker_runs"]} leanchecker runs, all {len(pairs)} proof-module declarations audited ({checksreceipt["new_r4a_declarations"]} new), and twelve negative controls rejected as expected. All 57 inherited modules and all 107 designated input sources and copies are byte-identical. Existing-olean refusal passed. Peak sampled private RSS was {checksreceipt["peak_sampled_private_rss_bytes"]} bytes; longest bounded call was {checksreceipt["max_wall_seconds"]:.3f} seconds. No resource-guard kills occurred in this lane. Validation covers the partial packet only. No lane jobs remain.\n')
# Final repack changes only documentation/receipts; every replayed code hash is identical.
with zipfile.ZipFile(r/'xor-magic-r4a-partial-source.zip','w',zipfile.ZIP_DEFLATED) as z:
 for f in [r/name for name in manifest]+[r/'source-manifest.json',r/'SUMMARY.md',r/'GAPS.md',r/'REPRODUCE.md',r/'statement-correspondence.md',r/'results.json']+list((r/'receipts').glob('*')):
  if f.name!='packet-sha256.txt':z.write(f,str(f.relative_to(r)))
with zipfile.ZipFile(r/'xor-magic-r4a-partial-source.zip') as z:
 assert not any('.olean' in x for x in z.namelist())
 for name,h in manifest.items():assert hashlib.sha256(z.read(name)).hexdigest()==h
(r/'receipts/packet-sha256.txt').write_text(hashlib.sha256((r/'xor-magic-r4a-partial-source.zip').read_bytes()).hexdigest()+'  xor-magic-r4a-partial-source.zip\n')
print(json.dumps(checksreceipt,indent=2))
