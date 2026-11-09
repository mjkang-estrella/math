from pathlib import Path
import hashlib,json,re,zipfile,subprocess,os
r=Path(__file__).resolve().parent
receipt=json.loads((r/'fresh-replay/logs/replay-receipt.json').read_text())
assert receipt['status']=='pass'
audit=(r/'fresh-replay/logs/Audit.log').read_text()+'\n'+(r/'fresh-replay/logs/AuditR3.log').read_text()
pairs=re.findall(r'DECL\|([^|\n]+)\|MODULE\|([^|\n]+)\|UNSAFE',audit)
assert len(pairs)==sum(int(x) for x in re.findall(r'AUDITED_LOCAL_DECLARATIONS\|(\d+)',audit))
counts={}
for name,module in pairs: counts[module]=counts.get(module,0)+1
before=json.loads((r/'receipts/inputs-before.json').read_text())
checks={name:{'source_unchanged':hashlib.sha256((r.parent/name).read_bytes()).hexdigest()==h,'copy_identical':hashlib.sha256((r/'inputs'/name).read_bytes()).hexdigest()==h} for name,h in before.items()}
assert all(all(v.values()) for v in checks.values())
(r/'receipts/inputs-after.json').write_text(json.dumps({'status':'pass','file_count':len(checks),'checks':checks},indent=2)+'\n')
old=list((r/'inputs/xor-magic-formal-r2/formal').glob('*.lean'))
assert all(f.read_bytes()==(r/'formal'/f.name).read_bytes() for f in old)
manifest=json.loads((r/'source-manifest.json').read_text())
assert all(hashlib.sha256((r/f).read_bytes()).hexdigest()==h and hashlib.sha256((r/'fresh-replay'/f).read_bytes()).hexdigest()==h for f,h in manifest.items())
refusal=subprocess.run(['python3','-I',str(r/'fresh-replay/replay.py')],capture_output=True,text=True)
assert refusal.returncode!=0 and 'Refusing a packet containing existing oleans' in refusal.stderr
(r/'receipts/existing-olean-refusal.txt').write_text(refusal.stdout+refusal.stderr)
checksreceipt={'status':'PARTIAL_PACKET_REPLAY_PASS','strict_builds':len(receipt['modules'])+2,'leanchecker_runs':len(receipt['modules'])+2,'audited_declarations':len(pairs),'by_module':counts,'negative_controls':receipt['negative_controls'],'all_inherited_modules_byte_identical':len(old),'input_files_unchanged':len(before),'source_extraction_hash_identity':True,'existing_olean_refusal':True,'peak_sampled_private_rss_bytes':max(x['sampled_private_rss_bytes'] for x in receipt['receipts']),'max_wall_seconds':max(x['wall_seconds'] for x in receipt['receipts'])}
(r/'receipts/final-validation.json').write_text(json.dumps(checksreceipt,indent=2)+'\n')
res=json.loads((r/'inputs/xor-magic-formal-r2/results.json').read_text());v=res['372205']
v.update(status='PARTIAL_NOT_QUALIFYING',credit=0,root_acceptance='not accepted; root adjudication required',packet='xor-magic-r3-partial-source.zip',replay_status='PARTIAL_PACKET_REPLAY_PASS',audit=f'PASS: all {len(pairs)} declarations in all {len(receipt["modules"])} proof modules; full type/body AST, module, safety/partial flags and transitive axioms.',leanchecker=f'PASS: {len(receipt["modules"])+2} modules including Audit and AuditR3',negative_controls={x:'rejected by kernel decide as expected' for x in receipt['negative_controls']},input_hash_verification=f'PASS: all {len(before)} before/after source and local-copy hashes unchanged',remaining_jobs=0,final_validation_receipt='receipts/final-validation.json')
v['declaration_counts'].update(proof_modules=len(receipt['modules']),all_local_declarations=len(pairs),by_module=counts,new_r3_proof_modules=8,new_r3_declarations=sum(counts[x] for x in ['LiftGraph','AffineLift','LiftFibres','LiftSums','LiftSections','LiftIncidence','LiftEdgeCount','StrongCycles']))
v['resource_limits']['exceptions'] = ['Three expanded-text audit attempts were killed by the RSS guard. Receipts: combined-audit-rss-guard.json, partition-audit-rss-guard.json, stream-audit-rss-guard.json. Final audit uses the byte-identical inherited Audit and a lossless shared Expr DAG for all r3 declarations; all final calls passed under the caps.']
v['completed_components'] += ['actual ordered-edge affine four-fold graph with inverse transports and degree preservation', 'exact two-coordinate neighborhood formulas and graph matching decomposition persistence', 'actual incidence D and B maps, nonzero BD entry, edge count and translation existence', 'component fibre transport, equal cardinalities along paths, singleton and size-three section obstructions', 'strong cycle record and four concrete seed bridges']
v['remaining_components'] = ['two-factor cycle orientation and special slope assignment', 'neighborhood constant sum equals Bc and linear coefficient cancellation', 'distinguished-cycle affine holonomy and full-fibre connectivity', 'complement matching decomposition and distinguished-cycle persistence', 'interpolation graph and literal degree interval assembly', 'n -> n+2 induction and universal CorrectedAt endpoint']
v['audit_encoding'] = 'Inherited Audit: full expanded type/body AST; AuditR3: lossless shared Expr DAG with all c.type and c.value? true roots, checked by tools/check_dag.py.'
v['new_helpers']=[{'declaration':'XorMagic.affine_translation_exists_regular','statement':'For any nonempty Fin m, any decidable simple graph G, any d-regularity proof with 4 <= d, and any s : OrientedEdge G -> Fin 3, there exists c : OrientedEdge G -> Four with incidenceB G s c = 0 and c not in (incidenceD G s).range.','proved':True},{'declaration':'XorMagic.EdgeTransport.matching','statement':'Every MatchingDecomposition G d induces a MatchingDecomposition T.graph d for any EdgeTransport G.','proved':True}]
(r/'results.json').write_text(json.dumps(res,indent=2,ensure_ascii=False)+'\n')
with (r/'SUMMARY.md').open('a') as f:f.write(f'\nFresh extracted sanitized replay passed: {len(receipt["modules"])+2} strict builds, {len(receipt["modules"])+2} leanchecker runs, all {len(pairs)} declarations audited and nine negative controls rejected as expected. Existing-olean refusal passed. All {len(old)} inherited Lean modules and all {len(before)} designated input files are byte-identical. Peak sampled private RSS was {checksreceipt["peak_sampled_private_rss_bytes"]} bytes; longest bounded call was {checksreceipt["max_wall_seconds"]:.3f} seconds. Three expanded-text audit attempts reached the RSS guard and were killed; all receipts and logs are retained. The final audit covers inherited declarations with the unchanged Audit and all r3 declarations with a lossless shared Expr DAG read from c.type and c.value? true. Every DAG root and child reference is validated. An earlier DAG using semantic Expr equality was rejected by the checker; the final serializer uses ExprStructEq and structural traversal, preserving binder names exactly. The replay validates this partial packet only.\n')
with zipfile.ZipFile(r/'xor-magic-r3-partial-source.zip','w',zipfile.ZIP_DEFLATED) as z:
 for f in [r/name for name in manifest]+[r/'source-manifest.json',r/'SUMMARY.md',r/'GAPS.md',r/'REPRODUCE.md',r/'statement-correspondence.md',r/'results.json']+list((r/'receipts').glob('*')):
  z.write(f,str(f.relative_to(r)))
(r/'receipts/packet-sha256.txt').write_text(hashlib.sha256((r/'xor-magic-r3-partial-source.zip').read_bytes()).hexdigest()+'  xor-magic-r3-partial-source.zip\n')
print(json.dumps(checksreceipt,indent=2))
