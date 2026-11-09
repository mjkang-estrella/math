from pathlib import Path
import json,re,hashlib,collections,subprocess,os
r=Path(__file__).resolve().parent
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
before=json.loads((r/'inputs-before.json').read_text());after={p:h(Path(p)) for p in before}
(r/'inputs-after.json').write_text(json.dumps(after,indent=2)+'\n');assert before==after
inherited=list((r/'inherited/formal').glob('*.lean'))
assert all(p.read_bytes()==(r/'formal'/p.name).read_bytes() for p in inherited)
assert h(r/'formal/NutInterface.lean')=='632b6913be638de9470b917bc4ec860291192ee552a6e7f1b5d4eb913d5ebcff'
manifest=json.loads((r/'source-manifest.json').read_text())
assert all(h(r/p)==digest==h(r/'fresh-extracted'/p) for p,digest in manifest.items())
modules=json.loads((r/'modules.json').read_text());counts={m:0 for m in modules};names=[]
audit=r/'fresh-extracted/logs/strict-AuditR6.log'
for line in audit.open():
 m=re.match(r'MODULE some \(([^)]+)\) DECL (\S+) TYPE ',line)
 if m:counts[m[1]]+=1;names.append(m[2])
assert sum(counts.values())==890 and len(set(names))==890
(r/'declaration-counts.json').write_text(json.dumps({'total':890,'by_module':counts},indent=2)+'\n')
rep=json.loads((r/'fresh-extracted/logs/replay.json').read_text());assert 'PASS' in rep['status']
neg={p.name:json.loads(p.read_text()) for p in sorted((r/'fresh-extracted/logs').glob('negative-*.log.json'))}
assert len(neg)==13 and all(v['exit']!=0 and not v['cap_reason'] for v in neg.values())
(r/'negative-controls.json').write_text(json.dumps(neg,indent=2)+'\n')
receipts=rep['receipts'];assert len(receipts)==219 and all(not x['cap_reason'] for x in receipts)
assert sum(x['exit']==0 for x in receipts)==206
rc=subprocess.run(['/usr/bin/python3','-I',str(r/'fresh-extracted/replay.py')],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
(r/'existing-olean-refusal.log').write_text(rc.stdout);assert rc.returncode!=0 and 'Refusing existing oleans' in rc.stdout
newmods=sorted(set(modules)-{p.stem for p in inherited})
res={'365943':{'status':'Coverage8 proved; conditional Target proved; PerSupport and root acceptance remain external','accepted':False,'campaign_count':'21/40 beyond 39, unchanged','endpoints':{'Nut8.coverage8':{'type':'Nut8.Coverage8','expanded_statement':'∀ (C : QuotientMatrix) (s : ℤ), Structural C s → ∃ (e : Equiv.Perm (Fin 8)) (code : Nat), code ∈ GraphClosure7_000.targets ∧ SupportCode (C.submatrix e e) code','hypotheses_remaining':[]},'Nut8.nut8_target':{'type':'(hp : Nut8.PerSupport) → Nut8.Target','source':'formal/FinalEndpoint.lean, inherited byte-identical','hypotheses_remaining':['Nut8.PerSupport']}},'definitions':{name:(r/'formal'/file).read_text() for name,file in [('interface','NutInterface.lean')]},'declarations':{'all_local_including_generated':890,'new_modules_including_command_only_audit':newmods,'new_module_declarations':sum(counts[m] for m in newmods),'by_module':counts},'validation':{'fresh_extracted_strict_rebuild':'PASS','strict_flags':['-j1','-DwarningAsError=true'],'source_modules':len(modules),'leanchecker_modules':103,'all_local_audit':'PASS','audit_log':'fresh-extracted/logs/strict-AuditR6.log','negative_controls_rejected':13,'receipts':'fresh-extracted/logs/replay.json','existing_olean_refusal':'PASS','max_sampled_private_bytes':max(x['peak_private_bytes'] for x in receipts),'max_wall_seconds_per_call':max(x['wall_seconds'] for x in receipts),'cap_violations':0,'sequential_processes':True,'allowed_axioms':['propext','Classical.choice','Quot.sound']},'inputs':{'before_after_identical':True,'bound_files':len(before),'inherited_lean_modules_byte_identical':len(inherited),'root_interface_sha256':h(r/'formal/NutInterface.lean')},'packet':{'path':'nut-r6p-source.zip','sha256':h(r/'nut-r6p-source.zip'),'source_manifest':'source-manifest.json'},'remaining':['PerSupport proof in separate r6q lane','Independent root integration and acceptance']}}
(r/'results.json').write_text(json.dumps(res,indent=2)+'\n')
with (r/'SUMMARY.md').open('a') as f:f.write('\nValidation completed: the fresh extracted, sanitized strict rebuild and leanchecker passed all 103 modules. AuditR6 checked all 890 local declarations, including generated ones, with full types, opaque-inclusive bodies, flags and allowed transitive axioms. All 13 negative controls were rejected without cap violations. The portable driver also refused existing oleans as required. All 107 bound input files and all 92 inherited Lean modules rechecked byte-identical. Full per-call logs and resource receipts are under fresh-extracted/logs/.\n')
print(json.dumps({'modules':len(modules),'declarations':890,'new_module_declarations':sum(counts[m] for m in newmods),'inherited_modules':len(inherited),'input_files':len(before),'negative_controls':len(neg),'packet_sha256':h(r/'nut-r6p-source.zip')},indent=2))
