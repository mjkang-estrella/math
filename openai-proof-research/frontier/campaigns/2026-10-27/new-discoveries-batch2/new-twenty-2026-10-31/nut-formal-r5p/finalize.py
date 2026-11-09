from pathlib import Path
import json,hashlib,re
r=Path(__file__).resolve().parent; base=r.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
combined={}
for name in ['inputs-before','additional-inputs-before']:
 before=json.loads((r/(name+'.json')).read_text())
 after={k:sha(base/k) for k in before}
 assert before==after
 for k,h in before.items():assert sha(r/'inputs'/k)==h
 (r/(name.replace('before','after')+'.json')).write_text(json.dumps(after,indent=2)+'\n')
 combined.update(after)
for p in (base/'nut-formal-r4b/formal').glob('*.lean'):assert sha(p)==sha(r/'formal'/p.name)
for p in (base/'nut-formal-r4a/formal').glob('*.lean'):assert sha(p)==sha(r/'formal'/p.name)
assert sha(base/'nut-interface-r5/NutInterface.lean')==sha(r/'formal/NutInterface.lean')
replay=json.loads((r/'fresh-extracted/logs/replay.json').read_text());receipts=replay['receipts']
audit=(r/'fresh-extracted/logs/strict-AuditAll.log').read_text()
total=int(re.search(r'LOCAL_TOTAL (\d+)',audit).group(1))
counts={}
for m,n in re.findall(r'MODULE (.*?) DECL (\S+) TYPE',audit):counts[m]=counts.get(m,0)+1
assert sum(counts.values())==total
newmods=['BitEncoding','RowEncoding','ExtensionEncoding','TransportedNeighbors','CatalogueGraph']+[f'CatalogueSimple{k}' for k in range(1,9)]+['FiniteOfParts','EndpointOfParts']
newcounts={k:v for k,v in counts.items() if any(k==f'some ({m})' for m in newmods)}
(r/'declaration-counts.json').write_text(json.dumps({'total':total,'by_module':counts,'new_by_module':newcounts},indent=2)+'\n')
result={'365943':{'status':'partial_zero_credit','acceptance_claimed':False,'coverage8_proved':False,'finite_obstruction_proved':False,'unconditional_target_proved':False,'frozen_interface_changed':False,'bound_input_files':len(combined),'inherited_r4b_source_files':len(list((base/'nut-formal-r4b/formal').glob('*.lean'))),'inherited_r4a_sources_compatible':True,'new_proof_modules':newmods,'endpoints':{'Nut8.coverage8':'ABSENT','Nut8.finite_of_parts':'(hc : Nut8.Coverage8) → (hp : Nut8.PerSupport) → Nut8.FiniteObstruction','Nut8.target_of_parts':'(hc : Nut8.Coverage8) → (hp : Nut8.PerSupport) → Nut8.Target','Nut8.nut8_target':'SOURCE ONLY; conditional module skipped because Coverage8.lean is absent','Nut8.endpoint_of_finite':'Nut8.FiniteObstruction → Nut8.Target (inherited r4a)'},'validation':{'status':replay['status'],'packet_checks':json.loads((r/'packet-checks.json').read_text()),'compiled_modules':len(json.loads((r/'modules.json').read_text())),'leanchecker_calls':sum('leanchecker' in x['command'][0] for x in receipts),'audited_local_declarations':total,'new_local_declarations_including_generated':sum(newcounts.values()),'new_declarations_by_module':newcounts,'negative_controls_rejected':sum('negative-' in str(x['command']) or '/tmp/' in str(x['command']) for x in receipts),'capped_calls':len(receipts),'peak_sampled_private_bytes':max(x['peak_private_bytes'] for x in receipts),'cap_violations':sum(x['cap_reason'] is not None for x in receipts),'summed_call_wall_seconds':sum(x['wall_seconds'] for x in receipts)},'remaining':['eligible transported neighbour masks, including strict deletion degree and graphDegree correspondence','one-vertex base and catalogue induction through eight vertices','specialization to Structural matrices and SupportCode permutation','FinalEndpoint strict compilation and audit after Coverage8 exists'],'resource_deviation':'Two capped development Lean calls briefly overlapped; final fresh replay sequential.','packet':'nut-r5p-source.zip','packet_sha256':sha(r/'nut-r5p-source.zip'),'counts_changed':False}}
(r/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
