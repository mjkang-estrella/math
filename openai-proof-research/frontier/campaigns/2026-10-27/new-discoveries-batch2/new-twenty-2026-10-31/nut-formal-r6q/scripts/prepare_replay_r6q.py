from pathlib import Path
import json,re
r=Path(__file__).resolve().parents[1]
inherited=json.loads((r/'inputs/modules.json').read_text());certs=json.loads((r/'new-certificate-modules.json').read_text());new=['SignedEnumeration','SignedCatalogue']+certs+json.loads((r/'support-modules.json').read_text())+['PerSupport']
template=(r/'formal/AuditR5.lean').read_text();tail=template[template.index('set_option pp.all true'):]
audits=[]
for k,start in enumerate(range(0,len(new),12)):
 group=new[start:start+12];name=f'AuditR6_{k:03}';audits.append(name)
 body=re.sub(r'#\[`Nut, .*?\]\.contains m', '#['+', '.join('`'+m for m in group)+'].contains m', tail)
 (r/'formal'/(name+'.lean')).write_text('\n'.join('import '+m for m in group)+'\n'+body)
(r/'modules.json').write_text(json.dumps(inherited+new+audits,indent=2)+'\n')
s=(r/'inputs/replay.py').read_text().replace('scripts/run_capped.py','scripts/capped_r6q.py').replace('PASS PARTIAL r5q PACKET ONLY','PASS r6q PER_SUPPORT PACKET').replace('PASS: INCOMPLETE r5q packet strict rebuild, leanchecker, full audit and rejected negative controls.','PASS: r6q PerSupport strict rebuild, leanchecker, full audit and rejected negative controls.')
s=s.replace("for name,source in controls.items():",'''controls['WrongSharedSemiSign'] = 'import SignedEnumeration\\nexample : Nut8.signedRepresentative (fun _ _ => (1 : ℤ)) (-1) ∅ 0 0 = 1 := by\\n  decide +kernel\\n'
controls['NegativeTreeSlot'] = 'import SignedEnumeration\\nexample : ((0,1) : Fin 8 × Fin 8) ∈ Nut8.signSlots (fun _ _ => (1 : ℤ)) (fun _ => 0) := by\\n  decide +kernel\\n'
for name,source in controls.items():''')
s=s.replace("for mod in json.loads", " (root/'logs/replay-progress.json').write_text(json.dumps({'status':'IN_PROGRESS','receipts':receipts},indent=2)+'\\n')\n print('REPLAY '+label,flush=True)\nfor mod in json.loads")
(r/'replay.py').write_text(s)
print('Replay modules',len(inherited+new+audits),'new audits',len(audits))
