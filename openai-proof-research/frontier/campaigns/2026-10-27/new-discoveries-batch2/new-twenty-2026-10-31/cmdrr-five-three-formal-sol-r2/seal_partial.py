"""Terminal manifest generator. Writes only through write_lane.py.
The manifest excludes exactly itself and this run's final receipt/log.
"""
import json,hashlib,subprocess,time
from pathlib import Path
lane=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,t):
    subprocess.run(['python3','-I','-B',str(lane/'write_lane.py'),p],input=t,text=True,check=True)
receipts=[]
for p in sorted((lane/'receipt').glob('*.json')):
    r=json.loads(p.read_text())
    receipts.append({'path':str(p.relative_to(lane)),'exit':r.get('exit'),'label':r.get('label'),'sha256':sha(p),'group_members_left':r.get('group_members_left')})
mods=['CMDRRBase','CMDRROccurrence','CMDRRCells','CMDRRTransport','CMDRRSourceTransport','CMDRRRows','CMDRRCounts','CMDRRRepeat','CMDRRSwap','CMDRRNormalize','CMDRRAudit']
latest={}
for m in mods:
    for prefix in ['lean_','leanchecker_']:
        rs=[r for r in receipts if r['label']==prefix+m]
        assert rs and rs[-1]['exit']==0,(m,prefix)
        latest[prefix+m]=rs[-1]
assert all(not r['group_members_left'] for r in receipts)
replay=json.loads((lane/'results/PARTIAL-REPLAY.json').read_text())
assert all(c['exit']==0 for c in replay['commands'])
unpaid=[
'Explicit canonical Fin5 matching and full Source equivalence/normalization assembly (synchronized Fin3+Fin2 labels are proved).',
'Derived unique-other-single repeat multiplicities.',
'Row restrictions, orbit partitions and spouse four-cycle classification.',
'Complementary-edge degree lemma and occurrence A/B/z definitions/incidence sums; A+B=1+z.',
'Single-row 3+2 elimination: A=0, B=2-z, contradiction2z=1, and five-cycle classification.',
'Application of entire cycle/incidence argument to columns with permutation correspondence (Source.swap itself is proved).',
'Cycle/support signs, T eleven-two-orbit sign, parity contradiction and universal noCMDRR endpoint.',
'Complete transitive body-origin dependency DAG and exact final-endpoint closures (229 production declarations and transitive axiom audits are paid).',
'Substantive positive source controls and semantic mutation negative controls.',
'Full finished manuscript PDF and all-page visual inspection.',
'Independent full formal/source/proof/manuscript review and root acceptance.'
]
report={'mathdb_id':326555,'status':'PARTIAL_NOT_TECHNICAL_PASS','credit':0,'campaign_accepted_new':55,'campaign_target':60,'previous_accepted':39,'endpoint_present':False,'production_modules':mods[:-1],'audit_module':mods[-1],'production_declarations_enumerated':229,'axioms_allowed':['propext','Classical.choice','Quot.sound'],'axiom_audit_scope':'All229production declarations, transitive axioms; direct dependencies printed; complete body-origin DAG unpaid','latest_real_exits':latest,'replay':'results/PARTIAL-REPLAY.json','replay_scope':'PARTIAL_ONLY','unpaid':unpaid,'prior_limit':'Unread2013companion403; no worldwide novelty claim','process_deviations':['Direct own-log retrieval with cat/sed outside runner for tool display','Direct check.sh invocation failed126 before bash correction','Empty-source writer refused1, preserving original source','Unbound PACKAGES_ROOT shell failure1 before subprocess'],'source_hashes_after_checker':replay['source_hashes_after_checker']}
write('results/326555.json',json.dumps(report,indent=2)+'\n')
summary='# Incomplete CMDRR(5,3) formalization\n\nCredit0; campaign55/60 beyond39prior unchanged. No nonexistence endpoint is present.\n\nTen production modules plus audit pass strict Lean and leanchecker. Proved: literal unordered occurrence model, injectivity/count bridges22/11, actual T/U/C permutations and C(Tx)=Ux, arbitrary relabel/source preservation, synchronized spouse labels Fin3+Fin2, full source sex-swap, and row-two-cycle repeated-single restriction.\n\n229production declarations enumerated including generated/private by module origin; each transitive axiom audit allows only propext/Classical.choice/Quot.sound. Direct dependency lists are printed. Complete body-origin DAG is unpaid.\n\nFresh source-only partial rebuild/checker from an empty build passed, with source hashes checked afterward. See results/PARTIAL-REPLAY.json and receipt/1794116778439418167_extracted-partial-replay.json(exit0).\n\nUnpaid obligations:\n\n'+''.join('- '+x+'\n' for x in unpaid)+'\nSee PARTIAL-MANUSCRIPT.md for source mapping, ordinary argument, exact gaps and procedural/scientific limits. This is a partial handback, not a claimed complete implementation or mathematical obstruction to completing it.\n'
write('SUMMARY.md',summary)
write('CHECKPOINT.md',summary+'\nLatest paid strict audit: receipt/1794116709248719970_lean_CMDRRAudit.json(exit0). All11module leanchecker exits0; exact latest receipts in results/326555.json. Previous failed receipts remain nonpass. Pins matched. All observed completed runner groups empty; RSS is sampled, not perfect cgroup enforcement. Direct log-retrieval and shell/writer failures disclosed in report.\n')
files=[p for p in sorted(lane.rglob('*')) if p.is_file()]
assert all(not p.is_symlink() for p in files)
current=[p for p in files if p.parent==lane/'logs' and p.name.endswith('_seal-partial.log')]
assert len(current)==1,current
terminal=current[0]
exclusions=['SHA256-MANIFEST.json',str(terminal.relative_to(lane)),str((lane/'receipt'/(terminal.stem+'.json')).relative_to(lane))]
inventory={'completed_receipts':receipts,'latest_real_exits':latest,'manifest_exact_self_exclusions':exclusions,'scope':'PARTIAL_ONLY','receipt_count':len(receipts),'receipt_exit_counts':{str(x):sum(r['exit']==x for r in receipts) for x in sorted(set(r['exit'] for r in receipts),key=str)},'files_before_terminal_manifest':[str(p.relative_to(lane)) for p in files]}
write('results/INVENTORY.json',json.dumps(inventory,indent=2)+'\n')
entries={str(p.relative_to(lane)):sha(p) for p in sorted(lane.rglob('*')) if p.is_file() and str(p.relative_to(lane)) not in exclusions}
manifest={'scope':'PARTIAL_NOT_TECHNICAL_PASS','sha256':entries,'exact_self_exclusions':exclusions}
write('SHA256-MANIFEST.json',json.dumps(manifest,indent=2)+'\n')
print('SEALED_PARTIAL_FILES',len(entries),'COMPLETED_RECEIPTS',len(receipts),flush=True)
print('MANIFEST_SHA256',sha(lane/'SHA256-MANIFEST.json'),flush=True)
print('RESULT_SHA256',sha(lane/'results/326555.json'),flush=True)
print('LAST_REPLAY_EXIT',0,'ALL_CURRENT_STRICT_AND_CHECKER_EXITS',0,flush=True)
print('EXCLUSIONS',json.dumps(exclusions),flush=True)
