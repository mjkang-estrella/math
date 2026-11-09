from pathlib import Path
import json,hashlib,re,zipfile,os
root=Path(__file__).resolve().parents[1];os.chdir(root)
replay=json.loads(Path('extracted/replay-receipt.json').read_text());neg=json.loads(Path('negative-controls/results.json').read_text())
assert replay['passed'] and neg['passed']
audit=Path('extracted/logs/replay-Audit.log').read_text();total=int(re.search(r'TOTAL_LOCAL_DECLARATIONS (\d+)',audit)[1])
counts={m:len(re.findall('MODULE '+m+'\\n',audit)) for m in ['Definitions','Concrete','Canonical','Separation','Invariance']};assert sum(counts.values())==total
# Identity of all formal sources and the portable replay implementation to the clean extraction.
identity={}
for p in [*sorted(Path('formal').glob('*.lean')),Path('scripts/replay.py'),Path('scripts/watchdog.py')]:
 h=hashlib.sha256(p.read_bytes()).hexdigest();assert h==hashlib.sha256((Path('extracted')/p).read_bytes()).hexdigest();identity[str(p)]=h
before=json.loads(Path('inputs-before.json').read_text());after=[]
for x in before:
 h=hashlib.sha256(Path(x['source']).read_bytes()).hexdigest();c=hashlib.sha256(Path(x['copy']).read_bytes()).hexdigest();assert h==c==x['sha256'];after.append(dict(source=x['source'],sha256=h,copy_sha256=c,unchanged=True))
Path('inputs-after.json').write_text(json.dumps(after,indent=2)+'\n')
result={'342414':{'status':'PARTIAL_ZERO_CREDIT','full_literal_endpoint':None,'refutation_proved':False,'root_accepted':False,'credit':0,'prior_art_gate':'No prior refutation located in bounded screen; limitations remain','universal_arbitrary_tree_bound_proved':False,'declarations':{'total_including_generated':total,'by_module':counts},'partial_endpoints':{'EdgePattern.Concrete.maxima_eq':'maxima graph = listed (the five specified sets)','EdgePattern.Concrete.occupancy_values':'occupancy 0 = 2/5 and occupancy 1 = 14/5 and occupancy 2 = 4/5, for supplied layer subsets only','EdgePattern.Concrete.separating_value':'sum_i alpha_i occupancy_i = 67027/67500','EdgePattern.Concrete.separating_lt_one':'sum_i alpha_i occupancy_i < 1','EdgePattern.Canonical.all_81':'forall a b c d : Fin 3, summary.count > 0 and 27*summary.count <= summary.weight; arithmetic only','EdgePattern.independent_map_iff':'independent sets preserved and reflected by arbitrary graph isomorphisms','EdgePattern.maximum_map_iff':'maximum independent sets preserved and reflected by arbitrary graph isomorphisms','EdgePattern.finite_separation':'positive rational test with witness < 1 and all family members >= 1 excludes every finite real convex combination'},'verification':{'strict_fresh_replay':True,'leanchecker_all_five_modules':True,'audit_all_local_declarations':True,'negative_controls':True,'allowed_axioms':['propext','Classical.choice','Quot.sound'],'receipt':'extracted/replay-receipt.json','audit_log':'extracted/logs/replay-Audit.log','negative_controls_log':'negative-controls/results.json'},'gaps':'GAPS.md','source_correspondence':'statement-correspondence.md','packet':'edgepattern-partial-source.zip','inputs_unchanged':True,'no_child_agents':True,'no_git':True,'no_shared_ledger_edits':True}}
Path('results.json').write_text(json.dumps(result,indent=2)+'\n')
Path('SUMMARY.md').write_text(Path('SUMMARY.md').read_text()+f'\nValidation result: strict fresh replay, all five leanchecker module checks, full audit of {total} local declarations including generated declarations, and all four negative controls passed. Only propext, Classical.choice and Quot.sound occur in transitive dependencies. These checks certify the partial statements only.\n')
Path('verification.json').write_text(json.dumps({'replay':replay,'negative_controls':neg,'audit_counts':counts,'total':total,'fresh_source_identity':identity},indent=2)+'\n')
files=[*Path('formal').glob('*.lean'),Path('scripts/replay.py'),Path('scripts/watchdog.py'),*[Path(x) for x in ['SUMMARY.md','GAPS.md','PRIOR-ART.md','PRIOR-ART.json','REPRODUCE.md','statement-correspondence.md','inputs-before.json','inputs-after.json','formal-source-hashes.json','verification.json','results.json']],*Path('negative-controls').glob('*.lean')]
with zipfile.ZipFile('edgepattern-partial-source.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in files:z.write(p,p.as_posix())
 z.write('extracted/replay-receipt.json','evidence/replay-receipt.json')
 for p in Path('extracted/logs').glob('*'):z.write(p,'evidence/'+p.name)
 for p in Path('negative-controls').glob('*.log*'):z.write(p,'evidence/negative-'+p.name)
 z.write('negative-controls/results.json','evidence/negative-results.json')
 assert not any(x.endswith(('.olean','.ilean','.ir')) for x in z.namelist())
Path('packet-receipt.json').write_text(json.dumps({'packet':'edgepattern-partial-source.zip','sha256':hashlib.sha256(Path('edgepattern-partial-source.zip').read_bytes()).hexdigest(),'source_only':True,'all_proof_sources_and_replay_driver_identical_to_successful_fresh_replay':True,'source_hashes':identity},indent=2)+'\n')
print(json.dumps({'status':'PARTIAL_ZERO_CREDIT','declarations':total,'audit_counts':counts,'packet_bytes':Path('edgepattern-partial-source.zip').stat().st_size}))
