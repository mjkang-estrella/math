from pathlib import Path
import json,hashlib
root=Path(__file__).resolve().parent.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
mods=(root/'module-order.txt').read_text().splitlines()
status=(root/'logs/replay-fresh/status.txt').read_text().splitlines()
assert status==[f'{m} {stage} PASS' for m in mods for stage in ('build','leanchecker')]
axioms=(root/'logs/replay-fresh/AllAxioms.build.log').read_text()
for name in ('conjecture_false','conjectureLinear_false'):
    assert f"'MathDB356266.{name}' depends on axioms: [propext, Classical.choice, Quot.sound]" in axioms
assert 'AXIOM AUDIT PASSED: 23 declarations' in axioms
for m in mods:
    assert not (root/f'logs/replay-fresh/{m}.leanchecker.log').read_text()
    assert sha(root/f'src/{m}.lean')==sha(root/f'replay-fresh/{m}.lean')
inputs=[root.parent/'hurlbert-root-ruling-r1.json',root.parent/'hurlbert-review-r1/REVIEW.md',root.parent/'expanded-corpus-r234/lean/Hurlbert.lean',root.parent/'expanded-corpus-r234/sources/chung-1992.txt',root.parent/'expanded-corpus-r234/sources/356266.txt',root.parent/'expanded-corpus-r234/raw/356266.jsonl']
(root/'inputs.sha256').write_text(''.join(f'{sha(p)}  {p}\n' for p in inputs))
r={
 'mathdb_id':356266,'lane':'hurlbert-formal-r1','status':'FORMALIZATION_COMPLETE_FOR_ROOT_REVIEW','accepted':False,'credit_awarded':0,
 'endpoints':{f'MathDB356266.{n}':{'type':t,'axioms':['propext','Classical.choice','Quot.sound']} for n,t in [('conjecture_false','¬ Conjecture'),('conjectureLinear_false','¬ ConjectureLinear')]},
 'positive_control':{'printed_word':'123412534153214532413254','word_type':'Fin 24 → Fin 6','theorems':['MathDB356266.cdg_euler','MathDB356266.cdg_realizes'],'proof_method':'decide'},
 'length_requirement':'Authorized documentation alternative: explicit bijection from Fin (N+1) to subtype of permutations; see STATEMENT-CORRESPONDENCE.md. No separate Lean factorial theorem claimed.',
 'lean_version':'4.34.1','mathlib_revision':'d13f23b723b8a846827a245b89c10fc7d3f11612','trust_scope':'Supplied prebuilt upstream oleans; upstream not rebuilt',
 'replay':{'fresh_extraction':'replay-fresh','modules':mods,'strict_builds':'PASS','explicit_module_leanchecker':'PASS for all 5 modules','source_scan':'PASS','metadata_audit':'PASS, 23 declarations','transitive_axiom_audit':'PASS, 23 declarations','logs':'logs/replay-fresh'},
 'resource_limits':{'rss_watchdog_bytes':6*1024**3,'cpu_seconds':120,'wall_seconds':140,'termination_grace_seconds':2,'affinity_cpu_count':2,'lean_memory_flag':'-M3500','MALLOC_ARENA_MAX':2,'heavy_concurrency':1,'python_flags':['-I','-B'],'temporary_and_cache_paths':'lane-local'},
 'original_hurlbert_sha256':sha(root/'src/Hurlbert.lean'),'archive_sha256':sha(root/'proof-source.zip'),
 'provenance':'Existing root ruling and independent review read; no new prior-art clearance claimed',
 'development_failures':'Corrected style warning and audit elaboration errors retained in logs/dev-*.log; no cap increases',
 'constraints':{'network_used':False,'git_used':False,'child_agents':False,'other_lanes_modified':False,'ledger_modified':False,'background_work_remaining':False},
}
(root/'results.json').write_text(json.dumps(r,indent=2)+'\n')
paths=[root/'proof-source.zip',root/'module-order.txt',root/'results.json',*(root/'src').glob('*.lean'),*(root/'scripts').glob('*'),root/'SUMMARY.md',root/'PROOF.md',root/'STATEMENT-CORRESPONDENCE.md',root/'REPRODUCE.md']
(root/'outputs.sha256').write_text(''.join(f'{sha(p)}  {p.relative_to(root)}\n' for p in sorted(paths)))
print('Verified all replay outcomes and wrote results.json, inputs.sha256, outputs.sha256')
