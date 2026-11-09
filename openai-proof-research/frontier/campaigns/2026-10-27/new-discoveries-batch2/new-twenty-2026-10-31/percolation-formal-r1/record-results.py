import sys,json,re,hashlib
from pathlib import Path
root=Path(sys.argv[1]).resolve()
replay=root/'fresh-extracted'
mods=(root/'module-order.txt').read_text().splitlines()
records=[]
for m in mods:
    row={'module':m,'passed':(replay/f'logs/{m}.ok').exists()}
    for suffix,label in [('time','lean'),('check.time','leanchecker')]:
        p=replay/f'logs/{m}.{suffix}'
        if p.exists():
            row[label]={k:float(v) for k,v in re.findall(r'(wall_seconds|peak_rss_kib)=([0-9.]+)',p.read_text())}
    records.append(row)
assert all(r['passed'] for r in records)
for p in (root/'src').glob('*.lean'):
    assert p.read_bytes()==(replay/'src'/p.name).read_bytes()
result={
 'mathdb_id':333709,'status':'conditional','accepted':False,
 'endpoint':'Percolation.not_conjecture20',
 'statement':'Percolation.NoMinimalTwoRound5 → ¬ Percolation.Conjecture20',
 'remaining_props':{'Percolation.NoMinimalTwoRound5':'¬ ∃ a : Infection 5, Minimal PG5 5 a ∧ TimeIs PG5 5 a 2'},
 'closed':['general definitions and least-time characterization','PG5 projective plane and modulo-5 dot-product incidence','minimal threshold-4 time-2 control','minimal threshold-5 time-3 control','fixed-separator soundness','no full initial line in a minimal threshold-5 set'],
 'not_completed':['finite nonexistence proof','CNF completeness bridge','projective normalization','proved certificate checker and kernel UNSAT replay'],
 'toolchain':'Lean 4.34.1 bundled Std; no mathlib dependency',
 'resources':{'rss_limit_gib':6,'lean_heap_M':3500,'cpus':[0,1],'cpu_seconds':120,'wall_seconds':140,'MALLOC_ARENA_MAX':2},
 'fresh_extraction':str(replay),'source_matches_archive_extraction':True,
 'module_count':len(mods),'all_lean_and_explicit_module_leanchecker_passed':True,
 'endpoint_axioms':['propext'], 'control_axioms':['propext','Classical.choice','Quot.sound'],
 'metadata_audit':(replay/'logs/Audit.lean.log').read_text().strip(),
 'source_scan':json.loads((root/'logs/source-scan.json').read_text()),
 'modules':records,
 'lean_total_wall_seconds':sum(r['lean']['wall_seconds'] for r in records),
 'checker_total_wall_seconds':sum(r['leanchecker']['wall_seconds'] for r in records)
}
(root/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['status','module_count','lean_total_wall_seconds','checker_total_wall_seconds','metadata_audit']},indent=2))
