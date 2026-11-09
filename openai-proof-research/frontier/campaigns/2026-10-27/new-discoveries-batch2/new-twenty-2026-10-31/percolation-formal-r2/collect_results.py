import hashlib,json,sys,zipfile
from pathlib import Path
root=Path(sys.argv[1]).resolve()
fresh=root/'fresh-extracted'
modules=(fresh/'module-order.txt').read_text().splitlines()
def metrics(path):
    return {k:float(v) for k,v in (token.split('=',1) for token in path.read_text().split())}
rows=[]
for mod in modules:
    if not (fresh/'logs'/f'{mod}.ok').is_file():
        raise RuntimeError(f'Missing success stamp {mod}')
    rows.append({'module':mod,'compiler':metrics(fresh/'logs'/f'{mod}.time'),
                 'checker':metrics(fresh/'logs'/f'{mod}.check.time'),
                 'compiler_success':True,'explicit_module_checker_success':True})
for name in ['Closure','FiniteSystem','TruthTableCNF','PG5CNF']:
    if not (fresh/'build'/f'{name}.olean').exists(): raise RuntimeError(name)
scan=json.loads((fresh/'logs/source-scan.json').read_text())
audit=(fresh/'logs/Audit.lean.log').read_text()
if 'passed' not in audit or scan['forbidden_source_tokens']: raise RuntimeError('audit')
with zipfile.ZipFile(root.parent/'percolation-formal-r1/source-only.zip') as prev:
    unchanged=[]
    for mod in modules:
        name=f'src/{mod}.lean'
        if name in prev.namelist() and mod!='Audit':
            if (fresh/name).read_bytes()!=prev.read(name): raise RuntimeError(f'Changed inherited {mod}')
            unchanged.append(mod)
report={'status':'partial_conditional_not_accepted', 'module_count':len(modules),
 'endpoint':'Percolation.not_conjecture20_generated',
 'statement':'Percolation.GeneratedCNFUnsat5 -> not Percolation.Conjecture20',
 'remaining_props':['Percolation.GeneratedCNFUnsat5'],
 'remaining_prop_definition':'not exists val : SatVar -> Bool, forall c in inputCNF5, CNF.Holds val c',
 'unconditional_endpoint_proved':False,
 'new_closed_modules':['Closure','FiniteSystem','TruthTableCNF','PG5CNF'],
 'input_clause_semantic_bridge':'proved for every clause of new Lean-side unnormalized inputCNF5',
 'normalization_proved':False,'rup_soundness_proved':False,'certificate_additions_replayed':0,
 'certificate_throughput':None,
 'allowed_endpoint_axioms':['propext','Classical.choice','Quot.sound'],
 'axiom_log':'fresh-extracted/logs/PG5CNF.lean.log',
 'metadata_audit':audit.strip(),'source_scan':scan,
 'inherited_byte_identical_modules':unchanged,
 'fresh_replay':{'compiler_all_success':True,'checker_all_success':True,
   'compiler_total_wall_seconds':round(sum(r['compiler']['wall_seconds'] for r in rows),2),
   'checker_total_wall_seconds':round(sum(r['checker']['wall_seconds'] for r in rows),2),
   'longest_process_wall_seconds':max(r[k]['wall_seconds'] for r in rows for k in ['compiler','checker']),
   'max_peak_rss_kib':max(r[k]['peak_rss_kib'] for r in rows for k in ['compiler','checker']),
   'modules':rows},
 'archive_sha256':hashlib.sha256((root/'source-only.zip').read_bytes()).hexdigest(),
 'source_archive':'source-only.zip',
 'limits':{'cpus':[0,1],'cpu_seconds':120,'wall_seconds':140,'rss_watchdog_gib':6,'lean_M_mb':3500,'malloc_arena_max':2},
 'resource_disclosure':'One development TruthTableCNF pilot briefly overlapped inherited-dependency build. Final fresh replay strictly serial; no limits raised.',
 'acceptance':'Root alone decides. No credit claimed.'}
(root/'results.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:report['fresh_replay'][k] for k in ['compiler_total_wall_seconds','checker_total_wall_seconds','longest_process_wall_seconds','max_peak_rss_kib']},indent=2))
