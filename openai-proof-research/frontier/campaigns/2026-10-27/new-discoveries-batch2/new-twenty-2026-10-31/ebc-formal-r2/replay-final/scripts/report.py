from pathlib import Path
import hashlib, json, re, zipfile
lane = Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ebc-formal-r2')
sha = lambda b: hashlib.sha256(b).hexdigest()
mods = (lane/'module-order.txt').read_text().split()
forbidden = r'\b(?:sorry|admit|axiom|unsafe|partial|native_decide|ofReduceBool|bv_decide|implemented_by|extern)\b|_unsafe_rec'
scan = {}
for p in sorted((lane/'src').glob('*.lean')):
    s = p.read_text()
    s = re.sub(r'/\*.*?\*/|/-.*?-/', '', s, flags=re.S)
    s = re.sub(r'--[^\n]*|"(?:\\.|[^"\\])*"', '', s)
    scan[p.name] = re.findall(forbidden, s)
source_ok = not any(scan.values())
(lane/'logs/source-scan.json').write_text(json.dumps({'pass': source_ok, 'matches':scan}, indent=2)+'\n')
with zipfile.ZipFile(lane/'round1-source.zip') as old:
    unchanged = {n: old.read(n)==(lane/n).read_bytes() for n in old.namelist()
                 if n.startswith('src/') and n != 'src/Audit.lean'}
with zipfile.ZipFile(lane/'source-only.zip') as z:
    safe = all(not Path(n).is_absolute() and '..' not in Path(n).parts and not n.endswith('.olean')
               and ((z.getinfo(n).external_attr >> 16) & 0o170000) != 0o120000 for n in z.namelist())
    archive_matches = all(z.read('src/'+m+'.lean')==(lane/'src'/f'{m}.lean').read_bytes() for m in mods)
replay = lane/'replay-final'
checks = {m:{'strict_compile':(replay/'logs'/f'{m}.PASS').is_file(),
             'explicit_module_leanchecker':(replay/'logs'/f'{m}.PASS').is_file(),
             'compile_log':str(replay/'logs'/f'{m}.lean.log'),
             'checker_log':str(replay/'logs'/f'{m}.checker.log')} for m in mods}
audit = (replay/'logs/Audit.lean.log').read_text() if (replay/'logs/Audit.lean.log').exists() else ''
metadata = 'AUDIT PASS:' in audit and checks['Audit']['strict_compile']
endpoint = re.search(r"'EBC337062\.conjecture21_false_unconditional' depends on axioms:\s*\[([^]]*)\]", audit)
axioms = [s.strip() for s in endpoint.group(1).split(',')] if endpoint else None
axiom_ok = axioms is not None and set(axioms) <= {'propext','Classical.choice','Quot.sound'}
result = {'endpoint':'EBC337062.conjecture21_false_unconditional', 'statement':'¬ EBC337062.Conjecture21',
 'status':'unconditional', 'remaining_props':[], 'module_count':len(mods), 'modules':checks,
 'source_only_zip_sha256':sha((lane/'source-only.zip').read_bytes()),
 'round1_source_zip_sha256':sha((lane/'round1-source.zip').read_bytes()),
 'unchanged_round1_sources_except_audit':unchanged, 'all_round1_definitions_byte_identical':all(unchanged.values()),
 'archive_paths_safe':safe,'archive_sources_match':archive_matches,'source_scan_pass':source_ok,
 'metadata_audit_pass':metadata,'endpoint_axioms':axioms,'endpoint_axioms_pass':axiom_ok,
 'source_sha256':{p.name:sha(p.read_bytes()) for p in sorted((lane/'src').glob('*.lean'))},
 'control':'Original unconditional C_2 control retained; optional C_21 control omitted',
 'acceptance_claimed':False}
result['all_checks_pass'] = all(c['strict_compile'] and c['explicit_module_leanchecker'] for c in checks.values()) and all(unchanged.values()) and safe and archive_matches and source_ok and metadata and axiom_ok
(lane/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['endpoint','status','module_count','endpoint_axioms','all_checks_pass']},indent=2))
raise SystemExit(0 if result['all_checks_pass'] else 1)
