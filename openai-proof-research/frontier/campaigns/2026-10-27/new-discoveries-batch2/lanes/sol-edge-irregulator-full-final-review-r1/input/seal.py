from pathlib import Path
import json,hashlib,shutil
L=Path(__file__).resolve().parent;P=L/'packet'
p=P/'provenance.json';r=json.loads(p.read_text());r['failures'].append('Own initial helper supervisors were copied verbatim from the inherited upper guard: payload AS/CPU and monitored group RSS/wall were capped, but supervisor self AS/CPU/alarm were not explicitly set. Self limits were added before packaging and both fresh replays; earlier supervisor self-limit compliance is not claimed.')
v=json.loads((L/'verification-fresh/verification-receipt.json').read_text());r['initial_fresh_implementation_replay']={'archive_sha256':v['archive_sha256'],'unique_declarations':v['declaration_count'],'peak_lean_group_rss_kib':max(x['peak_group_rss_kib'] for x in v['steps']),'peak_helper_group_rss_bytes':250392576,'pdf_and_zip_byte_identical':True,'audit_logs_byte_identical':True,'binary_and_nine_pins_and_dependency_hashes_checked':True,'own_initial_prebuilt_artifacts':0,'receipt_sha256':hashlib.sha256((L/'verification-fresh/verification-receipt.json').read_bytes()).hexdigest()}
p.write_text(json.dumps(r,indent=2)+'\n')
(P/'evidence/replay').mkdir(exist_ok=True);shutil.copyfile(L/'verification-fresh/verification-receipt.json',P/'evidence/replay/initial-verification-receipt.json');shutil.copyfile(L/'fresh-helper.log',P/'evidence/replay/initial-helper.log')
# Source manifest seals selected source artifacts only, never build/cache products.
m=json.loads((P/'manifest.json').read_text())
for f in [p,P/'evidence/replay/initial-verification-receipt.json',P/'evidence/replay/initial-helper.log']:
 m[str(f.relative_to(P))]=hashlib.sha256(f.read_bytes()).hexdigest()
(P/'manifest.json').write_text(json.dumps(dict(sorted(m.items())),indent=2)+'\n')
