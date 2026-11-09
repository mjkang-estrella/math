from pathlib import Path
import hashlib,json,zipfile,re,importlib.util
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
M=json.loads((L/'MANIFEST.json').read_text())
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in {'MANIFEST.json','verification-receipt.json'}}
assert actual==set(M),(actual-set(M),set(M)-actual)
for n,h in M.items():assert sha(L/n)==h,n
bindings=json.loads((L/'source-bindings.json').read_text())
for b in bindings:
 assert sha(Path(b['original']))==b['sha256']==sha(L/b['copy']),b
LEAN=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
assert sha(LEAN)=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
spec=importlib.util.spec_from_file_location('pack',L/'package.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
pins=mod.checkpins();assert pins==json.loads((L/'pins.json').read_text())
assert not any(p.suffix in {'.olean','.ilean','.ir','.o','.so'} for p in L.rglob('*') if p.is_file())
with zipfile.ZipFile(L/'source-only.zip') as z:
 assert not any(n.endswith(('.olean','.ilean','.ir','.o','.so')) for n in z.namelist())
 archive=json.loads(z.read('archive-files.json'))
 for n,h in archive.items():assert hashlib.sha256(z.read(n)).hexdigest()==h==sha(L/n),n
receipt=json.loads((L/'replay-receipt.json').read_text())
assert receipt['status']=='PASS' and receipt['packet_sha256']==sha(L/'source-only.zip')
assert receipt['deterministic_diagnostics'] and len(receipt['replays'])==2
for r in receipt['replays']:
 assert r['declarations']==198 and r['transitive_safe_constants']==884
 for s in r['steps']:
  assert s['serial'] and s['reason'] is None and s['exit']==0 and s['peak_group_rss']<=2800*1024**2
  assert s['seconds']<230
audit=json.loads((L/'audit.json').read_text());assert audit['status']=='PASS' and len(audit['declarations'])==198
for d in audit['declarations']:assert not d['isUnsafe'] and set(d['axioms'])<={'propext','Classical.choice','Quot.sound'}
s=(L/'Literal.lean').read_text()
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|partial|implemented_by)\b',s)
out=dict(status='PASS',manifest_sha256=sha(L/'MANIFEST.json'),manifest_files=len(M),science_original_copy_pairs_verified=len(bindings),compiler_sha256=sha(LEAN),package_pins=pins,owned_declarations=198,transitive_safe_constants=884,source_only_archive_sha256=sha(L/'source-only.zip'),two_fresh_replays=True,owned_compiled_objects_remaining=0,mandatory_gate='INCOMPLETE: terminal uniqueness/Z(N) bridge and normalized reciprocal-type-count P_N law absent',counts_changed=False)
(L/'verification-receipt.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS manifest, all science originals/copies, nine pins, compiler, source-only archive, two replays; mandatory scope INCOMPLETE')
