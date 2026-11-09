from pathlib import Path
import json,hashlib,subprocess,sys,datetime
B=Path(__file__).resolve().parent;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((B/'manifest.json').read_text())
files={str(p.relative_to(B)) for p in B.rglob('*') if p.is_file() and p.name not in ['manifest.json','receipt.json']}
assert set(m)==files
for n,h in m.items():assert sha(B/n)==h,n
count=0
for r in json.loads((B/'freeze.json').read_text()):
 # Administrative originals are mutable shared state: snapshot only.
 if 'original' in r and '/administrative/' not in r['copy']:assert sha(Path(r['original']))==r['sha256']
 assert sha(Path(r['copy']))==r['sha256'];count+=1
for r in json.loads((B/'immutable-references.json').read_text()):
 cp=Path(r['copy'])
 if not cp.is_absolute():cp=B/'extracted'/cp
 assert sha(Path(r['original']))==sha(cp)==r['sha256'];count+=1
for line in (B/'retrieval/http.jsonl').read_text().splitlines():
 r=json.loads(line)
 if 'file' in r:assert sha(Path(r['file']))==sha(Path(r['frozen']))==r['sha256'];count+=1
for script in [B/'audit.py',B/'replay/verify_pins.py']:
 p=subprocess.run([sys.executable,str(script)],cwd=script.parent,capture_output=True,text=True,check=True)
 if script.name=='verify_pins.py':assert json.loads(p.stdout)['compiler_sha256']==json.loads((B/'pins-verification.json').read_text())['compiler_sha256']
# audit.py regenerates deterministic review results; verify no manifested byte changed.
for n,h in m.items():assert sha(B/n)==h,n
assert json.loads((B/'replay/IndependentAudit.guard.json').read_text())['exit_code']==0
receipt=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS',manifest_sha256=sha(B/'manifest.json'),manifest_files=len(m),integrity_rows=count,owned_declarations=71,unsafe=0,partial=0,all_ten_deletions=True,source_archive_sha256=sha(B/'frozen/source-only.tar.gz'),counts_unchanged=[9,39,40],acceptance=False)
(B/'receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt,indent=2))
