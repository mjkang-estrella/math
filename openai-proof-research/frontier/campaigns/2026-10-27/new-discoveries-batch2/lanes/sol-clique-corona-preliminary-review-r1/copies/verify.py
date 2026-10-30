from pathlib import Path
import hashlib,json,subprocess,sys,datetime
L=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def check_manifest(name):
 j=json.loads((L/name).read_text());bad=[n for n,h in j['files'].items() if not (L/n).is_file() or sha(L/n)!=h];assert not bad,(name,bad);return len(j['files'])
a=check_manifest('finalmanifest.json');b=check_manifest('scientific-freeze.json')
old=sha(L/'checks.json');p=subprocess.run([sys.executable,str(L/'checks.py')],capture_output=True,text=True,timeout=60);assert p.returncode==0,p.stderr;assert sha(L/'checks.json')==old
for name in ['corona.pdf','chord.pdf','chord-published.pdf','corona-companion.pdf','original-corona.pdf']:
 assert (L/'sources'/name).read_bytes().startswith(b'%PDF')
pro=json.loads((L/'provenance.json').read_text())
assert sha(Path(pro['guard']['path']))==pro['guard']['sha256']
for x in pro['inherited_registry_inputs']:assert sha(Path(x['path']))==x['sha256']
assert not list(L.rglob('*.lean')) and not list(L.rglob('*.tex'))
assert a==check_manifest('finalmanifest.json') and b==check_manifest('scientific-freeze.json')
j=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS',finalmanifest_sha256=sha(L/'finalmanifest.json'),scientific_freeze_sha256=sha(L/'scientific-freeze.json'),manifest_entries=a,scientific_entries=b,checks_replay='PASS; checks.json byte-identical',source_pdf_headers='PASS',external_baseline_hashes='PASS',unchanged_guard='PASS',eligibility='HOLD',limitations='hashes and arithmetic replay do not constitute independent mathematical/novelty review')
(L/'manifest-verification.json').write_text(json.dumps(j,indent=2)+'\n');print(json.dumps(j,indent=2))
