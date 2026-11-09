import pathlib,json,hashlib,re
D=pathlib.Path(__file__).resolve().parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
r=json.loads((D/'results.json').read_text());ids=json.loads((D/'reservation.json').read_text())['ids']
assert len(r)==20 and set(map(int,r))==set(ids)
for i,o in r.items():
 p=D/'raw'/f'{i}.jsonl';assert p.read_bytes().endswith(b'\n')
 assert sha(p)==o['provenance']['raw_sha256']
 assert hashlib.sha256(o['statement'].encode()).hexdigest()==o['provenance']['statement_utf8_sha256']
 assert o['accepted_credit']==0
 for f in o['source_files']:assert sha(D/f['path'])==f['sha256']
mods=['Base']+[f'C{i}R{x}' for i in range(2) for x in range(8)]+['Certificates','Final','Semantics']
for m in mods:
 assert (D/'extracted/packet'/f'{m}.olean').exists()
 assert (D/'extracted/packet/logs'/f'check-{m}.log').exists()
 assert (D/'extracted/packet'/f'{m}.lean').read_bytes()==(D/'packet'/f'{m}.lean').read_bytes()==(D/f'{m}.lean').read_bytes()
 assert 'error:' not in (D/'extracted/packet/logs'/f'build-{m}.log').read_text()
text=(D/'extracted/packet/logs/audit.log').read_text()
assert 'AUDITED_LOCAL_DECLARATIONS 168' in text and 'sorryAx' not in text
assert 'flagged=[]' in (D/'logs/metadata-audit.log').read_text()
assert not (D/'outputs/sanitization-scan.txt').read_text()
rec=dict(result_entries=20,raw_hashes_verified=20,statement_hashes_verified=20,accepted_credit=0,candidate='346167',strict_modules=len(mods),explicit_module_checker_passes=len(mods),audited_local_declarations=168,metadata_flagged=0,extracted_replay='PASS',packet_sha256=sha(D/'lean-packet.tar.gz'),axioms=['propext','Classical.choice','Quot.sound'],limits='read-only dependency cache trusted; no full upstream rebuild; sampled RSS watchdog is not a cgroup guarantee')
(D/'outputs/final-validation.json').write_text(json.dumps(rec,indent=2)+'\n')
print(json.dumps(rec,indent=2))
