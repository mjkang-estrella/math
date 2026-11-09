from pathlib import Path
import hashlib,json,shutil,subprocess,sys,zipfile,datetime
w=Path(__file__).resolve().parent;x=w/'fresh-extract'
receipt=json.loads((x/'replay-receipt.json').read_text())
assert receipt['status']=='PASS_FULL_LEAN_ENDPOINT'
for f,h in receipt['source_hashes'].items():
 assert hashlib.sha256((w/f).read_bytes()).hexdigest()==h
 assert (w/f).read_bytes()==(x/f).read_bytes()
shutil.copyfile(x/'replay-receipt.json',w/'replay-receipt.json')
b=json.loads((w/'input-bindings.json').read_text())
v={p:{'expected':h,'actual':hashlib.sha256(Path(p).read_bytes()).hexdigest()} for p,h in b.items()}
assert all(d['expected']==d['actual'] for d in v.values())
(w/'input-verification-after.json').write_text(json.dumps(v,indent=2))
r=json.loads((w/'results.json').read_text());r.update(status='FULL_LEAN_ENDPOINT_STRICT_EXTRACTED_REPLAY_PASS',fresh_extracted_replay={'status':receipt['status'],'elapsed':receipt['elapsed'],'axiom_audits':len(receipt['axiom_audits']),'receipt':'replay-receipt.json'},predecessor_hashes_unchanged=True,transitive_import_modules=3106)
(w/'results.json').write_text(json.dumps(r,indent=2))
p=w/'SUMMARY.md';s=p.read_text().replace('Local strict Lean check PASS; fresh extracted replay pending.',f"Local strict Lean check and fresh extracted replay PASS ({receipt['elapsed']:.2f} seconds, {len(receipt['axiom_audits'])} allowed-axiom audits).")
p.write_text(s)
p=w/'FORMAL-GAPS.md';p.write_text(p.read_text().replace('None in the locally checked endpoint. The extracted replay must also pass before handback.','None. The full endpoint passes both local strict checking and the fresh extracted strict replay.'))
subprocess.run([sys.executable,str(w/'make_packet.py')],check=True)
# Update extracted documentation and verify final archive bytes against checked sources.
with zipfile.ZipFile(w/'330264-r3-FULL-LEAN.zip') as z:
 for f,h in receipt['source_hashes'].items(): assert hashlib.sha256(z.read(f)).hexdigest()==h
 z.extractall(x)
manifest=json.loads((w/'packet-manifest.json').read_text())
for f,h in manifest['files'].items(): assert hashlib.sha256((x/f).read_bytes()).hexdigest()==h
(w/'archive-receipt.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'archive':'330264-r3-FULL-LEAN.zip','sha256':hashlib.sha256((w/'330264-r3-FULL-LEAN.zip').read_bytes()).hexdigest(),'final_archive_manifest_verified_after_extraction':True,'all_final_Lean_bytes_match_fresh_strict_replay':True,'only_documentation_and_receipts_updated_after_replay':True,'predecessor_hashes_before_after':'all frozen bindings unchanged'},indent=2))
print(r['status'],receipt['elapsed'],len(receipt['axiom_audits']))
