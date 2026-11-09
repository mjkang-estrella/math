import pathlib,hashlib,json,datetime
L=pathlib.Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
bindings=json.loads((L/'frozenbindings.json').read_text())
status=[dict(original=x['original'],sha256=x['sha256'],original_after=h(pathlib.Path(x['original'])),copy_after=h(pathlib.Path(x['copy']))) for x in bindings]
(L/'source-after.json').write_text(json.dumps(status,indent=2)+'\n')
admin={p.name:h(p) for p in (L/'administrative').iterdir() if p.is_file()}
provenance={'date_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'NO_NOMINATION_PRECISE_GAP',
 'guard':str(guard),'guard_sha256':h(guard),'limits':{'address_space_bytes':512*1024**2,'group_rss_bytes':512*1024**2,'cpu_seconds':210,'wall_seconds':230},
 'environment':{'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1','PYTHONDONTWRITEBYTECODE':'1'},
 'administrative_snapshots_sha256':admin,'administrative_immutability_claim':False,
 'counts_read_only':{'additional':9,'total':39,'next':40},'source_bindings':'frozenbindings.json','http_receipts':'primaryreceipts.jsonl',
 'source_scope':'six fresh primary PDFs; one reused survey PDF; copied compact lane reports; no recursive evidence tree',
 'known_protocol_failure':'Historical reports and catalogue header initially excerpt-read before freeze; see FAILURES.md',
 'current_registry_clearance':False,'source_after_all_match':all(x['sha256']==x['original_after']==x['copy_after'] for x in status)}
(L/'provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')
files={str(p.relative_to(L)):h(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['finalmanifest.json','verification-receipt.json']}
(L/'finalmanifest.json').write_text(json.dumps({'algorithm':'sha256','excludes':['finalmanifest.json','verification-receipt.json'],'files':files},indent=2)+'\n')
print(json.dumps({'files':len(files),'originals_and_copies_match':provenance['source_after_all_match']}))
