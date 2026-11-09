import pathlib,json,hashlib,datetime
D=pathlib.Path(__file__).resolve().parents[1];sha=lambda b:hashlib.sha256(b).hexdigest();X=json.loads((D/'results.json').read_text());r=json.loads((D/'reservation.json').read_text());assert set(map(int,X))==set(r['ids']) and len(X)==20
for key,o in X.items():
 raw=(D/f'raw/{key}.jsonl').read_bytes();assert raw.endswith(b'\n') and sha(raw)==o['provenance']['raw_sha256'];assert sha(o['statement'].encode())==o['provenance']['statement_utf8_sha256'];src=D/o['source_receipt']['path'];assert sha(src.read_bytes())==o['source_receipt']['sha256']
assert all(o['accepted_credit']==0 and o['lean_endpoint'] is None for o in X.values())
cached=json.loads((D.parent/'fresh-corpus-r10/sources/registry-preprints.json').read_text());root=json.loads((D/'sources/openai-root.json').read_text());assert next(x['sha'] for x in root['tree'] if x['path']=='preprints')==cached['sha']
for k in ['D5','Problems']:assert not json.loads((D/f'sources/omega-{k}.json').read_text())['truncated']
manifest={str(p.relative_to(D)):sha(p.read_bytes()) for p in sorted(D.rglob('*')) if p.is_file() and p.name not in ['manifest.json','validation.json'] and '__pycache__' not in p.parts}
(D/'manifest.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':manifest},indent=2)+'\n');(D/'outputs/validation.json').write_text(json.dumps({'entries':20,'raw_hashes_match':True,'source_hashes_match':True,'newline_preserved':True,'openai_cache_subtree_matches_fresh_root':True,'omega_scopes_not_truncated':True,'accepted_credit':0,'lean_validation':'not performed'},indent=2)+'\n');print('20 entries, raw/source hashes, current registry scopes and zero-credit flags validated')
