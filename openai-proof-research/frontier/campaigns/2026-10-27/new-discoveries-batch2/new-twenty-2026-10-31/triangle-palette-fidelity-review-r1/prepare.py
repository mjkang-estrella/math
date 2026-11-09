from run_audit import *
A=O.parent/'expanded-corpus-r58'
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((A/'proof-packet-manifest.json').read_text());rows={n:{'extracted':h(F/n),'author':h(A/n),'manifest':v} for n,v in m['files'].items()};assert all(len(set(r.values()))==1 for r in rows.values());(O/'extract-hashes.json').write_text(json.dumps(rows,indent=2))
pins={str(p):h(p) for p in [BIN/'lean',BIN/'leanchecker',PACK.parent.parent/'lake-manifest.json']};pins['lean_version']=subprocess.check_output([str(BIN/'lean'),'--version'],text=True);(O/'pins.json').write_text(json.dumps(pins,indent=2))
def cache():
 return {str(p):{'size':p.stat().st_size,'mtime_ns':p.stat().st_mtime_ns,'sha256':h(p)} for p in PACK.rglob('*.olean*') if p.is_file()}
(O/'cache-before.json').write_text(json.dumps(cache(),indent=2))
raw=A/'raw/364095.jsonl';r=json.loads((A/'results.json').read_text())['364095']['literal_provenance'];row=raw.read_bytes();chunk=pathlib.Path(r['chunk']);line=chunk.open('rb').readlines()[r['one_based_line']-1];assert row==line and h(raw)==r['raw_sha256'] and h(chunk)==r['chunk_sha256'];(O/'raw-verification.json').write_text(json.dumps({'raw_sha256':h(raw),'chunk_sha256':h(chunk),'byte_equal_line':True,'statement_sha256':hashlib.sha256(json.loads(row)['statement'].encode()).hexdigest()},indent=2))
(O/'raw-364095.jsonl').write_bytes(row)
