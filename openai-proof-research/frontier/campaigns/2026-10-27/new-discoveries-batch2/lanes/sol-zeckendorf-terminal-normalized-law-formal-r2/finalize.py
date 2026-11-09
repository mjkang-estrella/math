from pathlib import Path
import hashlib,json,sys,re,zipfile,importlib.util
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def science():
 rows=json.loads((L/'bindings.json').read_text())
 for r in rows:
  assert sha(Path(r['original']))==r['sha256']==sha(L/r['copy']),r
 old=L.parent/'sol-zeckendorf-literal-game-law-formal-r1'
 inherited=json.loads((L/'frozen/sol-zeckendorf-literal-game-law-formal-r1/source-bindings.json').read_text())
 for r in inherited:
  assert sha(Path(r['original']))==r['sha256']==sha(old/r['copy']),r
 assert (L/'Literal.lean').read_bytes()==(old/'Literal.lean').read_bytes()
 return len(rows),len(inherited)
def pins():
 spec=importlib.util.spec_from_file_location('pincheck',L/'package.py')
 mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
 actual=mod.checkpins();assert actual==json.loads((L/'pins.json').read_text())
 return actual
mode=sys.argv[1]
if mode=='provenance':
 direct,old=science();p=pins()
 prior=L.parent/'sol-zeckendorf-literal-game-law-formal-r1'
 logs=[dict(path=str(x),sha256=sha(x)) for x in sorted(prior.glob('attempt-*.log'))]
 receipt=json.loads((L/'frozen/sol-zeckendorf-literal-game-law-formal-r1/replay-receipt.json').read_text())
 ledger=json.loads((L/'administrative/ledger.json').read_text())
 context=json.loads((L/'administrative/prior-campaign-context.json').read_text())
 (L/'provenance.json').write_text(json.dumps(dict(date='2026-10-30',scope='two finite mandatory endpoints only',external_actions=False,counts=dict(additional=ledger['accepted_count'],total=ledger['total_accepted_count'],next=ledger['next_global_outcome_number']),prior_context_entries=len(context['accepted']),scientific_direct_bindings=direct,inherited_immutable_reference_pairs=old,predecessor_attempt_logs=logs,predecessor_archive_sha256=receipt['packet_sha256'],inherited_literal_sha256=sha(L/'Literal.lean'),compiler_sha256=sha(Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')),package_pins=p,administrative_snapshots={x.name:sha(x) for x in (L/'administrative').iterdir() if x.is_file()},access_limitations='No remote retrieval; denied routes and inaccessible historical intervals parked. No novelty clearance.'),indent=2)+'\n')
 print('PASS before/final source bindings',direct,old)
elif mode=='manifest':
 science();pins()
 files={str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in {'MANIFEST.json','verification-receipt.json'}}
 (L/'MANIFEST.json').write_text(json.dumps(files,indent=2)+'\n');print('manifest',len(files))
elif mode=='verify':
 manifest=json.loads((L/'MANIFEST.json').read_text())
 actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in {'MANIFEST.json','verification-receipt.json'}}
 assert set(manifest)==actual
 for f,h in manifest.items():assert sha(L/f)==h,f
 direct,old=science();p=pins()
 prov=json.loads((L/'provenance.json').read_text())
 for r in prov['predecessor_attempt_logs']:assert sha(Path(r['path']))==r['sha256']
 artifacts=[str(x) for x in L.rglob('*') if x.suffix in {'.olean','.ilean','.ir','.o','.so','.pyc'}]
 assert not artifacts,artifacts
 replay=json.loads((L/'replay-receipt.json').read_text())
 assert replay['status']=='PASS' and replay['deterministic_diagnostics']
 assert replay['archive_sha256']==sha(L/'source-only.zip')
 for r in replay['replays']:
  assert r['declarations']==295
  for s in r['steps']:assert s['exit']==0 and s['reason'] is None and s['peak_group_rss']<=2800*1024**2
 audit=json.loads((L/'audit.json').read_text());assert audit['status']=='PASS' and audit['total_count']==295
 assert len(audit['declarations'])==295
 assert all(not x['unsafe'] and set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in audit['declarations'])
 counts={}
 for x in re.findall(r'^OWN_MODULE \S+ (\S+)$',(L/'replay/fresh-a/attempt-003.log').read_text(),re.M):counts[x]=counts.get(x,0)+1
 closure=int(re.search(r'TRANSITIVE_SAFE_COUNT (\d+)',(L/'replay/fresh-a/attempt-003.log').read_text())[1])
 (L/'verification-receipt.json').write_text(json.dumps(dict(status='PASS',manifest_sha256=sha(L/'MANIFEST.json'),manifest_files=len(manifest),direct_bindings_verified=direct,inherited_reference_pairs_verified=old,inherited_declarations=198,declarations_by_module=counts,total_declarations=295,transitive_safe_constants=closure,allowed_axioms=['propext','Classical.choice','Quot.sound'],source_only_archive_sha256=sha(L/'source-only.zip'),two_fresh_extracted_replays=True,compiled_artifacts_remaining=0,compiler_sha256=prov['compiler_sha256'],all_nine_pins=p,finite_mandatory_endpoints='proved; rational finite P_N, no PMF wrapper',mixing_novelty='HOLD',counts_changed=False),indent=2)+'\n')
 print('PASS final separate verification',counts,'closure',closure)
