from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
bindings=[]
for name in ['freeze.json','support-freeze.json']:
 for r in json.loads((L/name).read_text()):
  assert sha(Path(r['original']))==sha(L/r['copy'])==r['sha256'],r
  bindings.append(r)
receipt=json.loads((L/'fresh-replay-02/replay-receipt.json').read_text())
assert receipt['component_status']=='PASS' and receipt['source_endpoint_status']=='NOT_PROVED'
for p in L.rglob('*.olean'):p.unlink()
guard=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py')
primary=next(r for r in bindings if r['copy'].endswith('frozen/1911.08613v2.pdf'))
r={'status':'PARTIAL_FORMAL_COMPONENT_ONLY','component_replay':'fresh-replay-02/replay-receipt.json',
 'actual_declarations':receipt['actual_declaration_count'],'primary':primary,
 'scientific_original_copy_bindings_unchanged':len(bindings),'helper_guard_path':str(guard),'helper_guard_sha256':sha(guard),
 'administrative_files':'snapshots only; never final-bound to live NEXT/count values',
 'network':'none; inherited current-prior and published-body holds retained','children':0,'acceptance_or_count':False,
 'limits':{'helper_AS_groupRSS_MiB':512,'Lean_M':2700,'Lean_groupRSS_MiB':2800,'CPU_seconds':210,'wall_seconds':230,'serial_j':1,'sample_seconds':.04},
 'successful_peak_Lean_groupRSS_bytes':max(x['sampled_peak_group_rss'] for x in receipt['builds'])}
(L/'provenance.json').write_text(json.dumps(r,indent=2)+'\n')
(L/'binding-after.json').write_text(json.dumps(bindings,indent=2)+'\n')
exclude={'manifest.json','verification-receipt.json'}
manifest={str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and str(p.relative_to(L)) not in exclude}
(L/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'files':len(manifest),'scientific_bindings':len(bindings),'declarations':receipt['actual_declaration_count'],'source_endpoint':'NOT_PROVED'}))
