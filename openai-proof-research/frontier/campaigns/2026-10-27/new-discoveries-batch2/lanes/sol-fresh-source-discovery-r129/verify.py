import pathlib,json,hashlib
L=pathlib.Path(__file__).parent;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((L/'manifest.json').read_text())
for r in manifest:
 p=L/r['path'];assert p.is_file() and p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],r['path']
freeze=json.loads((L/'scientific-freeze.json').read_text())
for p,h in freeze.items():assert sha(L/p)==h,p
prov=json.loads((L/'provenance.json').read_text());assert sha(L/prov['guard']['path'])==prov['guard']['sha256']
r=json.loads((L/'history/receipt.json').read_text());assert r['global_hit_cutoff'] is None and r['date_filter'] is None
assert not any(x.endswith('r111') or x.endswith('r112') or x.endswith('r113') for x in r['pruned_role_directories'])
for name,needle in [('r47-discovery.md','Conjecture7.2'),('r34-discovery.md','599'),('r52-discovery.md','Question1.7')]:assert needle in (L/'history'/name).read_text(),name
reg=json.loads((L/'sources/registry-receipt.json').read_text());assert reg['behind']==0 and reg['ahead']==reg['total_commits']==reg['commits_returned']==21 and reg['files_returned']==18 and not reg['api_cap_detected']
assert not (L/'PROOF.md').exists();assert not (L/'checks/results.json').exists()
result={'status':'PASS documentary integrity only','manifest_files':len(manifest),'scientific_source_files':len(freeze),'history_unique':r['counts']['unique_files'],'old_targets':3,'new_results':0,'no_mathematical_checker_run':True}
(L/'verification-results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
