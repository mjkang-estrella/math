from pathlib import Path
import json,hashlib,re,zipfile
D=Path(__file__).resolve().parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
R=Path((D/'latest-replay.txt').read_text().strip())
s=json.loads((R/'replay-state.json').read_text());assert s['complete']
mods=json.loads((D/'scripts/modules.json').read_text())
assert s['build']==mods and s['check']==mods and all(s['negative'].values())
before=json.loads((D/'frozen-before.json').read_text());after={n:sha(D/'formal'/n) for n in before};assert before==after
original=D.parent/'expanded-corpus-r126/338258-proof-source.zip'
assert sha(original)=='628b850b31e347ab2d395fa6c11474c4ea8765c1cbdb6cc051e1ed3d77b0d198'
with zipfile.ZipFile(original) as z:
 for n in before:assert hashlib.sha256(z.read(n)).hexdigest()==before[n]
(D/'frozen-after.json').write_text(json.dumps(after,indent=2))
for m in mods:assert (D/'formal'/(m+'.lean')).read_bytes()==(R/(m+'.lean')).read_bytes()
records=[(p,json.loads(p.read_text())) for p in (D/'logs').glob('*.json')]
# Latest successfully compiled audit is the audit from the fresh extraction.
audit=max((p for p,r in records if '-o' in r['command'] and 'StrongAudit.lean' in r['command'] and r['returncode']==0),key=lambda p:p.stat().st_mtime)
at=audit.with_suffix('.log').read_text()
local=int(re.search(r'LOCAL_TOTAL=(\d+)',at)[1]);dep=int(re.search(r'DEPENDENCY_TOTAL=(\d+)',at)[1])
assert 'CLOSURE_EQUALITY=true' in at
assert len(re.findall(r'^LOCAL\|',at,re.M))==local
assert len(re.findall(r'^DECL\|',at,re.M))==dep
assert not re.search(r'unsafe=true|partial=true',at)
assert re.search(r'UPSTREAM_EXTERN=57\|UPSTREAM_IMPLEMENTED_BY=4',at)
# Check forbidden proof mechanisms in successful source files; tooling strings
# and #print axioms are not declaration commands.
hits=[]
for m in mods[:20]:
 src=(R/(m+'.lean')).read_text()
 for pat in [r'\bsorry\b',r'\badmit\b',r'\bnative_decide\b',r'\bofReduceBool\b',r'^\s*(?:unsafe\s+|partial\s+|axiom\s+)']:
  if re.search(pat,src,re.M):hits.append([m,pat])
assert not hits
endpoints=['Riordan.source_conjecture_false','Riordan.source_conjecture_false_infinite_family']
for ep in endpoints:
 assert "'"+ep+"' depends on axioms: [propext, Classical.choice, Quot.sound]" in at
B=Path('/home/mj-kang/Documents/Dev/math')
manifest=B/'openai-proof-research/frontier/campaigns/2026-10-14/formal/lake-manifest.json'
pin=[p for p in json.loads(manifest.read_text())['packages'] if p['name']=='mathlib'][0]['rev']
assert pin=='d13f23b723b8a846827a245b89c10fc7d3f11612'
result={'mathdb_id':338258,'lane':'riordan-formal-r2','status':'implemented and validated; root review required','accepted':False,'credit':0,'root_decides':True,
 'modules':{m:{'sha256':sha(R/(m+'.lean')),'lines':len((R/(m+'.lean')).read_text().splitlines()),'role':'proof' if m in mods[:20] else 'audit tooling'} for m in mods},
 'frozen_hashes_before':before,'frozen_hashes_after':after,'frozen_unchanged':before==after,
 'frozen_proof_module_count':18,'frozen_auxiliary_source_count':1,'original_archive_sha256':sha(original),
 'source_archive':{'path':'338258-infinite-family-source.zip','sha256':sha(D/'338258-infinite-family-source.zip'),'safe_paths':True,'source_only':True},
 'endpoints':{ep:{'status':'strict fresh build and leanchecker passed','axioms':['propext','Classical.choice','Quot.sound']} for ep in endpoints},
 'fresh_replay':{'directory':str(R.relative_to(D)),'strict_build_count':len(s['build']),'leanchecker_count':len(s['check']),'complete':s['complete'],'state':str((R/'replay-state.json').relative_to(D))},
 'audit':{'log':str(audit.with_suffix('.log').relative_to(D)),'local_module_count':20,'local_generated_and_ordinary_declarations':local,'transitive_body_and_type_dependency_declarations':dep,'audited_set_equals_dependency_closure':True,'unsafe':0,'partial':0,'unsafe_rec_companions':0,'local_implemented_by':0,'local_extern':0,'upstream_extern':57,'upstream_implemented_by':4,'upstream_runtime_attributes_inventoried_not_used_as_proof':True,'axioms':['propext','Classical.choice','Quot.sound'],'scope':'all declarations from the local module import closure of both endpoints, plus their complete transitive kernel body/type dependency closure; unrelated upstream metaprogramming is not part of this set'},
 'negative_controls':s['negative'],'source_scan_forbidden_hits':hits,
 'pins':{'lean_version':'4.34.1','mathlib_rev':pin,'manifest_sha256':sha(manifest),'lean_sha256':sha(B/'dlp-research/.tools/lean-4.34.1-linux/bin/lean'),'leanchecker_sha256':sha(B/'dlp-research/.tools/lean-4.34.1-linux/bin/leanchecker')},
 'resources':{'cpu_affinity_max':2,'cpu_seconds_per_expensive_child':120,'wall_seconds_per_expensive_child':140,'sampled_rss_limit_bytes':6*1024**3,'peak_sampled_group_rss_bytes':max(r['sampled_peak_rss'] for p,r in records),'MALLOC_ARENA_MAX':2,'heavy_concurrency_in_lane':1,'RSS_is_sampled_not_cgroup':True},
 'failed_development_logs':[str(p.with_suffix('.log').relative_to(D)) for p,r in records if r['returncode'] and not any('Negative' in c for c in r['command'])],
 'background_processes_at_handback':0}
(D/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'local':local,'dependency_closure':dep,'build':len(s['build']),'checker':len(s['check']),'negative':s['negative'],'peak_rss':result['resources']['peak_sampled_group_rss_bytes']},indent=2))
