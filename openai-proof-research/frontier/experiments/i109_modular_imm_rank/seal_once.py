"""One-time preparation step, separate from the offline read-only verifier."""
import pathlib,json,hashlib
R=pathlib.Path(__file__).resolve().parents[3];S=R/'frontier/sources/i109_modular_imm_rank';X=R/'frontier/experiments/i109_modular_imm_rank'
assert not (S/'seal.json').exists()
events=json.loads((S/'preseal-events.json').read_text());assert events and events[-1]['exit_code']==0
last=json.loads((S/events[-1]['record']).read_text());assert last['exit_code']==0 and json.loads(last['stdout'])['status']=='PRESEAL_PASS'
files=[R/'frontier/iterations/i109-modular-imm-rank.md']+[p for base in [S,X] for p in base.rglob('*') if p.is_file()]
seal={'schema':'i109-integrity-seal-v1','pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','policy':'One final seal after validation; no postseal edits or resealing. Seal itself is the excluded root manifest.','scope':'Evidence integrity and finite diagnostics only; not universal proof or substantiality certification','files':{str(p.relative_to(R)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(files)}}
with (S/'seal.json').open('x') as f:f.write(json.dumps(seal,indent=2)+'\n')
print(json.dumps({'files_excluding_seal':len(files),'seal_sha256':hashlib.sha256((S/'seal.json').read_bytes()).hexdigest()}))
