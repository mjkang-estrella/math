from pathlib import Path
import hashlib,json
L=Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
# Read complete administrative snapshots, emitting only relevant inventory.
ledger=json.loads((L/'context/ledger.json').read_text())
prior=json.loads((L/'context/prior-campaign-context.json').read_text())
(L/'history-screen.json').write_text(json.dumps(dict(counts={k:ledger[k] for k in ['accepted_count','total_accepted_count','next_global_outcome_number']},accepted_titles=[x.get('title') for x in ledger['accepted']],prior_keys=list(prior),prior_accepted_titles=[x.get('title') for x in prior['accepted']],alias_terms=['biquadratic','Krasensky','Krásenský','Tinkova','Tinková','Zemkova','Zemková','2307.04908','indecomposable'],limit='administrative history only; not current public registry clearance'),indent=2)+'\n')
bindings=json.loads((L/'bindings.json').read_text())
for b in bindings:
 assert h(L/b['copy'])==b['sha256']
 if b['kind']=='scientific':assert h(Path(b['original']))==b['sha256']
fresh=json.loads((L/'access.json').read_text())+[json.loads(s) for s in (L/'more-access.jsonl').read_text().splitlines()]
for b in fresh:
 if 'path' in b:assert h(L/b['path'])==b['sha256']
inventory={str(p.relative_to(L)):h(p) for p in sorted((L/'sources').iterdir()) if p.is_file()}
(L/'source-inventory.json').write_text(json.dumps(inventory,indent=2)+'\n')
manifest={str(p.relative_to(L)):h(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['manifest.json','final-verification.json']}
(L/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(dict(sealed=len(manifest),scientific_sources=len(inventory),bound_originals_copies='PASS')))
