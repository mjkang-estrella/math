import pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
bindings=json.loads((L/'bindings.json').read_text())
for r in bindings:
 if 'immutable_reference' in r:r['immutable_reference']=r['original']
(L/'bindings.json').write_text(json.dumps(bindings,indent=2)+'\n')
# Administrative snapshots are inspected without binding changing live ledgers.
admin=json.loads((L/'administrative/ledger.json').read_text())
assert [admin[k] for k in ['accepted_count','total_accepted_count','next_global_outcome_number']]==[9,39,40]
prior=json.loads((L/'administrative/prior-campaign-context.json').read_text())
print('Administrative snapshots read:',len(prior.get('accepted',[])),'prior outcomes;',admin['accepted_count'],'additional')
files=[{'path':str(p.relative_to(L)),'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['final-manifest.json','final-verification.json']]
(L/'final-manifest.json').write_text(json.dumps({'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'excluded':['final-manifest.json','final-verification.json'],'files':files},indent=2)+'\n')
print('Manifest files:',len(files))
