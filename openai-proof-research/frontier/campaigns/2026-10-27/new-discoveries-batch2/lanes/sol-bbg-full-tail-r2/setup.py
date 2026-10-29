import pathlib,hashlib,json,datetime,shutil
R=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research');B=R/'frontier/campaigns/2026-10-27/new-discoveries-batch2';L=B/'lanes/sol-bbg-full-tail-r2';old=B/'lanes/sol-fresh-analytic-probability-r27'
paths=[R/'AGENTS.md',B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',B/'NEXT.md']+list(old.rglob('*'))+list((B/'lanes/root-bbg-tail-followup-r1').glob('*'))
rows={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths if p.is_file()}
(L/'inputs-before.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'hashes':rows},indent=2))
(L/'sources').mkdir(exist_ok=True)
for p in (old/'sources').glob('*'):
 if p.name.startswith(('bbg','boppana')):shutil.copyfile(p,L/'sources'/p.name)
shutil.copyfile(old/'check.py',L/'prefix-original.py');shutil.copyfile(old/'checks.json',L/'prefix-original.json')
for p in [B/'ledger.json',B/'prior-campaign-context.json',B/'NEXT.md']:
 data=p.read_text(); print(p.name,len(data), 'read in full; relevant lines:'); print('\n'.join(x[:500] for x in data.splitlines() if any(t in x.lower() for t in ['bbg','boppana','sinusoidal','373621','5/30','35/60'])))
for name in ['omega-live.txt','omega-delta.txt']:
 p=B/'lanes/sol-fresh-finite-optimization-r26/sources'/name;shutil.copyfile(p,L/'sources'/name);print(name,p.read_text()[:12000])
