from pathlib import Path
import json,hashlib,datetime,resource,signal
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(15,15));signal.alarm(20)
b=Path(__file__).resolve().parent;p=b.parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
r=json.loads((b/'registry.json').read_text())
old=p/'sol-fresh-probability-finite-r21/sources'
r['omega']={'current_head':json.loads((b/'sources/omega-head.json').read_text())['sha'],'current_commit_utc':json.loads((b/'sources/omega-head.json').read_text())['commit']['committer']['date'],'coverage':'HOLD: current root-tree403; no API retries','old_head':'65b7e4d804a45e6b255f6f0974bbda900855a3e6','old_commit_utc':'2026-10-29T08:36:52Z','trees':[]}
for name in ['Blueprint','D5','Problems']:
 f=old/f'omega-{name}-tree.json';j=json.loads(f.read_text());assert not j['truncated']
 r['omega']['trees'].append({'file':str(f),'sha256':sha(f),'sha':j['sha'],'entries':len(j['tree']),'truncated':False,'prefix':name})
(b/'registry.json').write_text(json.dumps(r,indent=2))
terms=['gatzweiler','krattenthaler','fakegaussian','fake-gaussian','fake_gaussian','levican','levicán','agoh','alternating-numerator','stanton']
screens={}
for key,x in r.items():
 files=[Path(x['base_file'])] if 'base_file' in x else [Path(z['file']) for z in x['trees']]
 screens[key]={str(f):[e['path'] for e in json.loads(f.read_text())['tree'] if any(t in e['path'].lower() for t in terms)] for f in files}
(b/'registry-screen.json').write_text(json.dumps(screens,indent=2))
ctx=json.loads((b/'past-context-read.json').read_text())
inputs=[{'path':v['path'],'sha256_at_read':hashlib.sha256(v['text'].encode()).hexdigest(),'bytes_at_read':len(v['text'].encode())} for v in ctx]
source_inventory=[{'path':str(f.relative_to(b)),'sha256':sha(f),'bytes':f.stat().st_size} for f in sorted((b/'sources').glob('*')) if f.is_file()]
output={'written_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'UNRESOLVED; no completed eligible result','credit':0,'counts_unchanged':{'additional':5,'total':35},'source':{'target':'published Gatzweiler–Krattenthaler Conjecture4/equation2','url':'https://link.springer.com/article/10.1007/s11139-025-01285-2','journal_published':'2025-12-17','arxiv':'2502.06032v3','arxiv_original':'2025-02-09','arxiv_latest':'2025-11-20','scope':'all positive m>=n; every nonnegative integer exponent vector; polynomiality implies all coefficients nonnegative','journal_body':'actual full HTML retrieved and inspected; no journal access gap','successor':'2603.22226v1 2026-03-23; actual Prop3.3/Thm3.9/Cor3.11 proofs read','successor_published_scope':'known m>2n floor(n/2)-2; no credit'},'registry':r,'registry_limits':'Complete path screening only. Current Omega coverage failed403; old complete bases dated. Clopen homepage/site search not exhaustive. No full-text literature-absence claim.','http':json.loads((b/'http.json').read_text()),'access_gaps':['api.github.com403 rate limit at2026-10-29T09:05:18Z: stopped; no current Omega tree/delta','arxiv HTML2502.06032v3 returned404: PDF acquired instead','No exhaustive MathSciNet/zbMATH or clopen corpus screen','Agoh original addition chronology unknown; existing immutable snapshot before lane suffices to discard lead; no priority claim'],'inputs':inputs,'source_inventory':source_inventory,'scripts':[{'path':f.name,'sha256':sha(f)} for f in b.glob('*.py')],'checks':json.loads((b/'checks.json').read_text()),'exact_obstruction':'exact-obstruction.json; integer-only independent reconstruction; source quotient nonnegative, semigroup criterion false','bounded_lp_search':'search-obstructions.json; floating search with exact acceptance, no theorem','failure':'cone-initial-failure.txt records initial solver abort; explicit solver threads1 rerun succeeds','limits':'Mathematical scripts512MiB AS, fixed seeds,45CPU/50wall or20CPU/25wall, BLAS1; no Lean','strongest_routine_subsumer':'successor Proposition3.3 plus classical Stanley Hilbert-series formula; all satisfying families public/routine','remaining_gap':'uniform all-n/exponent positivity or actual negative coefficient inside m>=n; direct raw-degree semigroup implication false','no_external_mutations':True,'no_children':True,'no_git':True,'all_writes_in_assigned_lane':True}
(b/'provenance.json').write_text(json.dumps(output,indent=2))
print('provenance saved;',len(inputs),'context inputs;',len(source_inventory),'source artifacts')
print(json.dumps(screens,indent=2)[:2500])
