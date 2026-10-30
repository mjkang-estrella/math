from work import *
terms=['2610.31785','10.48550/arXiv.2610.31785','principal specializations of the t-chromatic symmetric function','t-chromatic','fourth principal specialization','Bingham','Celano','Commins','Orellana','Jianping Pan','Mary Claire Simone']
refs=[]
for n in [207,208]:
    d=L.parent/f'sol-fresh-source-discovery-r{n}'
    for p in (d/'indexes').iterdir():refs.append({'path':str(p),'sha256':sha(p),'role':'corrected historical index snapshot, not scientific premise'})
for n in [205,206,207,208]:
    p=L.parent/f'root-r{n}-handback/DECISION.md';refs.append({'path':str(p),'sha256':sha(p),'role':'root historical decision'})
for n in [206,207,208]:
    for fn in ['SUMMARY.md','discovery.md']:
        p=L.parent/f'sol-fresh-source-discovery-r{n}'/fn;refs.append({'path':str(p),'sha256':sha(p),'role':'historical report'})
save('reference-bindings.json',refs)
aliases={}
for n in [207,208]:
    p=L.parent/f'sol-fresh-source-discovery-r{n}/alias-refresh.json'
    for r in json.loads(p.read_text())['records']:aliases[r['original']]=r
out=[]
(L/'alias-changed').mkdir(exist_ok=True)
for i,(s,r) in enumerate(sorted(aliases.items())):
    p=Path(s);q=r.get('canonical_copy',r.get('snapshot_reference',r.get('copy')))
    if not p.exists():out.append({'original':s,'missing':True});continue
    h=sha(p)
    if q and not Path(q).is_absolute():q=str(Path.cwd()/q)
    if not q or not Path(q).exists() or sha(q)!=h:
        q=str(L/'alias-changed'/f'{i:04d}-{p.name}');Path(q).write_bytes(p.read_bytes())
    t=Path(q).read_text(errors='replace').lower()
    out.append({'original':s,'sha256':h,'snapshot_reference':q,'changed':h!=r.get('sha256'),'terms':[a for a in terms if a.lower() in t],'qualification':'inherited alias only; never promoted to original provenance'})
save('alias-refresh.json',{'utc':utc(),'records':out})
for p in B.glob('NEXT*'):
    if p.is_file():(L/'administrative'/p.name).write_bytes(p.read_bytes())
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
(L/'guard-copy.py').write_bytes(guard.read_bytes())
bindings=[{'original':str(guard),'copy':str(L/'guard-copy.py'),'sha256':sha(guard),'role':'execution guard'}]
for line in (L/'http.jsonl').read_text().splitlines():
    r=json.loads(line)
    if 'sha256' in r:
        assert sha(r['original'])==sha(r['copy'])==r['sha256']
        bindings.append({k:r[k] for k in ['original','copy','sha256','url','utc','name']})
save('scientific-bindings.json',bindings)
r=subprocess.run([sys.executable,str(L/'checks.py')],capture_output=True,text=True)
(L/'checks.json').write_text(r.stdout);(L/'checks.stderr').write_text(r.stderr);assert r.returncode==0
save('provenance.json',{'utc':utc(),'target':'arXiv:2610.31785v1 Conjecture 6.1, printed p25','source_authors':['Aram Bingham','Kyle Celano','Patricia Commins','Rosa Orellana','Jianping Pan','Mary Claire Simone'],'source_submission':'2026-10-22T18:22:33Z','source_internal_date':'2026-10-26','source_version':'v1 only listed','source_doi':'10.48550/arXiv.2610.31785','classical':'Loebl–Sereni arXiv:1405.4132v4, Theorem 2, Sections 3–5','classical_versions':['2014-05-16T11:33:28Z','2016-06-20T10:27:08Z','2017-03-28T06:19:29Z','2018-06-13T13:14:40Z'],'classical_journal':'AIHP D 6(3) (2019) 357–384 per primary target bibliography; journal body not independently compared','eligibility':'bounded-history fresh target; unresolved here; zero nominations; current complete public registries inaccessible under inherited denials','administrative':'ledger/NEXT/context are point-in-time snapshots, excluded from scientific bindings','manifest_exclusions':['finalmanifest.json','verification-receipt.json'],'resource_caps':{'AS_MiB':512,'sampled_group_RSS_MiB':512,'CPU_seconds':210,'wall_seconds':230,'sample_ms':40},'universal_gap':'Rigidity of four-color scalar transfer invariants for all canonical caterpillar compositions, up to reversal. No complete proof/refutation.'})
print('aliases',len(out),'alias changed',sum(r.get('changed',False) for r in out),'alias hits',sum(bool(r.get('terms')) for r in out),'scientific',len(bindings),'refs',len(refs))
