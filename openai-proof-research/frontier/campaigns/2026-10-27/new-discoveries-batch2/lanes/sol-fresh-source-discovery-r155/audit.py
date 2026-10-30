import sys,json,hashlib,datetime,zipfile
from pathlib import Path
L=Path(__file__).resolve().parent
def H(b):return hashlib.sha256(b).hexdigest()
def J(n,x):(L/n).write_text(json.dumps(x,indent=2)+'\n')
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
if sys.argv[1]=='inspect':
    j=json.loads((L/'sources/su-latest.json').read_bytes())
    print('latest',j['id'],j.get('created'),j.get('updated'),j['metadata'])
    with zipfile.ZipFile(L/'sources/su-source.zip') as z:
        print('archive members',z.namelist())
        for n in z.namelist():
            if n.endswith(('.md','.tex')) and z.getinfo(n).file_size<200000:
                b=z.read(n);f=L/'sources'/('archive-'+Path(n).name);f.write_bytes(b)
    for n in ['ledger.json','prior-campaign-context.json']:
        j=json.loads((L/('context-'+n)).read_bytes())
        rows=[{k:a[k] for k in ['number','title','scope','source_target','status','novelty_limit'] if k in a} for a in j.get('accepted',[])]
        J('read-'+n,dict(rows=rows,other_keys=list(j),sha256=H((L/('context-'+n)).read_bytes())))
    print('Structured context read; digest files saved.')
elif sys.argv[1]=='freeze':
    J('baseline-provenance.json',[dict(path=str(p),sha256=H(p.read_bytes())) for p in [L.parent/'sol-fresh-source-discovery-r153/history-delta.json',L.parent/'sol-fresh-source-discovery-r150/history-receipt.json',L.parent/'sol-fresh-source-discovery-r147/history-receipt.json',L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py']])
    http=[json.loads(x) for x in (L/'http.jsonl').read_text().splitlines()]
    J('provenance.json',dict(utc=now(),result='zero qualifying discoveries',http=http,coverage=dict(history='Qualified r150/r147 baseline, merged r153 delta; changed/new roles refreshed. Complete retained original bodies searched, no size cutoff. frozen/private/context/core/extraction echoes excluded by role; original r111-r113 retained.',registry='Fixed Omega490f6bccbf445ab8e111a16b0b8670a5dd7c9a9c and OpenAI7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a; lexical trees only, two actual candidate theorem bodies read; both compare lists capped300 remain gaps.',source='Latest-version API points to21853500; v2 actual PDF pp1-10 and selected later statements, source archive changelog and current record. No journal publication established. No full audit of every appendix or cited literature.',mathematics='No universal proof, counterexample, classical exclusion or novelty clearance.'),resource='Unchanged helper_guard.py; AS/group sampledRSS512MiB, CPU210s, wall230s, nominal40ms; unsampled transients not ruled out',external_actions=False))
    omitted={'scientific-freeze.json','finalmanifest.json','manifest-verification.json','freeze.log','verify.log'}
    science={};manifest={}
    for f in sorted(L.rglob('*')):
        if not f.is_file() or f.name in omitted:continue
        p=str(f.relative_to(L));h=H(f.read_bytes());manifest[p]=h
        if not p.startswith('context-') and not p.startswith('read-') and not p.endswith('.log'):science[p]=h
    J('scientific-freeze.json',dict(utc=now(),files=science,mutable_context_excluded=True))
    manifest['scientific-freeze.json']=H((L/'scientific-freeze.json').read_bytes())
    J('finalmanifest.json',dict(utc=now(),files=manifest,excluded=list(omitted-{'scientific-freeze.json'}),self_hash_excluded=True))
elif sys.argv[1]=='verify':
    checks={}
    for n in ['scientific-freeze.json','finalmanifest.json']:
        j=json.loads((L/n).read_bytes());bad=[p for p,h in j['files'].items() if not (L/p).exists() or H((L/p).read_bytes())!=h]
        checks[n]=dict(entries=len(j['files']),mismatches=bad)
        assert not bad
    for r in map(json.loads,(L/'http.jsonl').read_text().splitlines()):
        if 'sha256' in r:assert H((L/'sources'/r['name']).read_bytes())==r['sha256']
    J('manifest-verification.json',dict(utc=now(),checks=checks,pass_=True))
    print(checks)
