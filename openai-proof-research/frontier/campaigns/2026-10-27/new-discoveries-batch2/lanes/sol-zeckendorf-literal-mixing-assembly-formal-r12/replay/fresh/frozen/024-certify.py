from pathlib import Path
import hashlib,json,re,sys,subprocess,zipfile,os
L=Path(__file__).resolve().parent
GUARD=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
if not GUARD.exists():
    GUARD=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def science():
    for r in json.loads((L/'bindings.json').read_text()):
        assert sha(L/r['copy'])==r['sha256'],r
        assert sha(Path(r['original']))==r['sha256'],r
    for n in ['Literal','Terminal','Law','Cells','Product','Prefix','Marks','Boards','Injection','Abundance','Tail','Concentration','Assembly','LastSplit','SuffixUnion']:
        assert (L/(n+'.lean')).read_bytes()==(L/'frozen'/('r10-'+n+'.lean')).read_bytes()
def pins():
    rows=json.loads((L/'pins.json').read_text())
    assert len(rows)==9
    for r in rows:
        g=Path(r['path'])/'.git'
        if g.is_file():g=(g.parent/g.read_text().strip().removeprefix('gitdir: ')).resolve()
        h=(g/'HEAD').read_text().strip()
        if h.startswith('ref: '):
            ref=h[5:]; f=g/ref
            if f.exists():h=f.read_text().strip()
            else:h=next(x.split()[0] for x in (g/'packed-refs').read_text().splitlines() if x.endswith(' '+ref))
        assert h==r['revision'],r
    return rows
def inventory(t):
    names=sorted(re.findall(r'^OWN_DECL (\S+)$',t,re.M))
    assert len(names)==len(set(names)) and len(names)>458
    for flag in ['SAFETY','PARTIAL']:
        rows=dict(re.findall(r'^OWN_'+flag+r' (\S+) (true|false)$',t,re.M))
        assert set(rows)==set(names) and set(rows.values())=={'false'}
    assert not re.search('panic|error:|REJECTED',t,re.I)
    return names
def audit(t,names):
    ax={n:re.findall(r'[\w.]+',a) for n,a in re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",t,re.M)}
    empty=re.findall(r"^'([^']+)' does not depend on any axioms$",t,re.M)
    assert set(names)==set(ax)|set(empty)
    assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in ax.values())
    assert not re.search('panic|error:|REJECTED',t,re.I)
    return [dict(name=n,axioms=ax.get(n,[]),partial=False,unsafe=False) for n in names]
def run(d,args):
    r=subprocess.run([sys.executable,str(GUARD),sys.executable,str(d/'runner.py'),*args],cwd=d,stdout=subprocess.DEVNULL)
    assert r.returncode==0,args
    p=sorted(d.glob('attempt-*.json'))[-1];rec=json.loads(p.read_text())
    assert rec['exit']==0 and rec['reason'] is None
    return p.with_suffix('.log').read_text(),rec
mode=sys.argv[1]
if mode=='pack':
    science();pins()
    logs=[p.read_text() for p in sorted(L.glob('attempt-*.log'))]
    inv=next(t for t in reversed(logs) if 'OWN_DECL ' in t)
    names=inventory(inv);aud=next(t for t in reversed(logs) if 'depends on axioms:' in t)
    rows=audit(aud,names)
    origins={}
    for m in re.findall(r'^OWN_MODULE \S+ (\S+)$',inv,re.M):origins[m]=origins.get(m,0)+1
    (L/'owned-declarations.json').write_text(json.dumps(names,indent=2)+'\n')
    assert set(origins)==set(['Literal','Terminal','Law','Cells','Product','Prefix','Marks','Boards','Injection','Abundance','Tail','Concentration','Assembly','LastSplit','SuffixUnion','Growth','Uniform','UniformSuffix'])
    (L/'audit.json').write_text(json.dumps(dict(status='PASS',declarations=rows,origins=origins,transitive=int(re.search(r'TRANSITIVE_SAFE_COUNT (\d+)',inv)[1]),instrumentation='StandaloneAudit is safe Lean instrumentation: module-index inventory plus transitive type/body inspection with allowOpaque=true; no proof axioms'),indent=2)+'\n')
    files=['Literal.lean','Terminal.lean','Law.lean','Cells.lean','Product.lean','Prefix.lean','Marks.lean','Boards.lean','Injection.lean','Abundance.lean','Tail.lean','Concentration.lean','Assembly.lean','LastSplit.lean','SuffixUnion.lean','Growth.lean','Uniform.lean','UniformSuffix.lean','StandaloneAudit.lean','runner.py','run.sh','certify.py','pins.json','RUN.md','SUMMARY.md','PROOF.md','PROOF-SOURCES.md','FAILURES.md','provenance.json','bindings.json']
    (L/'archive-files.json').write_text(json.dumps({f:sha(L/f) for f in files},indent=2)+'\n')
    with zipfile.ZipFile(L/'source-only.zip','w') as z:
        for f in files+['archive-files.json']:
            i=zipfile.ZipInfo(f,date_time=(2026,10,30,0,0,0));i.compress_type=zipfile.ZIP_DEFLATED;i.external_attr=0o100644<<16
            z.writestr(i,(L/f).read_bytes())
    print('PACK PASS',origins)
elif mode=='replay':
    science();pins();dest=L/'replay/fresh';dest.mkdir(parents=True,exist_ok=False)
    with zipfile.ZipFile(L/'source-only.zip') as z:
        assert all(not Path(n).is_absolute() and '..' not in Path(n).parts and not n.endswith(('.olean','.ilean','.ir','.so','.o')) for n in z.namelist())
        z.extractall(dest)
    hashes=json.loads((dest/'archive-files.json').read_text())
    for f,h in hashes.items():assert sha(dest/f)==h
    steps=[]
    for n in ['Literal', 'Terminal', 'Law', 'Cells', 'Product', 'Prefix', 'Marks', 'Boards', 'Injection', 'Abundance', 'Tail', 'Concentration', 'Assembly', 'LastSplit', 'SuffixUnion', 'Growth', 'Uniform', 'UniformSuffix']:
        _,r=run(dest,['-o',n+'.olean',n+'.lean']);steps.append(r)
    inv,r=run(dest,['--run','StandaloneAudit.lean']);steps.append(r)
    aud=inv
    names=inventory(inv);rows=audit(aud,names)
    assert names==json.loads((L/'owned-declarations.json').read_text())
    assert rows==json.loads((L/'audit.json').read_text())['declarations']
    for f,h in hashes.items():assert sha(dest/f)==h
    for p in L.rglob('*'):
        if p.suffix in {'.olean','.ilean','.ir','.o','.so'}:p.unlink()
    science();pins()
    (L/'replay-receipt.json').write_text(json.dumps(dict(status='PASS',archive_sha256=sha(L/'source-only.zip'),fresh_source_only=True,steps=steps,declarations=len(names),compiled_artifacts_removed=True),indent=2)+'\n')
    print('EXTRACTED REPLAY PASS',len(names))
elif mode=='manifest':
    science();pins()
    files={str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and str(p.relative_to(L)) not in ['MANIFEST.json','verification-receipt.json']}
    (L/'MANIFEST.json').write_text(json.dumps(files,indent=2)+'\n');print('MANIFEST',len(files))
elif mode=='verify':
    science();pins();files=json.loads((L/'MANIFEST.json').read_text())
    actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and str(p.relative_to(L)) not in ['MANIFEST.json','verification-receipt.json']}
    assert set(files)==actual
    for f,h in files.items():assert sha(L/f)==h,f
    assert not [p for p in L.rglob('*') if p.suffix in {'.olean','.ilean','.ir','.so','.o','.pyc'}]
    replay=json.loads((L/'replay-receipt.json').read_text());assert replay['status']=='PASS' and replay['archive_sha256']==sha(L/'source-only.zip')
    names=inventory((L/'replay/fresh/attempt-018.log').read_text())
    rows=audit((L/'replay/fresh/attempt-018.log').read_text(),names)
    a=json.loads((L/'audit.json').read_text());assert rows==a['declarations']
    (L/'verification-receipt.json').write_text(json.dumps(dict(status='PASS',manifest_sha256=sha(L/'MANIFEST.json'),files=len(files),declarations=len(names),origins=a['origins'],transitive=a['transitive'],all_nine_pins_unchanged=True,compiled_artifacts=0,scientific_status='CLOSED: uniform interval and literal suffix asymptotics; full-source and novelty HOLD',counts_changed=False),indent=2)+'\n')
    print('SEPARATE FINAL VERIFICATION PASS',a['origins'])
