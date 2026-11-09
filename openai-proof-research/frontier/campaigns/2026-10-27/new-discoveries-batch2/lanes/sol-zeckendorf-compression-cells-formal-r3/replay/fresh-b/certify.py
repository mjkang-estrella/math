from pathlib import Path
import hashlib, json, re, sys, subprocess, zipfile
from package import checkpins
L=Path(__file__).resolve().parent
GUARD=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def science():
    rows=json.loads((L/'source-bindings.json').read_text())
    for r in rows:
        assert sha(Path(r['original']))==r['sha256']==sha(L/r['copy']),r
    for n in ['Literal.lean','Terminal.lean','Law.lean']:
        assert (L/n).read_bytes()==(L/'frozen/sol-zeckendorf-terminal-normalized-law-formal-r2'/n).read_bytes()
    for r in json.loads((L/'immutable-references.json').read_text()):
        assert sha(Path(r['original']))==r['sha256']==sha(Path(r['copy']))
    return len(rows)
def inventory(log):
    names=sorted(re.findall(r'^OWN_DECL (\S+)$',log,re.M))
    for kind in ['SAFETY','PARTIAL']:
        flags=dict(re.findall(r'^OWN_'+kind+r' (\S+) (true|false)$',log,re.M))
        assert set(flags)==set(names)
        if kind=='SAFETY':assert set(flags.values())=={'false'}
    assert len(names)==len(set(names)) and len(names)>295
    inherited=json.loads((L/'frozen/sol-zeckendorf-terminal-normalized-law-formal-r2/owned-declarations.json').read_text())
    assert len(inherited)==295 and set(inherited)<=set(names)
    return names
def audit(log,names):
    ax={n:re.findall(r'[\w.]+',a) for n,a in re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",log,re.M)}
    empty=re.findall(r"^'([^']+)' does not depend on any axioms$",log,re.M)
    assert set(names)==set(ax)|set(empty)
    assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in ax.values())
    return [dict(name=n,axioms=ax.get(n,[]),unsafe=False) for n in names]
def run(dest,args):
    result=subprocess.run([sys.executable,str(GUARD),sys.executable,str(dest/'runner.py'),*args],cwd=dest,stdout=subprocess.DEVNULL)
    assert result.returncode==0,(dest,args)
    rec=json.loads(sorted(dest.glob('attempt-*.json'))[-1].read_text())
    assert rec['exit']==0 and rec['reason'] is None and rec['peak_group_rss']<=2800*1024**2
    return rec
mode=sys.argv[1]
if mode=='pack':
    science();pins=checkpins()
    logs=[p.read_text() for p in sorted(L.glob('attempt-*.log'))]
    inv=next(t for t in reversed(logs) if 'OWN_DECL ' in t)
    names=inventory(inv)
    aud=next(t for t in reversed(logs) if 'depends on axioms:' in t)
    rows=audit(aud,names)
    partial=dict(re.findall(r'^OWN_PARTIAL (\S+) (true|false)$',inv,re.M))
    for row in rows:row['partial']=partial[row['name']]=='true'
    assert all(not row['partial'] for row in rows if row['name'] not in json.loads((L/'frozen/sol-zeckendorf-terminal-normalized-law-formal-r2/owned-declarations.json').read_text()))
    (L/'owned-declarations.json').write_text(json.dumps(names,indent=2)+'\n')
    (L/'audit.json').write_text(json.dumps(dict(status='HOLD: inherited generated partial declarations violate requested rule',inherited=295,total=len(names),declarations=rows,transitive_partial=sorted(set(re.findall(r'^REJECTED_TRANSITIVE_PARTIAL (\S+)$',inv,re.M))),transitive_safety='every origin type and body recursively traversed; unsafe rejected; every partial flagged, no exemption claimed'),indent=2)+'\n')
    (L/'pins.json').write_text(json.dumps(pins,indent=2)+'\n')
    files=['Literal.lean','Terminal.lean','Law.lean','Cells.lean','Inventory.lean','Audit.lean','runner.py','package.py','certify.py','RUN.md','SUMMARY.md','pins.json','administrative/lake-manifest.json']
    hashes={f:sha(L/f) for f in files}
    (L/'archive-files.json').write_text(json.dumps(hashes,indent=2)+'\n')
    with zipfile.ZipFile(L/'source-only.zip','w') as z:
        for f in files+['archive-files.json']:
            i=zipfile.ZipInfo(f,date_time=(2026,10,30,0,0,0));i.compress_type=zipfile.ZIP_DEFLATED;i.external_attr=0o100644<<16
            z.writestr(i,(L/f).read_bytes())
    print('pack',len(names),sha(L/'source-only.zip'))
elif mode=='replay':
    science();checkpins();results=[]
    for tag in ['fresh-a','fresh-b']:
        dest=L/'replay'/tag;dest.mkdir(parents=True,exist_ok=False)
        with zipfile.ZipFile(L/'source-only.zip') as z:
            assert all(not Path(n).is_absolute() and '..' not in Path(n).parts for n in z.namelist())
            assert all(not n.endswith(('.olean','.ilean','.ir','.so','.o')) for n in z.namelist())
            z.extractall(dest)
        files=json.loads((dest/'archive-files.json').read_text())
        for f,h in files.items():assert sha(dest/f)==h
        steps=[]
        for name in ['Literal','Terminal','Law','Cells']:
            steps.append(run(dest,['-o',name+'.olean',name+'.lean']))
        steps.append(run(dest,['Inventory.lean']));steps.append(run(dest,['Audit.lean']))
        names=inventory((dest/'attempt-004.log').read_text())
        assert names==json.loads((L/'owned-declarations.json').read_text())
        audit((dest/'attempt-005.log').read_text(),names)
        for f,h in files.items():assert sha(dest/f)==h
        for p in dest.rglob('*'):
            if p.suffix in {'.olean','.ilean','.ir','.o','.so'}:p.unlink()
        results.append(dict(extraction=tag,steps=steps,declarations=len(names),inventory_sha256=sha(dest/'attempt-004.log'),audit_sha256=sha(dest/'attempt-005.log'),compiled_artifacts_removed=True))
    assert results[0]['inventory_sha256']==results[1]['inventory_sha256']
    assert results[0]['audit_sha256']==results[1]['audit_sha256']
    for p in L.glob('*.olean'):p.unlink()
    science();checkpins()
    (L/'replay-receipt.json').write_text(json.dumps(dict(status='PASS',archive_sha256=sha(L/'source-only.zip'),deterministic_diagnostics=True,replays=results),indent=2)+'\n')
    print('PASS two fresh replays')
elif mode=='manifest':
    science();checkpins()
    files={str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and p not in [L/'MANIFEST.json',L/'verification-receipt.json']}
    (L/'MANIFEST.json').write_text(json.dumps(files,indent=2)+'\n');print('manifest',len(files))
elif mode=='verify':
    files=json.loads((L/'MANIFEST.json').read_text())
    actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p not in [L/'MANIFEST.json',L/'verification-receipt.json']}
    assert set(files)==actual
    for f,h in files.items():assert sha(L/f)==h,f
    count=science();pins=checkpins()
    assert pins==json.loads((L/'pins.json').read_text())
    assert not [p for p in L.rglob('*') if p.suffix in {'.olean','.ilean','.ir','.so','.o','.pyc'}]
    replay=json.loads((L/'replay-receipt.json').read_text());assert replay['status']=='PASS'
    assert replay['archive_sha256']==sha(L/'source-only.zip')
    inv=(L/'replay/fresh-a/attempt-004.log').read_text();names=inventory(inv)
    rows=audit((L/'replay/fresh-a/attempt-005.log').read_text(),names)
    stored=json.loads((L/'audit.json').read_text())
    partial=dict(re.findall(r'^OWN_PARTIAL (\S+) (true|false)$',inv,re.M))
    for row in rows:row['partial']=partial[row['name']]=='true'
    assert rows==stored['declarations']
    origins={}
    for m in re.findall(r'^OWN_MODULE \S+ (\S+)$',inv,re.M):origins[m]=origins.get(m,0)+1
    (L/'verification-receipt.json').write_text(json.dumps(dict(status='HOLD: verified partial packet, inherited generated partial declarations remain',manifest_sha256=sha(L/'MANIFEST.json'),files=len(files),source_bindings_verified=count,declarations=len(names),origins=origins,transitive_safe_constants=int(re.search(r'TRANSITIVE_SAFE_COUNT (\d+)',inv)[1]),all_nine_pins=pins,source_only_archive_sha256=sha(L/'source-only.zip'),fresh_extracted_replays=2,compiled_artifacts=0,scientific_status='PARTIAL: exhaustive partition and actual weights proved; closed cell-mass product and Bernoulli normalization remain',counts_changed=False),indent=2)+'\n')
    print('VERIFIED partial packet; strict generated-partial gate HOLD',origins)
