#!/usr/bin/env python3
"""Extract the exact source-only packet and compile sequentially with pinned Lean."""
import argparse, gzip, hashlib, io, json, os, re, subprocess, sys, tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
LEAN = Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
LEAN_SHA = 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
MATHLIB = Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib')
MATHLIB_COMMIT = 'd13f23b723b8a846827a245b89c10fc7d3f11612'
MODULES = ['BinaryDigits','Filtration','Riccati','NonSubring','MidpointAlgebra','MidpointSequence','MidpointParity','MidpointNormalForm','MidpointRational','OddTriangular','MidpointPrimitive','OddPrimitiveSequence']
AUDITS = ['OddPrimitiveAudit','MidpointAudit','FiltrationAudit','OddPrimitiveInventory']
ALLOW = {'propext','Classical.choice','Quot.sound'}
FORBIDDEN = re.compile(r'\b(?:sorry|admit|axiom|unsafe|native_decide|run_tac|implemented_by)\b')

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def package():
    files = sorted([*(ROOT/'formal').glob('*.lean'), ROOT/'formal/run_lean.py', ROOT/'formal/guard.py'], key=lambda p:p.name)
    manifest = {p.name:sha(p) for p in files}
    for p in files:
        if p.suffix == '.lean':
            assert not FORBIDDEN.search(p.read_text()), ('forbidden source token',p)
    buf = io.BytesIO()
    with tarfile.open(fileobj=buf, mode='w', format=tarfile.USTAR_FORMAT) as tf:
        for p in files:
            raw=p.read_bytes(); ti=tarfile.TarInfo(p.name)
            ti.size=len(raw); ti.mode=0o644; ti.uid=ti.gid=ti.mtime=0
            tf.addfile(ti,io.BytesIO(raw))
    with (ROOT/'formal-source.tar.gz').open('wb') as out:
        with gzip.GzipFile(filename='',fileobj=out,mode='wb',mtime=0) as gz: gz.write(buf.getvalue())
    (ROOT/'source-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    return manifest

def parse_audit(path,expected):
    s=path.read_text()
    assert not re.search(r'\b(?:error|warning):',s),path
    reports={}
    for m in re.finditer(r"^'([^']+)' (?:depends on axioms: (\[[^\]]*\])|does not depend on any axioms)",s,re.M):
        n=m.group(1); ax=set(re.findall(r'[A-Za-z_][A-Za-z0-9_.]*',m.group(2) or ''))
        assert n not in reports,('duplicate axiom report',n)
        assert ax<=ALLOW,(n,ax)
        reports[n]=sorted(ax)
    assert set(reports)==set(expected),('axiom inventory mismatch',set(expected)-set(reports),set(reports)-set(expected))
    checks=[]
    for n in expected:
        assert re.search(r'^'+re.escape(n)+r'(?:\.\{[^}]*\})?(?:\s|:)',s,re.M),('missing #check output',n)
        checks.append(n)
    return {'reports':reports,'all_expected_checks_present':True}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',default='verification/fresh');args=ap.parse_args()
    out=(ROOT/args.output).resolve()
    assert out.is_relative_to(ROOT) and not out.exists(), 'Use a fresh directory inside this lane.'
    assert sha(LEAN)==LEAN_SHA
    gitdir=MATHLIB/'.git'
    head=(gitdir/'HEAD').read_text().strip()
    if head.startswith('ref: '): head=(gitdir/head[5:]).read_text().strip()
    assert head==MATHLIB_COMMIT
    manifest=package()
    out.mkdir(parents=True);source=out/'source';source.mkdir();logs=out/'logs';logs.mkdir()
    receipt={'source_archive_sha256':sha(ROOT/'formal-source.tar.gz'),'lean_sha256':sha(LEAN),
             'mathlib_head':head,'initial_local_oleans':[], 'builds':[], 'success':False}
    receipt_path=out/'receipt.json'
    def save(): receipt_path.write_text(json.dumps(receipt,indent=2)+'\n')
    with tarfile.open(ROOT/'formal-source.tar.gz','r:gz') as tf:
        for m in tf.getmembers():
            assert m.isfile() and Path(m.name).name==m.name and m.name in manifest
            data=tf.extractfile(m).read();(source/m.name).write_bytes(data)
    assert not list(source.rglob('*.olean'))
    assert {p.name:sha(p) for p in source.iterdir()}==manifest
    save()
    for idx,module in enumerate(MODULES+AUDITS,1):
        log=logs/f'{idx:02d}-{module}.log'
        args=[module+'.lean']+(['-o',module+'.olean'] if module in MODULES else [])
        with (logs/f'{idx:02d}-{module}.runner.log').open('w') as runner:
            p=subprocess.run([sys.executable,'guard.py',str(log),*args],cwd=source,stdout=runner,stderr=subprocess.STDOUT)
        stats=json.loads(log.with_suffix(log.suffix+'.json').read_text())
        receipt['builds'].append({'module':module,**stats}); save()
        assert p.returncode==0 and stats['exit_code']==0 and not stats['guard_killed'],module
        if module in MODULES: assert log.read_text()=='', ('nonempty proof log',module)
        print(module+': PASS',flush=True)
    names=[x['name'] for x in json.loads((ROOT/'declarations.json').read_text())]
    receipt['odd_primitive_audit']=parse_audit(logs/'13-OddPrimitiveAudit.log',names)
    for module,idx in [('MidpointAudit',14),('FiltrationAudit',15)]:
        dep_src=(source/(module+'.lean')).read_text()
        dep_names=re.findall(r'^#check ([\w.]+)',dep_src,re.M)
        receipt[module]=parse_audit(logs/f'{idx:02d}-{module}.log',dep_names)
    inv=(logs/'16-OddPrimitiveInventory.log').read_text()
    actual=set(re.findall(r'^ODD_PRIMITIVE_DECL (.+)$',inv,re.M))
    assert actual==set(names),('fresh environment inventory mismatch',actual^set(names))
    safety=dict(re.findall(r'^ODD_PRIMITIVE_SAFETY (\S+) (true|false)$',inv,re.M))
    assert set(safety)==actual and all(v=='false' for v in safety.values())
    origins=dict(re.findall(r'^ODD_PRIMITIVE_MODULE (\S+) (\S+)$',inv,re.M))
    expected_origins={x['name']:x['source_module'] for x in json.loads((ROOT/'declarations.json').read_text())}
    assert origins==expected_origins
    receipt['all_new_declarations_inventory_coverage']=len(actual)
    receipt['new_declaration_modules']=sorted(set(origins.values()))
    receipt['all_new_declarations_safe']=True
    receipt['final_source_hashes_unchanged']={p.name:sha(p) for p in source.iterdir() if p.name in manifest}==manifest
    assert receipt['final_source_hashes_unchanged']
    receipt['sampled_peak_rss_kib']=max(x['sampled_peak_rss_kib'] for x in receipt['builds'])
    receipt['success']=True;save()
    print('Fresh source-only replay: PASS',flush=True)

if __name__=='__main__':main()
