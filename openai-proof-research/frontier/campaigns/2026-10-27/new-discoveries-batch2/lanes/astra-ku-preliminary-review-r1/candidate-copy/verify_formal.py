#!/usr/bin/env python3
"""Fresh temporary-source compilation, declaration and axiom inspection.

This is a ROOT PRELIMINARY receipt, not independent review or packet acceptance.
"""
import hashlib, json, os, re, shutil, subprocess, tempfile
from pathlib import Path

LANE=Path(__file__).resolve().parent
LEAN=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
PACKAGES=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
PIN='d13f23b723b8a846827a245b89c10fc7d3f11612'
MODULES=['Counterexample','Moments','SourceUniform']

def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    revision=subprocess.check_output(['git','-C',str(PACKAGES/'mathlib'),'rev-parse','HEAD'],text=True).strip()
    assert revision==PIN,(revision,PIN)
    version=subprocess.check_output([str(LEAN),'--version'],text=True).strip()
    assert '4.34.1' in version
    out=LANE/'build'/'root-preliminary'
    out.mkdir(parents=True,exist_ok=True)
    declarations=[]
    hashes={}
    with tempfile.TemporaryDirectory(prefix='ku-torus-preliminary-') as td:
        work=Path(td)
        for name in MODULES:
            src=LANE/'formal'/f'{name}.lean'
            text=src.read_text()
            assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',text)
            declarations += re.findall(r'^(?:abbrev|def|theorem)\s+([A-Za-z0-9_]+)',text,re.M)
            hashes[src.name]=digest(src)
            shutil.copy2(src,work/src.name)
        checks='import SourceUniform\n'
        checks+='\n'.join(f'#check KuTorus.{n}\n#print axioms KuTorus.{n}' for n in declarations)+'\n'
        (work/'Checks.lean').write_text(checks)
        (out/'Checks.lean').write_text(checks)
        env=dict(os.environ)
        env['LEAN_PATH']=str(work)+':'+':'.join(str(p/'.lake/build/lib/lean')
            for p in sorted(PACKAGES.iterdir()) if (p/'.lake/build/lib/lean').is_dir())
        for name in MODULES+['Checks']:
            result=subprocess.run([str(LEAN),'-DwarningAsError=true','-o',f'{name}.olean',f'{name}.lean'],
                cwd=work,env=env,text=True,capture_output=True,timeout=1800)
            log=result.stdout+result.stderr
            (out/f'{name}.log').write_text(log)
            assert result.returncode==0,(name,log)
            if name!='Checks': assert log=='',(name,log)
        log=(out/'Checks.log').read_text()
        reports=re.findall(r"'KuTorus\.([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log)
        assert len(reports)==len(declarations),(len(reports),len(declarations))
        for name,axioms in reports:
            assert set(axioms.split(', '))-{''} <= {'propext','Classical.choice','Quot.sound'},(name,axioms)
        audit=dict(status='PASS',scope='root preliminary fresh replay; credit 0',lean=version,
                   mathlib=revision,modules=MODULES,declaration_count=len(declarations),
                   declarations=declarations,source_sha256=hashes,checks_log_sha256=digest(out/'Checks.log'))
        (out/'audit.json').write_text(json.dumps(audit,indent=2)+'\n')
        print(json.dumps(audit,indent=2))

if __name__=='__main__': main()
