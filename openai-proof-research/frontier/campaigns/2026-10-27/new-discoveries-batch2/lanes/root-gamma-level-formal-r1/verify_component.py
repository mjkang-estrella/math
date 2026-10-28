#!/usr/bin/env python3
"""Fresh source replay of supporting Jensen component, not a source endpoint."""
from pathlib import Path
import tempfile,shutil,subprocess,json,hashlib,re

base=Path(__file__).resolve().parent
p=base/'formal'
mods=['GammaDefs','ProfileConvex','StrictJensen','ConvexAssembly']
out=base/'verification';out.mkdir(exist_ok=True)
with tempfile.TemporaryDirectory(prefix='gamma-jensen-fresh-') as tmp:
    t=Path(tmp)
    for f in [*(m+'.lean' for m in mods),'Checks.lean','run_lean.py']:
        shutil.copy2(p/f,t/f)
    for mod in mods:
        r=subprocess.run(['python3','run_lean.py',mod+'.lean','-o',mod+'.olean'],cwd=t,capture_output=True,text=True)
        (out/(mod+'.log')).write_text(r.stdout+r.stderr)
        assert r.returncode==0 and not r.stdout and not r.stderr,(mod,r.returncode,r.stdout,r.stderr)
    r=subprocess.run(['python3','run_lean.py','Checks.lean'],cwd=t,capture_output=True,text=True)
    assert r.returncode==0 and not r.stderr
    (out/'Checks.log').write_text(r.stdout)
    reports=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",r.stdout)
    assert len(reports)==17
    allowed={'propext','Classical.choice','Quot.sound'}
    for n,ax in reports:
        assert set(ax.split(', '))<=allowed,(n,ax)
    sources={m+'.lean':hashlib.sha256((t/(m+'.lean')).read_bytes()).hexdigest() for m in mods}
    (out/'audit.json').write_text(json.dumps({'status':'PASS component only; no literal source endpoint','modules':4,'declarations':17,'warnings_as_errors':True,'fresh_copy':True,'actual_types_and_axioms_read_by_root':True,'allowed_axioms':sorted(allowed),'source_hashes':sources},indent=2)+'\n')
    print('PASS fresh copy: 4 modules,17 declarations; full source endpoint NOT proved')
