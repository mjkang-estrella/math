#!/usr/bin/env python3
"""Bounded private synthetic copied controls, never against author originals."""
from pathlib import Path
import hashlib, json, runpy, shutil, subprocess, sys
sys.dont_write_bytecode = True
r = Path(__file__).resolve().parent
v = runpy.run_path(str(r/'verify_packet.py'))
d = r/'private/controls'
d.mkdir(exist_ok=True)
base = d/'baseline'
base.mkdir(exist_ok=False)
shutil.copy2(r/'private/author/FROZEN-STATEMENT.md', base/'frozen-copy.md')
shutil.copy2(r/'private/source/preprints/Sharp-integral-fillings-in-CAT(0)-spaces-September-23-2026/build/main.tex', base/'source-main-copy.tex')
(base/'FINAL.md').write_text('Synthetic copied control only. No mathematical verdict.\n')
(base/'REPORT.md').write_text('Synthetic fixture, independently selected membership; not an inherited manifest.\n')
files, dirs = v['inventory'](base)
m = {'format':'analytic161-independent-selected-packet-v1', 'outside_envelopes':sorted(v['ENVELOPES']), 'directories':dirs, 'files':[files[x] for x in sorted(files)]}
(base/'MANIFEST.json').write_text(json.dumps(m,indent=2)+'\n')
anchors = {name:hashlib.sha256((base/name).read_bytes()).hexdigest() for name in v['ENVELOPES']}
results=[]
def check(name, path, expect):
    try:
        result=v['verify'](path,anchors);ok=True
    except Exception as e:
        result={'verified':False,'reason':str(e)};ok=False
    assert ok is expect, (name,result)
    results.append({'case':name,'expected_verified':expect,'observed':result})
check('baseline',base,True)
for name in ['changed-bytes','extra-file','missing-file','changed-mode','changed-envelope','extra-empty-directory']:
    p=d/name;shutil.copytree(base,p)
    if name=='changed-bytes':
        f=p/'frozen-copy.md';f.write_bytes(f.read_bytes()+b'\nMUTATION\n')
    elif name=='extra-file':(p/'unlisted.txt').write_text('extra\n')
    elif name=='missing-file':(p/'source-main-copy.tex').unlink()
    elif name=='changed-mode':(p/'frozen-copy.md').chmod(0o600)
    elif name=='changed-envelope':(p/'FINAL.md').write_text('changed envelope\n')
    elif name=='extra-empty-directory':(p/'unlisted-directory').mkdir()
    check(name,p,False)
(r/'private/CONTROL-RESULTS.json').write_text(json.dumps({'anchors':anchors,'cases':results,'meaning':'mechanical verifier controls only, no mathematical gate'},indent=2)+'\n')
print(json.dumps({'control_cases':len(results),'all_expected_outcomes':True,'author_mutations':0}))
