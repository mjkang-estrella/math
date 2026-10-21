#!/usr/bin/env python3
"""Proportionate selected-copy controls; mutates only own private/controls."""
from pathlib import Path
import hashlib,json,runpy,stat
ROOT=Path(__file__).resolve().parents[1]
v=runpy.run_path(str(ROOT/'tools/verify.py'))
control=ROOT/'private/controls/selected-copy'
control.mkdir(exist_ok=True)
source=ROOT/'notes/01-mathematical-checks.md'
original=source.read_bytes();st=source.stat()
p=control/'selected-note.md';p.write_bytes(original)
for name in ['FINAL.md','REPORT.md']:(control/name).write_text('Selected-copy artifact control only. No mathematical verdict.\n')
(control/'MANIFEST.json').write_text(json.dumps({'schema':v['SCHEMA'],**v['inventory'](control)},indent=2)+'\n')
anchors=[v['sha'](control/n) for n in v['ENVELOPES']]
results=[]
def check(name,expected,aa=anchors):
    try:v['verify'](control,aa);actual=True;message='verified'
    except Exception as e:actual=False;message=str(e)
    assert actual==expected,(name,actual,expected)
    results.append({'case':name,'expected_accept':expected,'actual_accept':actual,'message':message})
check('clean selected copy',True)
p.write_bytes(original+b'changed\n');check('payload byte mutation',False);p.write_bytes(original)
extra=control/'extra.txt';extra.write_text('extra');check('extra member',False);extra.unlink()
wrong=list(anchors);wrong[0]='0'*64;check('wrong detached FINAL anchor',False,wrong)
mode=stat.S_IMODE(p.stat().st_mode);p.chmod(mode^0o100);check('payload mode mutation',False);p.chmod(mode)
assert source.read_bytes()==original
now=source.stat();assert (st.st_mode,st.st_nlink,st.st_mtime_ns)==(now.st_mode,now.st_nlink,now.st_mtime_ns)
assert v['verify'](control,anchors)
(ROOT/'private/copied-control-results.json').write_text(json.dumps({'controls':results,'selected_copy_anchors':dict(zip(v['ENVELOPES'],anchors)),'original_selected_note_bytes_mode_nlink_mtime_unchanged':True,'rights':'This selected copy has its own manifest; no incoming author manifest inherited.'},indent=2)+'\n')
print('Five selected-copy controls matched expected artifact outcomes; original note unchanged.')
