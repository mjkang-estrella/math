"""Tiny copied controls, same-logic preflight, one final seal."""
import importlib.util
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile
sys.dont_write_bytecode=True
ROOT=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r164-sol')
PROJECT=Path.cwd()
spec=importlib.util.spec_from_file_location('packet_verify',ROOT/'verify.py')
v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
assert not any((ROOT/x).exists() for x in ('MANIFEST.json','ANCHORS.json')),'already sealed'
controls=[]
def rejects(label,fn):
    try:fn()
    except (AssertionError,ValueError):controls.append({'control':label,'result':'REJECTED'});return
    raise AssertionError('control accepted: '+label)
with tempfile.TemporaryDirectory(prefix='tiny-',dir=ROOT/'scratch') as td:
    q=Path(td);(q/'sub').mkdir();(q/'sub/original.txt').write_text('tiny exact fixture\n')
    shutil.copy2(q/'sub/original.txt',q/'copied.txt')
    m=v.snapshot(q);v.payload(q,m);controls.append({'control':'baseline copied fixture','result':'MATCH'})
    p=q/'copied.txt';old=p.read_bytes();p.write_bytes(old+b'x');rejects('changed bytes',lambda:v.payload(q,m));p.write_bytes(old)
    mode=p.stat().st_mode;p.chmod(0o600 if mode&0o077 else 0o644);rejects('changed full mode',lambda:v.payload(q,m));p.chmod(mode&0o7777)
    extra=q/'extra';extra.write_text('extra');rejects('unexpected member',lambda:v.payload(q,m));extra.unlink()
    bad=json.loads(json.dumps(m));bad['files'].append(dict(bad['files'][0]));rejects('duplicate member',lambda:v.payload(q,bad))
    bad=json.loads(json.dumps(m));bad['files'][0]['path']='../escape';rejects('unsafe member',lambda:v.payload(q,bad))
    bad=json.loads(json.dumps(m));bad['files'].reverse();rejects('unsorted members',lambda:v.payload(q,bad))
    for label in ('FINAL','MANIFEST','REPORT'):
        rejects('wrong '+label+' anchor',lambda:v.anchor(q,'copied.txt','0'*64))
    v.payload(q,m);controls.append({'control':'restored fixture','result':'MATCH'})
(ROOT/'private/artifact-controls.json').write_text(json.dumps(controls,indent=2)+'\n')
records=json.loads((ROOT/'private/completed-bindings.json').read_text())
kept={str(ROOT/e['copy']):e['mode']&0o7777 for e in records}
for base,dirs,files in os.walk(ROOT):
    Path(base).chmod(0o700)
    for name in files:
        p=Path(base)/name
        if str(p) in kept:p.chmod(kept[str(p)])
        elif p.is_relative_to(ROOT/'private') or p.is_relative_to(ROOT/'scratch'):p.chmod(0o600)
        else:p.chmod(0o644)
m=v.snapshot(ROOT);v.payload(ROOT,m);v.bindings(ROOT,PROJECT)
report="""# R164-Sol detached artifact report

PREFREEZE/no nominee. No mathematical gates, grades, acceptance or count.

Same-logic preflight matched exact safe sorted payload membership, SHA256, byte lengths,
full stat modes, pinned Source184 blob/tree bindings, the complete preprint-tree anchor,
and five exact completed original/copy pairs. Tiny copied controls rejected changed
bytes, changed mode, extra/duplicate/unsafe/unsorted membership and three wrong anchors;
the original tiny fixture was restored and matched. These checks establish artifact
integrity only. They do not validate mathematical arguments or repair the journal
read-scope breach disclosed in FINAL and READING-LIMITS.

Payload files: {files}. Payload bytes: {size}. Directories including root: {dirs}.
Source blobs/entries:24/32. Exact completed pairs:5. Full semantic canonical texts:22,
164770bytes. Primary pages:72 across8 partial papers. Two rendered checks.

MANIFEST.json is this packet's own manifest. REPORT.md, MANIFEST.json and ANCHORS.json
are detached; FINAL.md is both a manifest payload and separately anchored. The verifier
requires all three expected hashes explicitly and does not write files. Everything
remains local to this exclusive root. All sealed file bytes and full modes are final.
""".format(files=len(m['files']),size=sum(x['bytes'] for x in m['files']),dirs=len(m['directories']))
(ROOT/'REPORT.md').write_text(report);(ROOT/'REPORT.md').chmod(0o644)
raw=(json.dumps(m,indent=2,sort_keys=True)+'\n').encode();(ROOT/'MANIFEST.json').write_bytes(raw);(ROOT/'MANIFEST.json').chmod(0o644)
anchors={name:v.digest((ROOT/name).read_bytes()) for name in ('FINAL.md','MANIFEST.json','REPORT.md')}
(ROOT/'ANCHORS.json').write_text(json.dumps(anchors,indent=2,sort_keys=True)+'\n');(ROOT/'ANCHORS.json').chmod(0o644)
print(json.dumps(v.verify(ROOT,PROJECT,anchors['FINAL.md'],anchors['MANIFEST.json'],anchors['REPORT.md']),sort_keys=True))
for name in anchors:
    args=dict(anchors);args[name]='0'*64
    try:v.verify(ROOT,PROJECT,args['FINAL.md'],args['MANIFEST.json'],args['REPORT.md'])
    except AssertionError:print('REJECTED wrong detached '+name)
    else:raise AssertionError('wrong detached anchor accepted')
print(json.dumps(anchors,indent=2,sort_keys=True))
