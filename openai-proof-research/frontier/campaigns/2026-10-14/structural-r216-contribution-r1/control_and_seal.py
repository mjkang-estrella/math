"""Bounded controls and a one-time seal for this review only. No author writes."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import runpy
import stat
import subprocess

ROOT=Path('frontier/campaigns/2026-10-14/structural-r216-contribution-r1')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()

def dump(p,x):
    p.write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
    p.chmod(0o600)

def private_tree(root):
    root.chmod(0o700)
    for p in root.rglob('*'):
        assert not p.is_symlink()
        p.chmod(0o700 if p.is_dir() else 0o600)

def make_seal(root):
    for n in ('MANIFEST.json','SELECTION.json','ANCHORS.json'):
        assert not (root/n).exists(), 'Refuse reseal: '+str(root/n)
    entries=runpy.run_path(str(ROOT/'verify_packet.py'))['inventory'](root/'packet')
    dump(root/'SELECTION.json',{'schema':'structural216-review-selection-v1',
                              'entries':{x['path']:x['type'] for x in entries}})
    dump(root/'MANIFEST.json',{'schema':'structural216-review-manifest-v1',
                             'selection_sha256':sha(root/'SELECTION.json'),'entries':entries})
    anchors={key:sha(root/path) for key,path in {'FINAL':'packet/FINAL.md','MANIFEST':'MANIFEST.json',
              'SELECTION':'SELECTION.json','REPORT':'REPORT.md'}.items()}
    anchors['VERIFIER']=sha(ROOT/'verify_packet.py')
    dump(root/'ANCHORS.json',anchors)
    return anchors

def verify(root,anchors):
    args=['python','-B',str(ROOT/'verify_packet.py'),'--packet',str(root/'packet'),
          '--manifest',str(root/'MANIFEST.json'),'--selection',str(root/'SELECTION.json'),
          '--report',str(root/'REPORT.md')]
    for key in ('FINAL','MANIFEST','SELECTION','REPORT'):
        args.extend(['--'+key.lower()+'-sha',anchors[key]])
    p=subprocess.run(args,capture_output=True,text=True,check=False)
    return {'command':args,'returncode':p.returncode,'stdout':p.stdout,'stderr':p.stderr}

def originals_check():
    old=json.loads((ROOT/'packet/private/admitted-originals-before.json').read_text())
    changes=[]
    for x in old:
        p=Path(x['path']);s=p.stat()
        actual={'path':x['path'],'size':s.st_size,'mode':oct(stat.S_IMODE(s.st_mode)),'sha256':sha(p)}
        if actual!=x: changes.append({'before':x,'after':actual})
    assert not changes, changes
    return {'admitted_files':len(old),'bytes_modes_unchanged':True,'changes':changes,
            'scope':'Only the 55 exact selected author packet files and seven exact admitted outside files.',
            'author_writes':False,'mathematical_gate':False}

def controls():
    c=ROOT/'controls'
    c.mkdir(mode=0o700)
    (c/'packet/private').mkdir(parents=True,mode=0o700)
    (c/'packet/FINAL.md').write_bytes((ROOT/'packet/FINAL.md').read_bytes())
    target=c/'packet/private/tiny-copy.txt'
    target.write_bytes((ROOT/'packet/REVIEW.md').read_bytes()[:128])
    (c/'REPORT.md').write_text('Tiny copied artifact control only. No mathematical verdict.\n')
    private_tree(c)
    anchors=make_seal(c)
    out=[]
    def trial(name,expected,aa=anchors):
        result=verify(c,aa)
        assert result['returncode']==expected,(name,result)
        out.append({'name':name,'expected_returncode':expected,**result})
    trial('baseline',0)
    original=target.read_bytes()
    target.write_bytes(original+b'changed')
    trial('changed-copy-bytes',1)
    target.write_bytes(original)
    target.chmod(0o640)
    trial('changed-copy-mode',1)
    target.chmod(0o600)
    extra=c/'packet/extra.txt';extra.write_text('extra\n');extra.chmod(0o600)
    trial('extra-file',1)
    extra.unlink()
    wrong=dict(anchors);wrong['FINAL']='0'*64
    trial('wrong-explicit-final-anchor',1,wrong)
    trial('restored-original-control',0)
    dump(ROOT/'packet/private/CONTROL-RESULTS.json',{'controls':out,'mathematical_gate':False,
          'control_packet_uses_own_reduced_selection':True,'no_author_manifest_attached':True})
    print(json.dumps({'control_cases':len(out),'all_expected_outcomes':True}))

def seal():
    assert (ROOT/'REPORT.md').exists()
    dump(ROOT/'packet/private/admitted-originals-after.json',originals_check())
    private_tree(ROOT)
    anchors=make_seal(ROOT)
    result=verify(ROOT,anchors)
    assert result['returncode']==0,result
    dump(ROOT/'VERIFICATION.txt',result)
    assert originals_check()['bytes_modes_unchanged']
    print(json.dumps({'anchors':anchors,'verification':json.loads(result['stdout']),
                      'admitted_originals_unchanged':True},indent=2))

p=argparse.ArgumentParser();p.add_argument('action',choices=['controls','seal','originals'])
a=p.parse_args()
if a.action=='controls': controls()
elif a.action=='seal': seal()
else: print(json.dumps(originals_check(),indent=2))
