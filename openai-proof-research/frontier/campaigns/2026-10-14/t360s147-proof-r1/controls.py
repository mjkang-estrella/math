#!/usr/bin/env python3
"""Six small disposable-copy integrity controls; does not run mathematical tests."""
from pathlib import Path
import hashlib
import json
import os
import shutil
import stat
import subprocess
import sys

ROOT=Path('frontier/campaigns/2026-10-14/t360s147-proof-r1')
FIXTURE=ROOT/'private/controls/fixture'
def sha(data): return hashlib.sha256(data).hexdigest()
def snapshot(root):
    out={}
    for p in [root]+sorted(root.rglob('*')):
        st=p.lstat()
        row={'mode':stat.S_IMODE(st.st_mode),'links':st.st_nlink,'mtime_ns':st.st_mtime_ns}
        if p.is_file(): row.update(size=st.st_size,sha256=sha(p.read_bytes()))
        out['.' if p==root else p.relative_to(root).as_posix()]=row
    return out

def main():
    if FIXTURE.exists(): raise ValueError('control fixture already exists; no resealing')
    FIXTURE.mkdir(parents=True)
    selections=[(ROOT/'private/author/STATEMENT.md','STATEMENT.md'),(ROOT/'verify.py','verify.py')]
    files=[]
    for original,name in selections:
        b=original.read_bytes(); (FIXTURE/name).write_bytes(b)
        assert (FIXTURE/name).read_bytes()==b
        files.append({'path':name,'size':len(b),'sha256':sha(b)})
    (FIXTURE/'FINAL.md').write_text('Independent two-file disposable selection; integrity only.\n')
    (FIXTURE/'REPORT.md').write_text('Selected statement copy plus verifier; no inherited author archive seal.\n')
    (FIXTURE/'MANIFEST.json').write_text(json.dumps({'excluded_envelopes':['FINAL.md','MANIFEST.json','REPORT.md'],'files':files},indent=2)+'\n')
    anchors={n:sha((FIXTURE/n).read_bytes()) for n in ['FINAL.md','MANIFEST.json','REPORT.md']}
    baseline=(FIXTURE/'STATEMENT.md').read_bytes()
    results=[]
    def run(label,expected,wrong=False):
        before=snapshot(FIXTURE)
        cmd=[sys.executable,str(FIXTURE/'verify.py'),str(FIXTURE),'--final-sha256',anchors['FINAL.md'],'--manifest-sha256',('0'*64 if wrong else anchors['MANIFEST.json']),'--report-sha256',anchors['REPORT.md']]
        result=subprocess.run(cmd,cwd=Path.cwd(),capture_output=True,text=True,timeout=30)
        after=snapshot(FIXTURE)
        accepted=result.returncode==0
        assert accepted==expected and before==after
        results.append({'control':label,'expected_accept':expected,'accepted':accepted,'read_only_snapshot_match':before==after,'stdout':result.stdout.strip(),'stderr_tail':result.stderr[-220:]})
    run('baseline',True)
    (FIXTURE/'STATEMENT.md').write_bytes(baseline+b'changed copy\n')
    run('changed selected payload',False)
    (FIXTURE/'STATEMENT.md').write_bytes(baseline)
    (FIXTURE/'STATEMENT.md').unlink()
    run('missing selected payload',False)
    (FIXTURE/'STATEMENT.md').write_bytes(baseline)
    (FIXTURE/'.hidden-extra').write_text('unlisted\n')
    run('hidden extra payload',False)
    (FIXTURE/'.hidden-extra').unlink()
    run('wrong detached manifest anchor',False,True)
    run('restored',True)
    record={'selection':'fresh independently enumerated two-file fixture, not an inherited archive seal','anchors':anchors,'controls':results,'snapshot_scope':'file bytes, file/directory/root modes, hardlink counts and modification times; excludes access times','mathematical_gate':False}
    (ROOT/'CONTROL-RESULTS.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps({'controls':len(results),'all_expected_outcomes':True,'all_invocations_read_only':True,'mathematical_gate':False}))
if __name__=='__main__': main()
