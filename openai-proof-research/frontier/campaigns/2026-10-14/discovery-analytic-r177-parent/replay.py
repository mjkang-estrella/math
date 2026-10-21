#!/usr/bin/env python3
"""Read-only Analytic177 selected-packet intake; no mathematical gate."""
import datetime,hashlib,importlib.util,json,stat,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];A=B/'fresh-analytic-discovery-r177'
sp=importlib.util.spec_from_file_location('base',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_bytes())
def dump(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def main():
    anchors={'FINAL.md':'24686f9527ab06dd82fa106e33a88a8a4b2f178a97ddbfd5589d863c72963eab','MANIFEST.json':'3edf22ab764e92dbc2af7c7a2c82f8be3db0946545bb2bed3c44c2225fb2607a','REPORT.md':'2dc4abdf2d47ec1ba96912bb4581d5741e843e315416255281b7c79d87ca61b8'}
    before=snap(A);mode=stat.S_IMODE(A.stat().st_mode);assert all(sha(A/p)==v for p,v in anchors.items())
    run=subprocess.run(['python','-I','-B',str(A/'VERIFY.py'),'--root',str(A),'--final-sha256',anchors['FINAL.md'],'--manifest-sha256',anchors['MANIFEST.json'],'--report-sha256',anchors['REPORT.md']],cwd=P,capture_output=True,text=True,check=True);assert not run.stderr
    m=read(A/'MANIFEST.json');selected={x['path']for x in m['files']};assert len(selected)==len(m['files'])==88 and {p for p,x in before.items()if x['kind']=='file'}==selected|{'MANIFEST.json','REPORT.md','ANCHORS.json'}
    tree=read(P/'sources/preprints-tree.json');lookup={e['path']:e for e in tree['tree']};assert len(lookup)==13223 and not tree['truncated']and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    bindings=read(A/'private/source-authentication.json');assert len(bindings)==24
    for x in bindings:
        p=P/x['local'];d=p.read_bytes();e=lookup[x['path']];assert p.resolve().is_relative_to(A.resolve())and len(d)==x['size']==e['size']and sha(p)==x['sha256']and hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()==x['sha']==e['sha']
    ranges=read(A/'private/original-extents.json');assert len(ranges)==6;stable={};modes={}
    for x in ranges:
        p=P/x['path'];assert not p.is_symlink()and p.stat().st_nlink==1
        with p.open('rb')as f:f.seek(x['start']);data=f.read(x['end']-x['start'])
        assert len(data)==x['end']-x['start']and hashlib.sha256(data).hexdigest()==x['sha256']and data==(A/x['local']).read_bytes();modes[x['path']]=stat.S_IMODE(p.stat().st_mode)
        if x['start']==0 and x['end']==p.stat().st_size:stable[x['path']]=x['sha256']
    completed=[('discovery-analytic-r176-parent/assessment.md','assessment'),*[(f'fresh-analytic-discovery-r176/{n}.md',n)for n in['FINAL','INTERFACES','HOLONOMY','ANNULAR','COMPARISON']],('fresh-analytic-discovery-r176/private/READING-LIMITS.md','READING-LIMITS')]
    for rel,name in completed:
        p=B/rel;c=A/('private/completed-r176-'+name+'.md');assert p.read_bytes()==c.read_bytes();stable[p.relative_to(P).as_posix()]=sha(p);modes[p.relative_to(P).as_posix()]=stat.S_IMODE(p.stat().st_mode)
    assert snap(A)==before and stat.S_IMODE(A.stat().st_mode)==mode
    dump(O/'observed-root.json',{'root':before,'root_mode':mode})
    report={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'artifact_only':True,'author_validator_stdout':run.stdout.strip(),'payload_files':88,'exact_whole_root_membership_and_modes_checked':True,'canonical_objects':24,'canonical_matches_complete_pinned_tree':True,'original_range_anchors':ranges,'selected_history_intervals':6,'selected_history_original_bodies':len({x['path']for x in ranges}),'completed_exception_records':7,'stable_named_originals':stable,'stable_original_modes':modes,'original_modes_observed_at_parent_intake_not_initial_child_reads':True,'entire_root_unchanged':True,'parent_semantic_reading':'Complete INTERFACES, DERIVATIONS, COMPARISON, FINAL, REPORT, READING-LIMITS and verifier; retained diagnostics read as finite algebra upper envelopes, not rerun as mathematical gates. Source and primary operative reading attributed to child; no fresh parent protected-body reread. No live Structural184/Arithmetic148 bodies/findings/status/activity inspected or steered.'}
    dump(O/'replay.json',report);print(json.dumps({k:report[k]for k in['payload_files','canonical_objects','selected_history_intervals','selected_history_original_bodies','completed_exception_records','entire_root_unchanged','artifact_only']}))
if __name__=='__main__':main()
