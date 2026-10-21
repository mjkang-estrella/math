#!/usr/bin/env python3
"""Read-only whole-scope correctness intake; artifact checks are not math gates."""
import datetime,hashlib,importlib.util,json,stat,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parents[1];P=B.parents[2];R=B/'arithmetic-r147-proof-r1'
sp=importlib.util.spec_from_file_location('base',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_bytes())
def dump(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def main():
    anchors={'FINAL.md':'0deeee65e3d6c32f532e9f5990b93b362b516456960c5506c14a8f8c1a91f6a1','MANIFEST.json':'1a5825e289810684c0543bbcf38647c4ce4a06d0f18908cdf9ba1e786c9ea6a1','REPORT.md':'53d6600fb1eada202a24ca0330739e4559d7fcf9bf85836e62b78768de60f25e'}
    before=snap(R);mode=stat.S_IMODE(R.stat().st_mode);assert all(sha(R/p)==v for p,v in anchors.items())
    cmd=['python','-I','-B',str(R/'verify_packet.py'),'--root',str(R),'--final-sha256',anchors['FINAL.md'],'--manifest-sha256',anchors['MANIFEST.json'],'--report-sha256',anchors['REPORT.md'],'--originals-project',str(P)]
    run=subprocess.run(cmd,cwd=P,text=True,capture_output=True,check=True);assert not run.stderr
    m=read(R/'MANIFEST.json');selected={x['path'] for x in m['files']};assert len(selected)==len(m['files'])==70
    assert {p for p,x in before.items()if x['kind']=='file'}==selected|{'FINAL.md','MANIFEST.json','REPORT.md','ANCHORS.json'}
    tree=read(P/'sources/preprints-tree.json');lookup={e['path']:e for e in tree['tree']};assert len(lookup)==13223 and not tree['truncated'] and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    bindings=read(R/'private/source-authentication.json');assert len(bindings)==8
    for x in bindings:
        p=R/'private/source'/Path(x['path']).name;d=p.read_bytes();e=lookup[x['path']]
        assert len(d)==x['bytes']==e['size'] and sha(p)==x['sha256'] and hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()==x['blob']==e['sha']
    ranges=read(R/'private/original-anchors.json');assert len(ranges)==48;stable={};modes={};whole=0
    for x in ranges:
        p=P/x['original'];assert not p.is_symlink()and p.stat().st_nlink==1
        with p.open('rb')as f:f.seek(x['start']);data=f.read(x['end']-x['start'])
        assert len(data)==x['end']-x['start']and hashlib.sha256(data).hexdigest()==x['sha256']and stat.S_IMODE(p.stat().st_mode)==x['mode'];modes[x['original']]=x['mode']
        if x['start']==0 and x['end']==p.stat().st_size:stable[x['original']]=x['sha256'];whole+=1
    copies=read(R/'private/selected-copies.json')
    for x in copies:assert sha(R/x['copy'])==x['sha256']and(R/x['copy']).stat().st_size==x['end']-x['start']
    assert snap(R)==before and stat.S_IMODE(R.stat().st_mode)==mode
    dump(O/'observed-root.json',{'root':before,'root_mode':mode})
    report={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'artifact_only':True,'author_validator_stdout':run.stdout.strip(),'payload_files':70,'exact_whole_root_membership':True,'canonical_objects':8,'canonical_matches_complete_pinned_tree':True,'explicit_original_records':48,'whole_original_records':whole,'original_range_anchors':ranges,'stable_named_originals':stable,'stable_original_modes':modes,'selected_copy_records':len(copies),'entire_root_unchanged':True,'parent_semantic_reading':'Complete REVIEW, DERIVATIONS including its final discharge of the earlier Brieskorn checkpoint, FINAL, REPORT, READING-AND-ISOLATION and verifier. Actual primary/source reading attributed to reviewer; parent has not reread their protected bodies. No live contribution or Analytic177 findings/status/activity read or steered.'}
    dump(O/'replay.json',report);print(json.dumps({k:report[k]for k in ['payload_files','canonical_objects','explicit_original_records','whole_original_records','entire_root_unchanged','artifact_only']}))
if __name__=='__main__':main()
