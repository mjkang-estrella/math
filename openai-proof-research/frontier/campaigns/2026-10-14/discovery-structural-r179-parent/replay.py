#!/usr/bin/env python3
"""Read-only S179 copied-selection intake; integrity assigns no mathematical gate."""
import datetime,hashlib,importlib.util,json,stat,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-structural-discovery-r179'
sp=importlib.util.spec_from_file_location('snapshot',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_bytes())
def main():
    anchors={'private/FINAL.json':'a5c6287b2f47c5e5aa65c94833a85ae73d230bafe29bb1059b936d2d23fe8ad4','private/packet/MANIFEST.json':'bce2289aa1e6b34f4c651b3449b923d7914e90402e7892765e6dd787054b83fc','REPORT.md':'a8cd1e60c2ecb633b7ccb327628ec8ffa754d2e8736cc6329e61cb79cafbdc7d'}
    before=snap(ROOT);mode=stat.S_IMODE(ROOT.stat().st_mode);assert all(sha(ROOT/p)==v for p,v in anchors.items())
    r=subprocess.run(['python','-I','-B',str(ROOT/'private/verify_packet.py'),'--root',str(ROOT),'--final-sha256',anchors['private/FINAL.json'],'--manifest-sha256',anchors['private/packet/MANIFEST.json'],'--report-sha256',anchors['REPORT.md']],cwd=P,text=True,capture_output=True,check=True);assert not r.stderr
    manifest=read(ROOT/'private/packet/MANIFEST.json');assert len(manifest['files'])==54
    names={x['path']for x in manifest['files']};packet=ROOT/'private/packet';actual={p[len('private/packet/'):]for p,x in before.items()if x['kind']=='file'and p.startswith('private/packet/payload/')};assert actual==names
    for x in manifest['files']:
        relative=x['path'].removeprefix('payload/');assert relative!=x['path'];assert (ROOT/relative).read_bytes()==(packet/x['path']).read_bytes()
    tree=read(P/'sources/preprints-tree.json');lookup={x['path']:x for x in tree['tree']};assert not tree['truncated'] and len(lookup)==13223 and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    canonical=read(ROOT/'private/source-auth.json');assert len(canonical)==11;pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
    for x in canonical:
        path=x['url'].split('/'+pin+'/',1)[1];p=P/x['local'];d=p.read_bytes();e=lookup[path];assert p.resolve().is_relative_to(ROOT) and len(d)==x['bytes']==e['size'] and sha(p)==x['sha256'] and hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()==x['git_blob']==e['sha']
    stable={};direct=read(ROOT/'private/original-input-checks.json');assert len(direct)==7
    for x in direct:
        p=P/x['path'];assert sha(p)==x['sha256'];start,end=x.get('extent',x.get('selected_bytes',[0,p.stat().st_size]));assert start==0 and p.stat().st_size==end;stable[x['path']]=sha(p)
        if 'fresh-structural-discovery-r41/'in x['path']:copy=ROOT/'private/r41-original.txt'
        else:copy=ROOT/'private/completed-r178'/Path(x['path']).relative_to(B.relative_to(P))
        assert p.read_bytes()==copy.read_bytes()
    sections=read(ROOT/'private/history-extents.json');assert len(sections)==1
    for x in sections:
        p=P/x['path'];assert sha(p)==x['sha256'] and x['selected_bytes']==[0,p.stat().st_size]
    assert snap(ROOT)==before and stat.S_IMODE(ROOT.stat().st_mode)==mode
    (O/'observed-root.json').write_text(json.dumps({'root':before,'root_mode':mode},indent=2)+'\n')
    result={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'author_verifier_stdout':r.stdout.strip(),'parent_exact_packet_membership_checked':True,'payload_files':54,'canonical_objects':11,'completed_originals':6,'selected_original_sections':1,'all54selected_copies_match_working_originals':True,'unselected_working_acquisitions_navigation_controls_and_cache_remain_outside_sealed_selection':True,'stable_named_originals':stable,'entire_working_root_unchanged_by_replay':True,'entire_root_unchanged':True,'artifact_only':True,'parent_semantic_reading':'Complete REPORT/private FINAL/four mathematical notes/private reading-limits/verifier. Source and actual-primary semantic extents remain attributed to author; parent did not reread all their proofs. An initial parent replay assumed every original record had an extent field; the history record instead binds its whole original by hash, and that schema assumption was corrected. Exact membership concerns the copied54-member packet; the wider working directory is separately observed for immutability, not claimed wholly selected or sealed.'}
    (O/'replay.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'payload_files':54,'canonical_objects':11,'completed_originals':6,'selected_original_sections':1,'selected_copies_match':True,'working_root_unchanged':True,'artifact_only':True}))
if __name__=='__main__':main()
