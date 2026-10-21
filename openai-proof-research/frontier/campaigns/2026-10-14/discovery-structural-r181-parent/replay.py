#!/usr/bin/env python3
"""Read-only Structural181 exact-selection intake; artifact checks assign no gate."""
import datetime,hashlib,importlib.util,json,stat,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-structural-discovery-r181'
sp=importlib.util.spec_from_file_location('snapshot',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_bytes())
def main():
    anchors={'FINAL.json':'34a3d8333cba7291851ae20e19e6f3ebe21591cfb1ef4336d142c3951fa14c32','packet/MANIFEST.json':'da16cf238930f3d610ba34edf95d5a25dd142163b09cf9a8644681bc7fa95ddd','REPORT.md':'73392225bf163d78e908a4681cb0b5eea174807c6c6a2b0d49aa35ad650fb99b'}
    before=snap(ROOT);mode=stat.S_IMODE(ROOT.stat().st_mode);assert all(sha(ROOT/p)==v for p,v in anchors.items())
    r=subprocess.run(['python','-I','-B',str(ROOT/'verify_packet.py'),'--packet',str(ROOT/'packet'),'--final',str(ROOT/'FINAL.json'),'--report',str(ROOT/'REPORT.md'),'--final-sha256',anchors['FINAL.json'],'--manifest-sha256',anchors['packet/MANIFEST.json'],'--report-sha256',anchors['REPORT.md'],'--project',str(P)],cwd=P,text=True,capture_output=True,check=True);assert not r.stderr;result0=json.loads(r.stdout);assert result0=={'artifact_verification':'matched','members':63,'source_blob_bindings':8,'original_selected_comparisons':11,'mathematical_gate':False}
    manifest=read(ROOT/'packet/MANIFEST.json');assert len(manifest['members'])==63;names={x['path']for x in manifest['members']};actual={p.removeprefix('packet/')for p,x in before.items()if x['kind']=='file'and p.startswith('packet/')and p!='packet/MANIFEST.json'};assert actual==names
    paired=0;only=[]
    for x in manifest['members']:
        if(ROOT/x['path']).is_file():assert(ROOT/x['path']).read_bytes()==(ROOT/'packet'/x['path']).read_bytes();paired+=1
        else:only.append(x['path'])
    assert paired==63 and not only
    tree=read(P/'sources/preprints-tree.json');lookup={x['path']:x for x in tree['tree']};assert not tree['truncated']and len(lookup)==13223 and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    canonical=read(ROOT/'packet/private/source-authentication.json');assert len(canonical)==8
    for x in canonical:
        p=P/x['local'];data=p.read_bytes();e=lookup[x['path']];assert p.resolve().is_relative_to(ROOT)and len(data)==x['bytes']==e['size']and sha(p)==x['sha256']and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==x['blob']==e['sha']
    stable={};completed=read(ROOT/'packet/private/completed-exception-extents.json');assert len(completed)==7
    for x in completed:
        p=P/x['original'];assert sha(p)==x['sha256']and x['start']==0 and x['end']==p.stat().st_size and p.read_bytes()==(ROOT/'packet'/x['local']).read_bytes();stable[x['original']]=sha(p)
    sections=read(ROOT/'packet/private/history-extents.json');assert len(sections)==4;recorded=[]
    for x in sections:
        p=P/x['original'];assert sha(p)==x['original_sha256']
        with p.open('rb')as f:f.seek(x['start']);data=f.read(x['end']-x['start'])
        assert hashlib.sha256(data).hexdigest()==x['selected_sha256']and data==(ROOT/'packet'/x['local']).read_bytes();stable[x['original']]=sha(p);recorded.append({'path':x['original'],'start':x['start'],'end':x['end'],'selection_sha256':x['selected_sha256']})
    assert snap(ROOT)==before and stat.S_IMODE(ROOT.stat().st_mode)==mode
    (O/'observed-root.json').write_text(json.dumps({'root':before,'root_mode':mode},indent=2)+'\n');result={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'author_verifier_stdout':r.stdout.strip(),'parent_exact_packet_membership_checked':True,'payload_files':63,'canonical_objects':8,'completed_originals':7,'selected_original_sections':4,'paired_working_copies':63,'packet_only_members':only,'stable_named_originals':stable,'history_section_anchors':recorded,'wider_working_directory_not_wholly_selected_or_sealed':True,'entire_root_unchanged':True,'artifact_only':True,'parent_semantic_reading':'Complete four mathematical notes, REPORT, FINAL, packet reading-limits/selection and verifier. Actual source/primary/history proof extents attributed to author. All63 selected copies match working originals; wider acquisitions/navigation and copied controls separately observed unchanged, not claimed selected.'};(O/'replay.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k]for k in ['payload_files','canonical_objects','completed_originals','selected_original_sections','paired_working_copies','entire_root_unchanged','artifact_only']}))
if __name__=='__main__':main()
