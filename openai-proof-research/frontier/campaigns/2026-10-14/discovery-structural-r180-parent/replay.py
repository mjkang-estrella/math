#!/usr/bin/env python3
"""Read-only S180 exact-selection intake; integrity is not a mathematical gate."""
import datetime,hashlib,importlib.util,json,stat,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-structural-discovery-r180'
sp=importlib.util.spec_from_file_location('snapshot',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_bytes())
def main():
    anchors={'FINAL.json':'1d3ce7b5a9819c85e5a5209ed85b8ceb3f59d82dae9bbd488bab1a254f1d965a','packet/MANIFEST.json':'7cbee20ff88997eece0cf85eca0d6b0c14e1eec5a9a37f3cbe8547e6464ee71b','REPORT.md':'9ed5808c35c3e89eaaeb2ec1501b5d2a66c93d87ace3badbf5ef694b0073f467'}
    before=snap(ROOT);mode=stat.S_IMODE(ROOT.stat().st_mode);assert all(sha(ROOT/p)==v for p,v in anchors.items())
    r=subprocess.run(['python','-I','-B',str(ROOT/'verify_packet.py'),'--packet',str(ROOT/'packet'),'--final',str(ROOT/'FINAL.json'),'--report',str(ROOT/'REPORT.md'),'--final-sha',anchors['FINAL.json'],'--manifest-sha',anchors['packet/MANIFEST.json'],'--report-sha',anchors['REPORT.md']],cwd=P,text=True,capture_output=True,check=True);assert not r.stderr
    manifest=read(ROOT/'packet/MANIFEST.json');assert len(manifest['files'])==85
    names={x['path']for x in manifest['files']};actual={p.removeprefix('packet/')for p,x in before.items()if x['kind']=='file'and p.startswith('packet/')and p!='packet/MANIFEST.json'};assert actual==names
    only=[];paired=0
    for x in manifest['files']:
        if (ROOT/x['path']).is_file():assert(ROOT/x['path']).read_bytes()==(ROOT/'packet'/x['path']).read_bytes();paired+=1
        else:only.append(x['path'])
    assert paired==84 and only==['private/selection.md']
    tree=read(P/'sources/preprints-tree.json');lookup={x['path']:x for x in tree['tree']};assert not tree['truncated']and len(lookup)==13223 and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    canonical=read(ROOT/'private/source-authentication.json')+read(ROOT/'private/companion-authentication.json');assert len(canonical)==31
    for x in canonical:
        p=P/x['local'];data=p.read_bytes();e=lookup[x['path']];assert p.resolve().is_relative_to(ROOT)and len(data)==x['bytes']==e['size']and sha(p)==x['sha256']and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==x['git_blob']==e['sha']
    stable={};completed=read(ROOT/'private/completed-r179-extents.json');assert len(completed)==7
    for x in completed:
        p=P/x['origin'];assert sha(p)==x['sha256']and p.read_bytes()==(ROOT/x['local']).read_bytes();assert x['semantic_byte_extents']==[[0,p.stat().st_size]];stable[x['origin']]=sha(p)
    sections=read(ROOT/'private/history-extents.json');assert len(sections)==3
    for x in sections:
        p=P/x['path'];assert p.stat().st_size==x['source_bytes']and sha(p)==x['source_sha256']
        with p.open('rb')as f:f.seek(x['start']);data=f.read(x['end']-x['start'])
        assert data==(P/x['selected']).read_bytes();stable[x['path']]=sha(p)
    assert snap(ROOT)==before and stat.S_IMODE(ROOT.stat().st_mode)==mode
    (O/'observed-root.json').write_text(json.dumps({'root':before,'root_mode':mode},indent=2)+'\n')
    result={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'author_verifier_stdout':r.stdout.strip(),'parent_exact_packet_membership_checked':True,'payload_files':85,'canonical_objects':31,'completed_originals':7,'selected_original_sections':3,'paired_working_copies':84,'packet_only_own_selection_record':only,'stable_named_originals':stable,'wider_working_directory_not_wholly_selected_or_sealed':True,'entire_root_unchanged':True,'artifact_only':True,'parent_semantic_reading':'Complete four mathematical notes, REPORT, FINAL, private reading-limits, own packet selection note and verifier. Actual source/companion/primary proof extents remain attributed to author. Eighty-four selected copies match working originals; own selection.md exists only in packet. Wider working acquisition/navigation/scratch is separately observed unchanged, not claimed selected.'}
    (O/'replay.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'payload_files':85,'canonical_objects':31,'completed_originals':7,'selected_original_sections':3,'paired_working_copies':84,'entire_root_unchanged':True,'artifact_only':True}))
if __name__=='__main__':main()
