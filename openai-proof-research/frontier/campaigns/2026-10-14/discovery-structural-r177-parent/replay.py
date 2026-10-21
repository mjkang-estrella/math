#!/usr/bin/env python3
"""Read-only explicit-anchor S177 prefreeze intake; no mathematical gate."""
import datetime,hashlib,importlib.util,json,stat,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-structural-discovery-r177'
sp=importlib.util.spec_from_file_location('snapshot',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_text())
def main():
    anchors={'private/packet/FINAL.json':'41d7f84340ac2afd8cdfe342da09ecbbd11881c971b60176398b26eddaa1cee9','private/packet/MANIFEST.json':'df56ffcfba87e85ecce529087e86c6dc812e10a7161babde9a5376db3f266f15','REPORT.md':'1b6ef75dec1fae1de09a8230fcbc82c6135eaf639ef27cb918ff78f5c5b0d33a'}
    before=snap(ROOT);mode=stat.S_IMODE(ROOT.stat().st_mode);assert all(sha(ROOT/p)==v for p,v in anchors.items())
    r=subprocess.run(['python','-I','-B',str(ROOT/'private/verify_packet.py'),'--root',str(ROOT),'--final',anchors['private/packet/FINAL.json'],'--manifest',anchors['private/packet/MANIFEST.json'],'--report',anchors['REPORT.md']],cwd=P,text=True,capture_output=True,check=True);assert not r.stderr;result=json.loads(r.stdout);assert result['artifact_files_matched']==72
    m=read(ROOT/'private/packet/MANIFEST.json');selected={x['path']for x in m['files']};actual={p for p,x in before.items()if x['kind']=='file'};outside={'ANCHORS.txt','REPORT.md','private/packet/FINAL.json','private/packet/MANIFEST.json'};excluded_controls={p for p in actual if p.startswith('private/controls/')};assert actual==selected|outside|excluded_controls and len(excluded_controls)==5
    tree=read(P/'sources/preprints-tree.json');lookup={x['path']:x for x in tree['tree']};assert not tree['truncated'] and len(lookup)==13223 and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    canonical=read(ROOT/'private/source-auth.json');assert len(canonical)==11
    for x in canonical:
        p=P/x['local'];d=p.read_bytes();e=lookup[x['path']];assert p.resolve().is_relative_to(ROOT) and len(d)==x['size']==e['size'] and sha(p)==x['sha256'] and hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()==x['git_blob']==e['sha']
    stable={};closing=read(ROOT/'private/original-byte-check.json');assert len(closing)==15
    for x in closing:
        p=P/x['path'];assert p.stat().st_size==x['bytes'] and sha(p)==x['sha256'] and stat.S_IMODE(p.stat().st_mode)==x['mode_at_final_check'];stable[x['path']]=sha(p)
    sections=read(ROOT/'private/history-extents.json');assert len(sections)==10
    for x in sections:
        p=P/x['path'];assert sha(p)==x['sha256']
        with p.open('rb')as f:f.seek(x['start_byte']);d=f.read(x['end_byte']-x['start_byte'])
        assert d==(P/x['local']).read_bytes();stable[x['path']]=sha(p)
    assert snap(ROOT)==before and stat.S_IMODE(ROOT.stat().st_mode)==mode
    (O/'observed-root.json').write_text(json.dumps({'root':before,'root_mode':mode},indent=2)+'\n')
    report={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'author_validator':result,'parent_exact_file_membership_checked':True,'excluded_copied_control_files':5,'payload_files':72,'canonical_objects':11,'closing_original_records':15,'selected_original_sections':10,'stable_named_originals':stable,'closing_input_modes':closing,'entire_root_unchanged':True,'artifact_only':True,'parent_semantic_reading':'Complete REPORT/notes01-03/reading-limits/verifier/FINAL envelope. Actual source/primary semantic extents remain attributed to author; no parent independent all-primary reading claim.'}
    (O/'replay.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'payload_files':72,'canonical_objects':11,'closing_original_records':15,'selected_original_sections':10,'entire_root_unchanged':True,'artifact_only':True}))
if __name__=='__main__':main()
