#!/usr/bin/env python3
"""Read-only S178 exact-packet intake; integrity is not a mathematical gate."""
import datetime,hashlib,importlib.util,json,stat,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-structural-discovery-r178'
sp=importlib.util.spec_from_file_location('snapshot',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_bytes())
def main():
    anchors={'FINAL.json':'0c6d727edf014f7a0e8e310e85a8fc5cce2e97647e3d57828a6ddfea2c9cadd2','private/packet/MANIFEST.json':'e824225b3e035484ffa6cd4e67ec15620fa685962917d32ed845de73b57eb317','REPORT.md':'06b3cc466b14d86fcca2a5f19ff7900f702e852d5287182c3632380fa022386f'}
    before=snap(ROOT);mode=stat.S_IMODE(ROOT.stat().st_mode);assert all(sha(ROOT/p)==v for p,v in anchors.items())
    r=subprocess.run(['python','-I','-B',str(ROOT/'private/verify_packet.py'),'--root',str(ROOT),'--final-sha256',anchors['FINAL.json'],'--manifest-sha256',anchors['private/packet/MANIFEST.json'],'--report-sha256',anchors['REPORT.md']],cwd=P,text=True,capture_output=True,check=True);assert not r.stderr
    manifest=read(ROOT/'private/packet/MANIFEST.json');assert len(manifest['files'])==78
    names={x['path']for x in manifest['files']};outside={'FINAL.json','private/packet/MANIFEST.json','REPORT.md','ANCHORS.json'};actual={p for p,x in before.items()if x['kind']=='file'};assert actual==names|outside
    tree=read(P/'sources/preprints-tree.json');lookup={x['path']:x for x in tree['tree']};assert not tree['truncated'] and len(lookup)==13223 and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    canonical=manifest['canonical_bindings'];assert len(canonical)==14;auth={x['path']:x for x in read(ROOT/'private/source-auth.json')}
    for x in canonical:
        p=ROOT/x['local'];d=p.read_bytes();e=lookup[x['upstream_path']];assert p.resolve().is_relative_to(ROOT) and len(d)==x['bytes']==e['size'] and sha(p)==auth[x['upstream_path']]['sha256'] and hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()==x['git_blob']==e['sha']
    stable={};direct=read(ROOT/'private/original-input-checks.json');assert len(direct)==7
    for i,x in enumerate(direct[:6]):
        p=P/x['path'];assert p.stat().st_size==x['bytes'] and sha(p)==x['sha256'] and p.read_bytes()==(ROOT/f'private/completed177-{i}.txt').read_bytes();stable[x['path']]=sha(p)
    sections=read(ROOT/'private/history-extents.json');assert len(sections)==13
    for x in sections:
        p=P/x['path'];assert sha(p)==x['full_sha256']
        with p.open('rb')as f:f.seek(x['byte_start']);d=f.read(x['byte_end']-x['byte_start'])
        assert d==(ROOT/x['copy']).read_bytes();stable[x['path']]=sha(p)
    assert snap(ROOT)==before and stat.S_IMODE(ROOT.stat().st_mode)==mode
    (O/'observed-root.json').write_text(json.dumps({'root':before,'root_mode':mode},indent=2)+'\n')
    result={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'author_verifier_stdout':r.stdout.strip(),'parent_exact_file_membership_checked':True,'payload_files':78,'outside_envelopes':4,'canonical_objects':14,'completed_originals':6,'selected_original_sections':13,'stable_named_originals':stable,'entire_root_unchanged':True,'artifact_only':True,'parent_semantic_reading':'Complete REPORT/FINAL.json/three mathematical notes/private reading-limits/verifier. An initial assumed FINAL.md filename was absent; corrected to actual FINAL.json before replay. Aggregate display truncated in note03; note03 and reading-limits were separately recovered in full. Source and actual-primary semantic extents remain attributed to author; parent did not reread all their proofs.'}
    (O/'replay.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'payload_files':78,'canonical_objects':14,'completed_originals':6,'selected_original_sections':13,'entire_root_unchanged':True,'artifact_only':True}))
if __name__=='__main__':main()
