#!/usr/bin/env python3
"""Read-only A171 exact-packet intake; byte integrity assigns no mathematical gate."""
import datetime,hashlib,importlib.util,json,stat,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-analytic-discovery-r171'
sp=importlib.util.spec_from_file_location('snapshot',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_bytes())
def main():
    anchors={'FINAL.md':'b045c8f72e6888ba0d9b3a83a69e4b01e093cb2767b8c23a4f5227b59dc92686','MANIFEST.json':'546e93189213764bd9bcc658af7fa9d1ae23d8cc8e0fd5b515fa921e18e90aab','REPORT.md':'722ea3077e536d6ebbb08a3e81957a86f92f99cdcc0cfe02ec587c1cfeab1842'}
    before=snap(ROOT);mode=stat.S_IMODE(ROOT.stat().st_mode);assert all(sha(ROOT/p)==v for p,v in anchors.items())
    r=subprocess.run(['python','-I','-B',str(ROOT/'VERIFY.py'),'--root',str(ROOT),'--final-sha',anchors['FINAL.md'],'--manifest-sha',anchors['MANIFEST.json'],'--report-sha',anchors['REPORT.md'],'--project-root',str(P)],cwd=P,text=True,capture_output=True,check=True);assert not r.stderr
    manifest=read(ROOT/'MANIFEST.json');assert len(manifest['files'])==63
    names={x['path']for x in manifest['files']};outside={'FINAL.md','MANIFEST.json','REPORT.md','ANCHORS.json'};actual={p for p,x in before.items()if x['kind']=='file'};assert actual==names|outside
    tree=read(P/'sources/preprints-tree.json');lookup={x['path']:x for x in tree['tree']};assert not tree['truncated'] and len(lookup)==13223 and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    canonical=read(ROOT/'private/source-auth.json');assert len(canonical)==12
    for x in canonical:
        p=P/x['local'];d=p.read_bytes();e=lookup[x['path']];assert p.resolve().is_relative_to(ROOT) and len(d)==x['bytes']==e['size'] and sha(p)==x['sha256'] and hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()==x['git_blob']==e['sha']
    stable={};completed=read(ROOT/'private/completed-exceptions.json');assert len(completed)==7
    for x in completed:
        p=P/x['path'];assert p.stat().st_size==x['bytes'] and sha(p)==x['sha256'];stable[x['path']]=sha(p)
    sections=read(ROOT/'private/original-extents.json')+read(ROOT/'private/original-equivariant-extents.json');assert len(sections)==8
    for x in sections:
        p=P/x['path'];assert sha(p)==x['sha256']
        with p.open('rb')as f:f.seek(x['start']);d=f.read(x['end']-x['start'])
        assert hashlib.sha256(d).hexdigest()==x['selection_sha256'] and d==(ROOT/x['local']).read_bytes();stable[x['path']]=sha(p)
    assert snap(ROOT)==before and stat.S_IMODE(ROOT.stat().st_mode)==mode
    (O/'observed-root.json').write_text(json.dumps({'root':before,'root_mode':mode},indent=2)+'\n')
    result={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'author_verifier_stdout':r.stdout.strip(),'parent_exact_file_membership_checked':True,'payload_files':63,'outside_envelopes':4,'canonical_objects':12,'completed_originals':7,'selected_original_sections':8,'stable_named_originals':stable,'direct_original_extents_checked_by_author_verifier':True,'entire_root_unchanged':True,'artifact_only':True,'parent_semantic_reading':'Complete FINAL/REPORT/CALCULATIONS/COHERENCE/RELATIVE/COMPARISON/private READING-LIMITS/verifier. Source and actual-primary semantic extents remain attributed to author; parent did not independently reread all their proofs. Bounded schema excerpts are navigation only.'}
    (O/'replay.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'payload_files':63,'canonical_objects':12,'completed_originals':7,'selected_original_sections':8,'entire_root_unchanged':True,'artifact_only':True}))
if __name__=='__main__':main()
