#!/usr/bin/env python3
"""Read-only detached-anchor A170 intake; identity assigns no mathematical gate."""
import datetime,hashlib,importlib.util,json,stat,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-analytic-discovery-r170'
sp=importlib.util.spec_from_file_location('snapshot',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_text())
def main():
    anchors={'FINAL.md':'e9b5bccee9c97acbc7b9a24ba48e0b27ecdfe1edea23ef81b2be1c0ddea2e5d4','MANIFEST.json':'20e9d54d22595f9a4e970e11db68be922812ca99ee9d778ae83aaf3a0d009983','REPORT.md':'2021f61429f9b56bcf0ebcfb9ae6c0a903d378b0a584bdd252ffda809a808b18'}
    before=snap(ROOT);mode=stat.S_IMODE(ROOT.stat().st_mode);assert all(sha(ROOT/p)==v for p,v in anchors.items())
    r=subprocess.run(['python','-I','-B',str(ROOT/'VERIFY.py'),'--root',str(ROOT),'--final-sha256',anchors['FINAL.md'],'--manifest-sha256',anchors['MANIFEST.json'],'--report-sha256',anchors['REPORT.md']],cwd=P,text=True,capture_output=True,check=True);assert not r.stderr
    manifest=read(ROOT/'MANIFEST.json');assert len(manifest['files'])==67
    names={x['path']for x in manifest['files']};outside={'MANIFEST.json','REPORT.md','ANCHORS.json'};actual={p for p,x in before.items()if x['kind']=='file'};assert actual==names|outside,(actual-names-outside,names-actual)
    tree=read(P/'sources/preprints-tree.json');lookup={x['path']:x for x in tree['tree']};assert not tree['truncated'] and len(lookup)==13223 and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    canonical=read(ROOT/'private/AUTH.json');assert len(canonical)==22
    for x in canonical:
        p=P/x['local'];d=p.read_bytes();e=lookup[x['path']];assert p.resolve().is_relative_to(ROOT) and len(d)==x['bytes']==e['size'] and sha(p)==x['sha256'] and hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()==x['git_blob']==e['sha']
    stable={};direct=read(ROOT/'private/DIRECT-ANCHORS.json')
    for x in direct['exact_completed_originals']:
        p=P/x['path'];copy=ROOT/x['copy'];assert p.read_bytes()==copy.read_bytes() and p.stat().st_size==x['bytes'] and sha(p)==x['sha256'];stable[x['path']]=sha(p)
    for x in direct['direct_inputs']:
        if x['path']=='sources/preprints-tree.json':continue
        p=P/x['path']
        with p.open('rb')as f:f.seek(x['start']);d=f.read(x['end']-x['start'])
        assert hashlib.sha256(d).hexdigest()==x['sha256']
    x=read(ROOT/'private/ORIGINAL-EXTENT.json');p=P/x['original'];assert p.stat().st_size==x['original_bytes'] and sha(p)==x['original_sha256']
    with p.open('rb')as f:f.seek(x['start']);d=f.read(x['end']-x['start'])
    assert hashlib.sha256(d).hexdigest()==x['selected_sha256'] and d==(ROOT/'private/ORIGINAL-CP-SECTION.md').read_bytes();stable[x['original']]=sha(p)
    assert snap(ROOT)==before and stat.S_IMODE(ROOT.stat().st_mode)==mode
    (O/'observed-root.json').write_text(json.dumps({'root':before,'root_mode':mode},indent=2)+'\n')
    result={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'author_verifier_stdout':r.stdout.strip(),'parent_exact_file_membership_checked':True,'payload_files':67,'outside_envelopes':3,'canonical_objects':22,'completed_originals':6,'selected_original_sections':1,'stable_named_originals':stable,'direct_input_extents_match':True,'entire_root_unchanged':True,'artifact_only':True,'parent_semantic_reading':'Complete FINAL/REPORT/CALCULATIONS/CONTRACTIVE/OBSTRUCTION/COMPARISON/private READING-LIMITS/verifier. Source and actual-primary semantic extents remain attributed to author; parent did not independently reread all their proofs. Bounded schema excerpts were navigation only.'}
    (O/'replay.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'payload_files':67,'canonical_objects':22,'completed_originals':6,'selected_original_sections':1,'entire_root_unchanged':True,'artifact_only':True}))
if __name__=='__main__':main()
