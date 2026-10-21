#!/usr/bin/env python3
"""Read-only detached-anchor Arithmetic141 intake; no mathematical grade."""
import datetime,hashlib,importlib.util,json,stat,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-arithmetic-discovery-r141'
sp=importlib.util.spec_from_file_location('snapshot',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_bytes())
def main():
    anchors={'FINAL.md':'f33add3ab19b1d7d69a0525cb78cf23f85752c20b3f99004eb59a22d59d0e620','MANIFEST.json':'81674c32020988d9a41337663f63779e15883c38d1f0aeac894dbffc68021664','REPORT.md':'0369229e8cb1689636eb7e3a790f4cfe0d817c4a675a16f997c5380381ac4a8b'}
    before=snap(ROOT);mode=stat.S_IMODE(ROOT.stat().st_mode);assert all(sha(ROOT/p)==v for p,v in anchors.items())
    r=subprocess.run(['python','-I','-B',str(ROOT/'verify_packet.py'),'--root',str(ROOT),'--final-sha256',anchors['FINAL.md'],'--manifest-sha256',anchors['MANIFEST.json'],'--report-sha256',anchors['REPORT.md']],cwd=P,text=True,capture_output=True,check=True);assert not r.stderr
    manifest=read(ROOT/'MANIFEST.json');assert len(manifest['files'])==89
    names={x['path']for x in manifest['files']};outside={'MANIFEST.json','REPORT.md','ANCHORS.json'};actual={p for p,x in before.items()if x['kind']=='file'};assert actual==names|outside,(actual-names-outside,names-actual)
    tree=read(P/'sources/preprints-tree.json');lookup={x['path']:x for x in tree['tree']};assert not tree['truncated'] and len(lookup)==13223 and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    canonical=read(ROOT/'private/source-identities.json');assert len(canonical)==12
    for x in canonical:
        p=P/x['local'];d=p.read_bytes();e=lookup[x['path']];assert p.resolve().is_relative_to(ROOT) and len(d)==x['size']==e['size'] and sha(p)==x['sha256'] and hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()==x['git_blob']==e['sha']
    stable={};direct=read(ROOT/'private/direct-reads.json');assert len(direct)==9
    for x in direct:
        p=P/x['path']
        with p.open('rb')as f:f.seek(x['start']);d=f.read(x['end']-x['start'])
        assert hashlib.sha256(d).hexdigest()==x['sha256'] and d==(ROOT/'private'/x['local']).read_bytes()
        if x['path']!='frontier/NEW-TEN-2026-10-14.md':stable[x['path']]=sha(p)
    sections=read(ROOT/'private/original-sections.json');assert len(sections)==5
    for x in sections:
        p=P/x['path']
        with p.open('rb')as f:f.seek(x['start']);d=f.read(x['end']-x['start'])
        assert hashlib.sha256(d).hexdigest()==x['sha256'] and d==(ROOT/'private'/x['local']).read_bytes()
    assert snap(ROOT)==before and stat.S_IMODE(ROOT.stat().st_mode)==mode
    (O/'observed-root.json').write_text(json.dumps({'root':before,'root_mode':mode},indent=2)+'\n')
    result={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'author_verifier_stdout':r.stdout.strip(),'parent_exact_file_membership_checked':True,'payload_files':89,'outside_envelopes':3,'canonical_objects':12,'completed_originals':6,'selected_original_sections':5,'stable_named_originals':stable,'direct_input_extents_match':True,'original_history_sections_match':True,'history_original_whole_hashes_not_supplied':True,'entire_root_unchanged':True,'artifact_only':True,'parent_semantic_reading':'Complete FINAL/REPORT/DERIVATIONS/UNRESOLVED/private READING/selection-limits/verifier. Source and actual-primary semantic extents remain attributed to author; parent did not independently reread all their proofs. Bounded schema excerpts are navigation only. Original-history checks bind supplied sections, not fabricated whole-original hash records.'}
    (O/'replay.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'payload_files':89,'canonical_objects':12,'completed_originals':6,'selected_original_sections':5,'entire_root_unchanged':True,'artifact_only':True}))
if __name__=='__main__':main()
