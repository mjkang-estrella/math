#!/usr/bin/env python3
"""Read-only A172 detached-anchor intake; byte integrity assigns no mathematical gate."""
import datetime,hashlib,importlib.util,json,stat,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-analytic-discovery-r172'
sp=importlib.util.spec_from_file_location('snapshot',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_bytes())
def main():
    anchors={'FINAL.md':'baced4e379ee3b6d367f026cf3a612fc45bc2385840de5ca09d39813622f7700','MANIFEST.json':'11784251f8e230d9a0a424c23d31fe568edc043ff5a58bed5a978eea708c723a','REPORT.md':'e39a8d6347151ff15cdffc3c5aaeb961943465a3e6d48472dbbad7222bcba076'}
    before=snap(ROOT);mode=stat.S_IMODE(ROOT.stat().st_mode);assert all(sha(ROOT/p)==v for p,v in anchors.items())
    r=subprocess.run(['python','-I','-B',str(ROOT/'verify_packet.py'),'--final-sha256',anchors['FINAL.md'],'--manifest-sha256',anchors['MANIFEST.json'],'--report-sha256',anchors['REPORT.md'],'--project-root',str(P)],cwd=P,text=True,capture_output=True,check=True);assert not r.stderr
    manifest=read(ROOT/'MANIFEST.json');assert len(manifest['files'])==63
    names={x['path']for x in manifest['files']};outside={'MANIFEST.json','REPORT.md','ANCHORS.json'};actual={p for p,x in before.items()if x['kind']=='file'};assert actual==names|outside
    tree=read(P/'sources/preprints-tree.json');lookup={x['path']:x for x in tree['tree']};assert not tree['truncated'] and len(lookup)==13223 and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    canonical=read(ROOT/'private/source-auth.json');assert len(canonical)==16
    for x in canonical:
        p=P/x['local'];d=p.read_bytes();e=lookup[x['path']];assert p.resolve().is_relative_to(ROOT) and len(d)==x['bytes']==e['size'] and sha(p)==x['sha256'] and hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()==x['git_blob']==e['sha']
    stable={};direct=read(ROOT/'private/direct-anchors.json');assert len(direct)==12;completed=0
    for x in direct:
        p=P/x['path']
        with p.open('rb')as f:f.seek(x['start']);data=f.read(x['end']-x['start'])
        assert hashlib.sha256(data).hexdigest()==x['sha256']
        if '/fresh-analytic-discovery-r171/'in x['path']or'/discovery-analytic-r171-parent/'in x['path']:
            assert x['start']==0 and p.stat().st_size==x['end'];stable[x['path']]=sha(p);completed+=1
    assert completed==7
    sections=read(ROOT/'private/original-extents.json');assert len(sections)==4
    for x in sections:
        p=P/x['path'];assert p.stat().st_size==x['bytes'] and sha(p)==x['sha256']
        with p.open('rb')as f:f.seek(x['start']);data=f.read(x['end']-x['start'])
        assert hashlib.sha256(data).hexdigest()==x['selected_sha256'] and data==(P/x['copy']).read_bytes();stable[x['path']]=sha(p)
    assert snap(ROOT)==before and stat.S_IMODE(ROOT.stat().st_mode)==mode
    (O/'observed-root.json').write_text(json.dumps({'root':before,'root_mode':mode},indent=2)+'\n')
    result={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'author_verifier_stdout':r.stdout.strip(),'parent_exact_file_membership_checked':True,'payload_files':63,'outside_envelopes':3,'canonical_objects':16,'completed_originals':7,'direct_anchors':12,'selected_original_sections':4,'stable_named_originals':stable,'direct_hashes_registered_later_not_fabricated_acquisition_hashes':True,'entire_root_unchanged':True,'artifact_only':True,'parent_semantic_reading':'Complete FINAL/REPORT/CALCULATIONS/DESCENT/QUANTITATIVE/COMPARISON/private READING-LIMITS/verifier. Source and actual-primary semantic extents remain attributed to author; parent did not independently reread all their proofs. Bounded schema excerpts and identity checks are navigation/artifact work only.'}
    (O/'replay.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'payload_files':63,'canonical_objects':16,'completed_originals':7,'direct_anchors':12,'selected_original_sections':4,'entire_root_unchanged':True,'artifact_only':True}))
if __name__=='__main__':main()
