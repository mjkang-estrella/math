#!/usr/bin/env python3
"""Read-only Arithmetic142 detached-anchor intake; no mathematical gate."""
import datetime,hashlib,importlib.util,json,stat,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-arithmetic-discovery-r142'
sp=importlib.util.spec_from_file_location('snapshot',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_bytes())
def main():
    anchors={'FINAL.md':'b208b8072d31e82559649e6785df0bbd3ca05cb3f537daea1a0c1d437eada60f','MANIFEST.json':'4bf3192673fb59a9c625f911446273d3c1743caa46c5a9cd8c86e9db0621361b','REPORT.md':'ffbd105381b3da369b90be981e40af9a96ef0d488ac942d34d8d225f3e78d068'}
    before=snap(ROOT);mode=stat.S_IMODE(ROOT.stat().st_mode);assert all(sha(ROOT/p)==v for p,v in anchors.items())
    r=subprocess.run(['python','-I','-B',str(ROOT/'verify.py'),'--final',anchors['FINAL.md'],'--manifest',anchors['MANIFEST.json'],'--report',anchors['REPORT.md']],cwd=P,text=True,capture_output=True,check=True);assert not r.stderr
    manifest=read(ROOT/'MANIFEST.json');assert len(manifest['files'])==79
    names={x['path']for x in manifest['files']};outside={'MANIFEST.json','REPORT.md'};actual={p for p,x in before.items()if x['kind']=='file'};assert actual==names|outside
    tree=read(P/'sources/preprints-tree.json');lookup={x['path']:x for x in tree['tree']};assert not tree['truncated'] and len(lookup)==13223 and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    canonical=read(ROOT/'private/source-identities.json');assert len(canonical)==24
    for x in canonical:
        p=P/x['local'];d=p.read_bytes();e=lookup[x['path']];assert p.resolve().is_relative_to(ROOT) and len(d)==x['size']==e['size'] and sha(p)==x['sha256'] and hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()==x['sha']==e['sha']
    stable={};completed=['discovery-arithmetic-r141-parent/assessment.md','fresh-arithmetic-discovery-r141/FINAL.md','fresh-arithmetic-discovery-r141/DERIVATIONS.md','fresh-arithmetic-discovery-r141/UNRESOLVED.md','fresh-arithmetic-discovery-r141/private/READING.md','fresh-arithmetic-discovery-r141/private/selection-limits.md']
    for name in completed:
        p=B/name;copy=ROOT/'private'/('r141-'+name.replace('/','__'));assert p.read_bytes()==copy.read_bytes();stable[p.relative_to(P).as_posix()]=sha(p)
    section_anchors=[]
    for name in ['original-sections.json','descent-original-sections.json']:
        for i,x in enumerate(read(ROOT/'private'/name)):
            start,end=x['extent']if'extent'in x else(x['start'],x['end']);p=P/x['path'];copy=ROOT/'private'/x.get('copy',f'descent-original-{i}.txt')
            with p.open('rb')as f:f.seek(start);data=f.read(end-start)
            assert hashlib.sha256(data).hexdigest()==x['sha256'] and data==copy.read_bytes();section_anchors.append({'path':x['path'],'start':start,'end':end,'selection_sha256':x['sha256']})
    assert len(section_anchors)==6 and snap(ROOT)==before and stat.S_IMODE(ROOT.stat().st_mode)==mode
    (O/'observed-root.json').write_text(json.dumps({'root':before,'root_mode':mode},indent=2)+'\n')
    result={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'author_verifier_stdout':r.stdout.strip(),'parent_exact_file_membership_checked':True,'payload_files':79,'outside_envelopes':2,'canonical_objects':24,'completed_originals':6,'selected_original_sections':6,'stable_named_originals':stable,'history_section_anchors':section_anchors,'history_checks_bind_section_hashes_not_whole_originals':True,'entire_root_unchanged':True,'artifact_only':True,'parent_semantic_reading':'Complete DERIVATIONS/UNRESOLVED/FINAL/REPORT/private READING/selection-limits/verifier. Source and actual-primary semantic extents remain attributed to author; parent did not independently reread all their proofs. Schema excerpts and byte matching are navigation/integrity only.'}
    (O/'replay.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'payload_files':79,'canonical_objects':24,'completed_originals':6,'selected_original_sections':6,'entire_root_unchanged':True,'artifact_only':True}))
if __name__=='__main__':main()
