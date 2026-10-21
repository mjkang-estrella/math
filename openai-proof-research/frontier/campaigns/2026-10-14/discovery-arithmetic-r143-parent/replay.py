#!/usr/bin/env python3
"""Read-only Arithmetic143 detached-anchor intake; no mathematical gate."""
import datetime,hashlib,importlib.util,json,stat,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-arithmetic-discovery-r143'
sp=importlib.util.spec_from_file_location('snapshot',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_bytes())
def main():
    anchors={'FINAL.md':'c3024d146dd54891d69a5f37e9906de5345e43f8e8e830890dbbb4ea8a4026b5','MANIFEST.json':'1eb480675f7316a3562cea64a54f41adaad18fe3a2aed41f08989c5e062b6b83','REPORT.md':'277dcd9b4be0dc031b08dba2db7e9bffa02b0a4d072b5b4b58b915da6b248285'}
    before=snap(ROOT);mode=stat.S_IMODE(ROOT.stat().st_mode);assert all(sha(ROOT/p)==v for p,v in anchors.items())
    r=subprocess.run(['python','-I','-B',str(ROOT/'verify.py'),'--root',str(ROOT),'--final-sha256',anchors['FINAL.md'],'--manifest-sha256',anchors['MANIFEST.json'],'--report-sha256',anchors['REPORT.md']],cwd=P,text=True,capture_output=True,check=True);assert not r.stderr and json.loads(r.stdout)['artifact_ok']
    manifest=read(ROOT/'MANIFEST.json');assert len(manifest['files'])==86
    names={x['path']for x in manifest['files']};outside={'MANIFEST.json','REPORT.md','ANCHORS.json'};actual={p for p,x in before.items()if x['kind']=='file'};assert actual==names|outside
    tree=read(P/'sources/preprints-tree.json');lookup={x['path']:x for x in tree['tree']};assert not tree['truncated']and len(lookup)==13223 and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    canonical=read(ROOT/'private/source-bindings.json')+read(ROOT/'private/companion-bindings.json');assert len(canonical)==23
    for x in canonical:
        p=P/x['local'];data=p.read_bytes();e=lookup[x['path']];assert p.resolve().is_relative_to(ROOT)and len(data)==x['size']==e['size']and sha(p)==x['sha256']and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==x['sha']==e['sha']
    stable={};direct=read(ROOT/'private/direct-extents.json');assert len(direct)==10;completed=0
    for x in direct:
        p=P/x['path']
        with p.open('rb')as f:f.seek(x['start']);data=f.read(x['end']-x['start'])
        assert hashlib.sha256(data).hexdigest()==x['sha256']and data==(ROOT/x['local']).read_bytes()
        if '/fresh-arithmetic-discovery-r142/'in x['path']or'/discovery-arithmetic-r142-parent/'in x['path']:
            assert x['start']==0 and p.stat().st_size==x['end'];stable[x['path']]=sha(p);completed+=1
    assert completed==6;section_anchors=[]
    for x in read(ROOT/'private/original-extents.json'):
        p=P/x['original'];copy=ROOT/x['local']
        with p.open('rb')as f:f.seek(x['start']);data=f.read(x['end']-x['start'])
        assert hashlib.sha256(data).hexdigest()==x['sha256']and data==copy.read_bytes();section_anchors.append({'path':x['original'],'start':x['start'],'end':x['end'],'selection_sha256':x['sha256'],'basis':'author selected-range hash'})
    for x in read(ROOT/'private/extra-extents.json'):
        p=P/x['path'];copy=ROOT/'private'/x['copy']
        with p.open('rb')as f:f.seek(x['start']);data=f.read(x['end']-x['start'])
        assert data==copy.read_bytes();section_anchors.append({'path':x['path'],'start':x['start'],'end':x['end'],'selection_sha256':sha(copy),'basis':'parent intake hash of retained section; no fabricated earlier original digest'})
    assert len(section_anchors)==12 and snap(ROOT)==before and stat.S_IMODE(ROOT.stat().st_mode)==mode
    (O/'observed-root.json').write_text(json.dumps({'root':before,'root_mode':mode},indent=2)+'\n')
    result={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'author_verifier_stdout':r.stdout.strip(),'parent_exact_file_membership_checked':True,'payload_files':86,'outside_envelopes':3,'canonical_objects':23,'completed_originals':6,'direct_anchors':10,'selected_original_sections':12,'stable_named_originals':stable,'history_section_anchors':section_anchors,'history_checks_bind_selected_ranges_only':True,'extra_four_section_hashes_are_parent_intake_observations':True,'entire_root_unchanged':True,'artifact_only':True,'parent_semantic_reading':'Complete DERIVATIONS/UNRESOLVED/FINAL/REPORT/private READING/selection-limits/verifier. Actual source/companion/primary semantic extents remain attributed to author. Bounded metadata title navigation initially assumed contiguous43–55 numbers; corrected after missing045 without decoding any extra family body. Only Source044 body selected.'}
    (O/'replay.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'payload_files':86,'canonical_objects':23,'completed_originals':6,'direct_anchors':10,'selected_original_sections':12,'entire_root_unchanged':True,'artifact_only':True}))
if __name__=='__main__':main()
