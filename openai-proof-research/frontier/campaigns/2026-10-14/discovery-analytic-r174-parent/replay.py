#!/usr/bin/env python3
"""Read-only Analytic174 detached-anchor intake; no mathematical gate."""
import datetime,hashlib,importlib.util,json,stat,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-analytic-discovery-r174'
sp=importlib.util.spec_from_file_location('snapshot',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_bytes())
def main():
    anchors={'FINAL.md':'8674133830571943b386622ab2ed34832f706adc89a234df41f68b09f4f18372','MANIFEST.json':'9e3b24b5b1ffc1dd07984018cbf3dc185270eb43b197dd911c1b9e7c514a75ff','REPORT.md':'7e3ab907d15244d9bebf96da9b13e59ef41cc347850da484b3b027b2967133cb'}
    before=snap(ROOT);mode=stat.S_IMODE(ROOT.stat().st_mode);assert all(sha(ROOT/p)==v for p,v in anchors.items())
    r=subprocess.run(['python','-I','-B',str(ROOT/'verify_packet.py'),'--root',str(ROOT),'--final-sha256',anchors['FINAL.md'],'--manifest-sha256',anchors['MANIFEST.json'],'--report-sha256',anchors['REPORT.md']],cwd=P,text=True,capture_output=True,check=True);assert not r.stderr and json.loads(r.stdout)=={'artifact_integrity':'matched','payload_files':82,'mathematical_gate':False}
    m=read(ROOT/'MANIFEST.json');assert len(m['files'])==82;names={x['path']for x in m['files']};assert {p for p,x in before.items()if x['kind']=='file'}==names|{'FINAL.md','MANIFEST.json','REPORT.md','ANCHORS.json'}
    tree=read(P/'sources/preprints-tree.json');lookup={x['path']:x for x in tree['tree']};assert not tree['truncated']and len(lookup)==13223 and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    canonical=read(ROOT/'private/source-authentication.json');assert len(canonical)==10
    for x in canonical:
        p=P/x['local'];data=p.read_bytes();e=lookup[x['path']];assert p.resolve().is_relative_to(ROOT)and len(data)==x['size']==e['size']and sha(p)==x['sha256']and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==x['sha']==e['sha']
    stable={};direct=read(ROOT/'private/completed-exceptions.json');assert len(direct)==8
    for x in direct:
        p=P/x['path'];assert x['read']==[0,x['bytes']]and p.stat().st_size==x['bytes']and sha(p)==x['sha256'];stable[x['path']]=sha(p)
    sections=[];rows=[json.loads(l)for l in(ROOT/'private/semantic-extents.jsonl').read_text().splitlines()]
    for x in rows:
        if x['kind']!='original':continue
        p=P/x['path'];assert sha(p)==x['sha256'];copy=P/x['selected'];assert copy.resolve().is_relative_to(ROOT)
        with p.open('rb')as f:f.seek(x['start']);data=f.read(x['end']-x['start'])
        assert hashlib.sha256(data).hexdigest()==x['selected_sha256']and data==copy.read_bytes();stable[x['path']]=sha(p);sections.append({'path':x['path'],'start':x['start'],'end':x['end'],'selection_sha256':x['selected_sha256']})
    for x in read(ROOT/'private/original-unchanged.json'):assert x['unchanged']and sha(P/x['path'])==stable[x['path']]
    assert len(sections)==9 and len(stable)==11 and snap(ROOT)==before and stat.S_IMODE(ROOT.stat().st_mode)==mode
    (O/'observed-root.json').write_text(json.dumps({'root':before,'root_mode':mode},indent=2)+'\n');result={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'author_verifier_stdout':r.stdout.strip(),'parent_exact_file_membership_checked':True,'payload_files':82,'outside_envelopes':4,'canonical_objects':10,'completed_originals':8,'selected_original_sections':9,'stable_named_originals':stable,'history_section_anchors':sections,'retrospective_hash_registration_disclosed':True,'entire_root_unchanged':True,'artifact_only':True,'parent_semantic_reading':'Complete CARRIER/CHARACTERS/DETECTION/RELATIVE/INTERFACES/COMPARISON/FINAL/REPORT/private READING-LIMITS/verifier. Actual source/primary/history semantic extents remain attributed to author. Only bounded Source306 catalogue body read for next discovery.'};(O/'replay.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k]for k in ['payload_files','canonical_objects','completed_originals','selected_original_sections','entire_root_unchanged','artifact_only']}))
if __name__=='__main__':main()
