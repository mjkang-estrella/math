#!/usr/bin/env python3
"""Read-only Structural182 frozen-author intake; artifact verification assigns no gate."""
import datetime,hashlib,importlib.util,json,stat,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-structural-discovery-r182'
sp=importlib.util.spec_from_file_location('snapshot',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_bytes())
def main():
    anchors={'FINAL.json':'3a5256695f9f6e33863353a8bad22ed595a8632e4fe6694445292d1cffc4586d','packet/MANIFEST.json':'05a51a35df6077b5e7cfe66391dbe33190c0be15a718e3fcc937e5ad170fb412','REPORT.md':'5d31720da54b4667d52c0e128289eb1c35b9878024069077e0cd0cf77a7eb04e'}
    before=snap(ROOT);mode=stat.S_IMODE(ROOT.stat().st_mode);assert all(sha(ROOT/p)==v for p,v in anchors.items())
    r=subprocess.run(['python','-I','-B',str(ROOT/'packet/verify_packet.py'),'--root',str(ROOT),'--final-sha256',anchors['FINAL.json'],'--manifest-sha256',anchors['packet/MANIFEST.json'],'--report-sha256',anchors['REPORT.md'],'--project',str(P)],cwd=P,text=True,capture_output=True,check=True);assert not r.stderr and json.loads(r.stdout)=={'artifact_only':'verified','members':40,'explicit_originals_checked':10}
    m=read(ROOT/'packet/MANIFEST.json');assert len(m['members'])==40;names={x['path']for x in m['members']};actual={p.removeprefix('packet/')for p,x in before.items()if x['kind']=='file'and p.startswith('packet/')and p!='packet/MANIFEST.json'};assert actual==names
    paired=[]
    for x in m['members']:
        if(ROOT/x['path']).is_file():assert(ROOT/x['path']).read_bytes()==(ROOT/'packet'/x['path']).read_bytes();paired.append(x['path'])
    assert set(paired)=={'FROZEN-THEOREM.md','notes/01-operative-inputs.md','notes/02-prefreeze-feasibility.md','notes/03-author-proof.md','notes/04-comparison-and-boundary-tests.md'}
    tree=read(P/'sources/preprints-tree.json');lookup={x['path']:x for x in tree['tree']};assert not tree['truncated']and len(lookup)==13223 and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';canonical=read(ROOT/'packet/private/source-authentication.json');assert len(canonical)==2
    for x in canonical:
        p=ROOT/'packet/private'/Path(x['path']).name;data=p.read_bytes();e=lookup[x['path']];assert len(data)==x['bytes']==e['size']and sha(p)==x['sha256']and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==x['git_blob']==e['sha']
    stable={};direct=read(ROOT/'packet/private/completed-exceptions.json');assert len(direct)==7
    for x in direct:
        p=P/x['path'];assert p.stat().st_size==x['bytes']and sha(p)==x['sha256'];stable[x['path']]=sha(p)
    sections=[];history=read(ROOT/'packet/private/history-extents.json');assert len(history)==2
    for x in history:
        p=P/x['path'];assert sha(p)==x['original_sha256'];data=b''
        for a,b in x['extents']:
            with p.open('rb')as f:f.seek(a);part=f.read(b-a)
            data+=part;sections.append({'path':x['path'],'start':a,'end':b,'selection_sha256':hashlib.sha256(part).hexdigest(),'basis':'parent intake selected-range hash; author records whole-original digest and concatenated copy'})
        assert data==(ROOT/'packet/private'/x['copy']).read_bytes();stable[x['path']]=sha(p)
    frozen='62b6ad633a662a491be617e82f8eb441be8f02069a7dc5289c10996dc8d9bee8';proof='9f2989669c20bea00260a77dd11a4a4fcb1e7cb0d84f75f8777871ae85d1d38e';assert sha(ROOT/'FROZEN-THEOREM.md')==frozen==read(ROOT/'packet/private/freeze-record.json')['statement_sha256']and sha(ROOT/'notes/03-author-proof.md')==proof
    assert len(sections)==3 and len(stable)==9 and snap(ROOT)==before and stat.S_IMODE(ROOT.stat().st_mode)==mode
    (O/'observed-root.json').write_text(json.dumps({'root':before,'root_mode':mode},indent=2)+'\n');result={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'author_verifier_stdout':r.stdout.strip(),'parent_exact_packet_membership_checked':True,'payload_files':40,'canonical_objects':2,'completed_originals':7,'selected_history_originals':2,'selected_original_sections':3,'explicit_original_anchors_in_author_verifier':10,'paired_working_author_files':paired,'frozen_scope_sha256':frozen,'author_proof_sha256':proof,'stable_named_originals':stable,'history_section_anchors':sections,'wider_working_directory_not_wholly_selected_or_sealed':True,'entire_root_unchanged':True,'artifact_only':True,'parent_semantic_reading':'Complete frozen theorem, four notes, FINAL, REPORT, reading-limits and verifier. Source/primary/history semantic extents remain attributed to author. Initial assumed root private directory did not exist; packet/private metadata was used instead, with no author mutation.'};(O/'replay.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k]for k in ['payload_files','canonical_objects','completed_originals','selected_original_sections','entire_root_unchanged','artifact_only']}))
if __name__=='__main__':main()
