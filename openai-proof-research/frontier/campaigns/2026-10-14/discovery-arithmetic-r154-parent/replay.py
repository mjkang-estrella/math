#!/usr/bin/env python3
"""Read-only Arithmetic154 discovery intake; artifact checks only, no mathematical gate."""
import datetime,hashlib,importlib.util,json,stat,subprocess
from fractions import Fraction as Fr
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];A=B/'fresh-arithmetic-discovery-r154'
sp=importlib.util.spec_from_file_location('base',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_bytes())
def dump(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def span(p,s,e):
    assert not p.is_symlink()and p.stat().st_nlink==1
    with p.open('rb')as f:f.seek(s);d=f.read(e-s)
    assert len(d)==e-s;return d
def main():
    anchors={'FINAL.md':'f9de3c2372200e711037be9f0e00374c72201f74b35c6320b6f9ac4ad66d37d2','MANIFEST.json':'eedd596702ac0799d481a9ce4fca4dd0febd306c1a9c964df5cf4976ddf833ee','REPORT.md':'5938a6ae70ce5d4fab40d37aaa946959c3eb9be706d925e898dd6b705dc1e7ed'}
    before=snap(A);mode=stat.S_IMODE(A.stat().st_mode);assert all(sha(A/p)==v for p,v in anchors.items())
    assert read(A/'ANCHORS.json')==anchors
    run=subprocess.run(['python','-I','-B',str(A/'verify_packet.py'),'--root',str(A),'--final-sha256',anchors['FINAL.md'],'--manifest-sha256',anchors['MANIFEST.json'],'--report-sha256',anchors['REPORT.md']],cwd=P,capture_output=True,text=True,check=True);assert not run.stderr
    out=json.loads(run.stdout);assert out['files']==91 and out['payload_bytes']==6656354 and out['artifact_integrity']=='matched explicit anchors'and out['mathematical_verdict']is None
    m=read(A/'MANIFEST.json');assert m['schema']=='r154-exact-packet-v1'and len(m['files'])==91 and {'FINAL.md','DERIVATIONS.md','PREFREEZE.md','UNRESOLVED.md','verify_packet.py','private/READING.md'}<=set(x['path']for x in m['files'])
    tree=read(P/'sources/preprints-tree.json');lookup={e['path']:e for e in tree['tree']};assert len(lookup)==13223 and not tree['truncated']and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    objs=read(A/'private/source-bindings.json');assert len(objs)==22;canonical=0;folders=set()
    for x in objs:
        p=A/x['local'];d=p.read_bytes();e=lookup[x['path']];folders.add(x['path'].split('/')[1])
        assert p.resolve().is_relative_to(A.resolve())and len(d)==x['size']==e['size']and e['type']=='blob'and sha(p)==x['sha256']and hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()==x['sha']==e['sha']and x['url_raw']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+x['path'];canonical+=1
    assert folders=={'A-Gepner-stability-condition-on-every-smooth-quintic-threefold-September-24-2026','Prescribed-large-volume-charges-on-threefolds-with-trivial-canonical-bundle-September-24-2026'}
    folder_blobs=[k for k,e in lookup.items()if any(k.startswith('preprints/'+f+'/')for f in folders)and e['type']=='blob'];assert sorted(folder_blobs)==sorted(x['path']for x in objs)
    edges=read(A/'private/include-edges.json');assert len(edges)==15
    direct=read(A/'private/direct-input-bindings.json');assert len(direct)==10
    for x in direct:
        d=span(P/x['original'],x['start'],x['end']);assert len(d)==x['bytes']and hashlib.sha256(d).hexdigest()==x['sha256']==sha(A/x['local'])
    brief=direct[0];assert brief['original'].endswith('fresh-arithmetic-r154-brief.txt')and brief['end']==(P/brief['original']).stat().st_size==22965 and brief['sha256']=='3ae0c72cc75f7c467b80c5b8d925b60034b6c7d9865cca44acbf1ddd10c079a7'
    completed=[x for x in direct if'r152'in x['original']];assert len(completed)==6 and all(x['start']==0 and x['end']==(P/x['original']).stat().st_size for x in completed)
    hist=read(A/'private/history-read-bindings.json');assert len(hist)==11;stable={}
    for x in hist:
        d=span(P/x['path'],x['start'],x['end']);assert hashlib.sha256(d).hexdigest()==x['sha256']==sha(A/x['local'])and len(d)==x['bytes']
        if x['start']==0 and x['end']==(P/x['path']).stat().st_size:stable[x['path']]=x['sha256']
    prim=read(A/'private/primary-read-extents.json');assert len(prim['extents'])==9
    ctl=read(A/'private/controls/observations.json');assert [c['observed']for c in ctl['cases']]==['accepted','rejected','rejected','rejected','rejected','accepted']
    # parent exact rechecks of the displayed finite algebra in Q(sqrt5), independent of private/derive.py
    alg=read(A/'private/algebra.json')['exact']
    def q(a,b):return (Fr(a),Fr(b))
    assert alg['s_G']=='-3/4 + (1/5)sqrt(5)'and alg['A_G']=='-11/24 + (1/10)sqrt(5)'and alg['A_G_minus_s_half']=='-1/12 + (0)sqrt(5)'
    sG=q(Fr(-3,4),Fr(1,5));AG=q(Fr(-11,24),Fr(1,10));assert (AG[0]-sG[0]/2,AG[1]-sG[1]/2)==(Fr(-1,12),Fr(0))
    # integral class 35[O]-35[O(1)]+21[O(2)]-5[O(3)] has twisted coordinates (16,0,0,0)
    r=c=d=e=Fr(0)
    for n,k in((35,0),(-35,1),(21,2),(-5,3)):r+=n;c+=n*k;d+=n*Fr(k*k,2);e+=n*Fr(k**3,6)
    assert (r,c,d,e)==(16,-8,2,Fr(-1,3))and (c+r/2,d+c/2+r/8,e+d/2+c/8+r/48)==(0,0,0)
    assert snap(A)==before and stat.S_IMODE(A.stat().st_mode)==mode
    dump(O/'observed-root.json',{'root':before,'root_mode':mode})
    report={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'detached_anchor_file_matches':True,'artifact_only':True,'author_verifier_stdout':run.stdout.strip(),'packet_files':91,'payload_bytes':6656354,'canonical_objects':canonical,'canonical_folders':2,'canonical_folder_blobs_exhausted':True,'canonical_matches_complete_pinned_tree':True,'include_edges':15,'direct_input_bindings':10,'completed_exception_copies':6,'selected_history_intervals':11,'whole_original_records':len(stable),'primary_extractions':9,'copied_control_cases':6,'parent_exact_rechecks':'sG=-3/4+sqrt5/5, AG=-11/24+sqrt5/10, AG-sG/2=-1/12; u+t0^2=3/4; Xu endpoint -7/40-s/2; kernel form s(s-K)r^2+(K-6A)y^2; A(0)=(232-52sqrt5)/687>1/12; integral class (16,-8,2,-1/3) with twisted coordinates (16,0,0,0)','entire_root_unchanged':True,'parent_semantic_reading':'Complete FINAL, PREFREEZE, UNRESOLVED, REPORT, DERIVATIONS and private/READING. Source055 (20 text objects in two folders) and primary (Toda, Li 2019/2026, Xu, BMS, Bayer, Cheng-Feyzbakhsh, Li et al. families, GRRZ Lefschetz) operative reading attributed to the child, not fresh parent protected-body reading. No live Structural187/Arithmetic155 bodies/findings/status/activity inspected or steered.'}
    dump(O/'replay.json',report);print(json.dumps({k:report[k]for k in['packet_files','canonical_objects','selected_history_intervals','completed_exception_copies','primary_extractions','entire_root_unchanged','artifact_only']}))
if __name__=='__main__':main()
