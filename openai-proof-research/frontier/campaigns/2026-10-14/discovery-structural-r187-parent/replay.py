#!/usr/bin/env python3
"""Read-only Structural187 discovery intake; artifact checks only, no mathematical gate."""
import datetime,hashlib,importlib.util,json,stat,subprocess
from itertools import product
from math import comb
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];A=B/'fresh-structural-discovery-r187'
sp=importlib.util.spec_from_file_location('base',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_bytes())
def dump(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def span(p,s,e):
    assert not p.is_symlink()and p.stat().st_nlink==1
    with p.open('rb')as f:f.seek(s);d=f.read(e-s)
    assert len(d)==e-s;return d
def main():
    anchors={'FINAL.md':'04aeec056fc5c09c14ba02caf4dec2a9b7b4976f6a23ee94451c329eb41cd57c','private/MANIFEST.json':'61720ee68bc29cc0fc099b3875f68e6e848df9e96d77876183add80526a32580','REPORT.md':'6fa12ef9890a927d4b89d5545ed22f8baadebcf1e355ddbb7909a597e1ea7905'}
    before=snap(A);mode=stat.S_IMODE(A.stat().st_mode);assert all(sha(A/p)==v for p,v in anchors.items())
    assert read(A/'ANCHORS.json')==anchors
    run=subprocess.run(['python','-I','-B',str(A/'VERIFY.py'),'--root',str(A),'--final-sha',anchors['FINAL.md'],'--manifest-sha',anchors['private/MANIFEST.json'],'--report-sha',anchors['REPORT.md'],'--originals',str(P)],cwd=P,capture_output=True,text=True,check=True);assert not run.stderr
    out=json.loads(run.stdout);assert out=={'artifact_verification':'matched','payload_files':82,'source_blobs':11,'original_spans':30,'mathematical_gate':False}
    m=read(A/'private/MANIFEST.json');assert m['schema']=='r187-selected-packet-v1'and len(m['files'])==82
    names={x['path']for x in m['files']};assert {'FINAL.md','DERIVATIONS.md','INTERFACES.md','COMPARISON.md','VERIFY.py','private/READING-LIMITS.md'}<=names
    allfiles={str(p.relative_to(A))for p in A.rglob('*')if p.is_file()};assert allfiles==names|{'private/MANIFEST.json','REPORT.md','ANCHORS.json'}
    tree=read(P/'sources/preprints-tree.json');lookup={e['path']:e for e in tree['tree']};assert len(lookup)==13223 and not tree['truncated']and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    folder='preprints/Stabilizer-Orbits-and-Thick-Tensor-Ideals-of-Dualizable-Kn-Local-Spectra-September-24-2026/'
    objs=read(A/'private/source-auth.json');assert len(objs)==11
    for x in objs:
        p=P/x['local'];d=p.read_bytes();e=lookup[x['path']]
        assert x['path'].startswith(folder)and p.resolve().is_relative_to(A.resolve())and len(d)==x['bytes']==e['size']and e['type']=='blob'and sha(p)==x['sha256']and hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()==x['git_blob']==e['sha']and x['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+x['path']
    assert sorted(k for k,e in lookup.items()if k.startswith(folder)and e['type']=='blob')==sorted(x['path']for x in objs)
    sre=read(A/'private/source-read-extents.json');assert len(sre)==11 and sum(1 for x in sre if x['semantic_read'])==10
    for x in sre:
        n=(A/x['local']).stat().st_size;assert n==x['bytes']
        if x['semantic_read']:
            iv=sorted(x['extents']);assert iv[0][0]==0 and iv[-1][1]==n and all(iv[i][1]==iv[i+1][0]for i in range(len(iv)-1))
    ob=read(A/'private/original-bindings.json');assert len(ob)==30;kinds={}
    for x in ob:
        kinds[x['kind']]=kinds.get(x['kind'],0)+1;d=span(P/x['path'],x['start'],x['end']);assert hashlib.sha256(d).hexdigest()==x['sha256']
        if 'copy'in x:assert (A/x['copy']).read_bytes()==d
    assert kinds=={'direct':5,'selected original heading extent':18,'exact completed direct exception':6,'metadata authentication only; not proof reading':1}
    brief=[x for x in ob if x['path'].endswith('fresh-structural-r187-brief.txt')][0];assert brief['start']==0 and brief['end']==(P/brief['path']).stat().st_size==21839 and brief['sha256']=='26f27b5ad930ed8995e0f3ba4059869c7edb701cd90162d55fba6d08e56796c4'
    nt=[x for x in ob if x['path']=='frontier/NEW-TEN-2026-10-14.md'][0];assert (nt['start'],nt['end'])==(4801,6347)
    cat=[x for x in ob if x['path']=='sources/CONTENTS.md'][0];assert (cat['start'],cat['end'])==(533720,534876)
    comp=[x for x in ob if x['kind']=='exact completed direct exception'];assert all(x['start']==0 and x['end']==(P/x['path']).stat().st_size and'r186'in x['path']for x in comp)
    hx=read(A/'private/history-extents.json');lx=read(A/'private/late-history-extents.json');assert len(hx)==16 and len(lx)==2
    for x in hx+lx:
        d=span(P/x['path'],x['start'],x['end']);assert hashlib.sha256(d).hexdigest()==x['sha256']and (A/'private'/x['copy']).read_bytes()==d
    pe=read(A/'private/primary-read-extents.json');assert [(x['name'],len(x['semantic_extents']))for x in pe]==[('ma-v1',1),('bhn-published',2),('li',2),('hs99',2),('bhn-v2',0)]
    for x in pe:
        txt=A/'private/primary'/(x['name']+'.txt');assert sha(txt)==x['text_sha256']
        for s in x['semantic_extents']:
            a,b=s['text_bytes'];assert hashlib.sha256(span(txt,a,b)).hexdigest()==s['sha256']
    ctl=read(A/'private/control-results.json');assert [(c['control'],c['expected_exit'],c['actual_exit'])for c in ctl['controls']]==[('valid',0,0),('damaged-copy',1,1),('wrong-detached-anchor',1,1)]and ctl['original_tiny_payload_unchanged']is True and ctl['mathematical_gate']is False
    # parent independent rechecks of the elementary finite data (not a mathematical gate)
    fc=read(A/'private/finite-calculation.json');assert len(fc['quotients'])==135 and len(fc['weights'])==54
    for q in fc['quotients']:
        # k[[x1,x2]]/((x1+x2^D)+m^M) = k[[x2]]/(x2^M); least e with x1^e=0 is ceil(M/D); dimension of B_M is C(M+1,2)
        assert q['quotient_dimension']==q['M']and q['least_e']==q['formula']==-(-q['M']//q['D'])and q['dimension_BM']==comb(q['M']+1,2)
    for w in fc['weights']:
        r,D=w['r'],w['D'];assert w['sum_degree']==r*comb(D+r,r+1)
        if r<=3 and D<=4:assert w['sum_degree']==sum(sum(b)for b in product(range(D+1),repeat=r)if sum(b)<=D)
    # |U_a/U_M| = p^{n^2 (M-a)} (A_n has Z_p-rank n^2); dim B_h/m^M = C(M+r-1,r)
    assert all(comb(M+r-1,r)==sum(comb(d+r-1,r-1)for d in range(M))for r in range(1,5)for M in range(1,8))
    assert snap(A)==before and stat.S_IMODE(A.stat().st_mode)==mode
    dump(O/'observed-root.json',{'root':before,'root_mode':mode})
    report={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'detached_anchor_file_matches':True,'artifact_only':True,'author_verifier_stdout':run.stdout.strip(),'packet_files':82,'root_files':85,'canonical_objects':11,'canonical_folder_blobs_exhausted':True,'canonical_matches_complete_pinned_tree':True,'source_text_objects_fully_read':10,'original_bindings':30,'original_binding_kinds':kinds,'selected_history_sections':16,'late_history_sections':2,'completed_exception_copies':6,'primary_extractions':5,'copied_controls':3,'finite_quotient_cases':135,'weight_identities':54,'parent_exact_rechecks':'ceil(M/D) exponent and quotient dimension M for all 135 cases; dim B_M=C(M+1,2); sum_{|beta|<=D}|beta|=r*C(D+r,r+1) for all 54 pairs (brute force r<=3,D<=4); C(M+r-1,r) monomial count; |U_a/U_M|=p^{n^2(M-a)} from Z_p-rank n^2','entire_root_unchanged':True,'parent_semantic_reading':'Complete FINAL, REPORT, DERIVATIONS, INTERFACES, COMPARISON, VERIFY.py and private/READING-LIMITS. Source311 (ten text objects) and primary (Ma 2610.10072v1, BHN published, Li Drive PDF, Hovey-Strickland 1999) operative reading attributed to the child, not fresh parent protected-body reading. No live Arithmetic155/Arithmetic156 bodies/findings/status/activity inspected or steered.'}
    dump(O/'replay.json',report);print(json.dumps({k:report[k]for k in['packet_files','canonical_objects','original_bindings','selected_history_sections','finite_quotient_cases','entire_root_unchanged','artifact_only']}))
if __name__=='__main__':main()
