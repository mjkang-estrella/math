#!/usr/bin/env python3
"""Read-only Structural188 discovery intake; artifact checks only, no mathematical gate."""
import datetime,hashlib,importlib.util,json,stat,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];A=B/'fresh-structural-discovery-r188'
sp=importlib.util.spec_from_file_location('base',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_bytes())
def dump(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def span(p,s,e):
    assert not p.is_symlink()and p.stat().st_nlink==1
    with p.open('rb')as f:f.seek(s);d=f.read(e-s)
    assert len(d)==e-s;return d
def globe_cells(j):
    # cell counts of the free globular set d_j by dimension: two parallel cells in each dimension <j, one top cell
    return [2]*j+[1]
def boundary_cells(j):return [2]*j
def pushout_cells(X,Y,Z):
    # cell counts of X amalgam_Z Y for a span of injective globular maps: |X|+|Y|-|Z| dimensionwise
    n=max(len(X),len(Y));g=lambda L,i:L[i]if i<len(L)else 0
    return [g(X,i)+g(Y,i)-g(Z,i)for i in range(n)]
def main():
    anchors={'FINAL.md':'92f936f1b023bf1d29810d25027e51c77dca14077c7a9a65a23ea166d63ee4e7','private/MANIFEST.json':'cd6000741bcd027f8cd8ac1e4f21afe966b628a0a79694f7ae649567dafa3d9e','REPORT.md':'d6c331996158968b524b84aea351dacaddcadd518974c2a40af0670e822c9628'}
    before=snap(A);mode=stat.S_IMODE(A.stat().st_mode);assert all(sha(A/p)==v for p,v in anchors.items())
    assert read(A/'ANCHORS.json')==anchors
    run=subprocess.run(['python','-I','-B',str(A/'VERIFY.py'),'--root',str(A),'--final',anchors['FINAL.md'],'--manifest',anchors['private/MANIFEST.json'],'--report',anchors['REPORT.md'],'--originals',str(P)],cwd=P,capture_output=True,text=True,check=True);assert not run.stderr
    assert run.stdout=='Matched 21 exact original spans and 12 canonical source blobs.\nMatched artifact verification on 74 payload files; no mathematical gate.\n'
    m=read(A/'private/MANIFEST.json');assert m['schema']==1 and m['source_pin']=='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'and len(m['files'])==74
    names={x['path']for x in m['files']};assert {'FINAL.md','DERIVATIONS.md','INTERFACES.md','COMPARISON.md','VERIFY.py','private/READING-LIMITS.md'}<=names
    for x in m['files']:assert (A/x['path']).stat().st_size==x['bytes']and sha(A/x['path'])==x['sha256']
    allfiles={str(p.relative_to(A))for p in A.rglob('*')if p.is_file()};assert allfiles==names|{'private/MANIFEST.json','REPORT.md','ANCHORS.json'}and len(allfiles)==77
    tree=read(P/'sources/preprints-tree.json');lookup={e['path']:e for e in tree['tree']};assert len(lookup)==13223 and not tree['truncated']and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    folder='preprints/The-Grothendieck-homotopy-hypothesis-via-elementary-expansions-September-24-2026/'
    objs=read(A/'private/source-auth.json');assert len(objs)==12
    for x in objs:
        p=P/x['local'];d=p.read_bytes();e=lookup[x['path']]
        assert x['path'].startswith(folder)and p.resolve().is_relative_to(A.resolve())and len(d)==x['bytes']==e['size']and e['type']=='blob'and sha(p)==x['sha256']and hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()==x['git_blob']==e['sha']and x['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+x['path']
    assert sorted(k for k,e in lookup.items()if k.startswith(folder)and e['type']=='blob')==sorted(x['path']for x in objs)
    wrap=[x for x in objs if x['path'].endswith('build/paper.tex')][0];assert wrap['bytes']==811 and wrap['git_blob']=='4e5dfc67207defee08e240655efe1a6689dab9a0'
    sre=read(A/'private/source-read-extents.json');assert len(sre)==11
    for x in sre:
        p=A/x['copy'];assert x['start']==0 and x['end']==p.stat().st_size==lookup[x['path']]['size']and sha(p)==x['sha256']
    assert {x['path']for x in objs}-{x['path']for x in sre}=={folder+'paper.pdf'}
    ob=read(A/'private/original-bindings.json');assert len(ob)==21
    for x in ob:
        d=span(P/x['path'],x['start'],x['end']);assert hashlib.sha256(d).hexdigest()==x['sha256']and (A/x['copy']).read_bytes()==d
    brief=[x for x in ob if x['path'].endswith('fresh-structural-r188-brief.txt')][0];assert brief['start']==0 and brief['end']==(P/brief['path']).stat().st_size==23221 and brief['sha256']=='c25d02dfc45de31208cb8f7c8f6f3c1d2f7907f2ecd4f3e047d93d851495a351'
    nt=[x for x in ob if x['path']=='frontier/NEW-TEN-2026-10-14.md'][0];assert (nt['start'],nt['end'])==(4801,6347)
    assert not any(x['path']=='sources/CONTENTS.md'for x in ob)
    comp=[x for x in ob if x['copy'].startswith('private/completed/')];assert len(comp)==6 and all(x['start']==0 and x['end']==(P/x['path']).stat().st_size and'r187'in x['path']for x in comp)
    hx=read(A/'private/original-extents.json');px=read(A/'private/primitive-extents.json');assert len(hx)==6 and len(px)==5
    hist={(x['path'],x['start'],x['end'])for x in hx+px};assert hist<={(x['path'],x['start'],x['end'])for x in ob}and len(hist)==11
    for x in hx+px:assert not any(t in x['path']for t in('r188','r187','r156','r157','structural-discovery-r18','arithmetic-discovery-r15'))
    pe=read(A/'private/primary-read-extents.json');assert len(pe)==70
    byname={}
    for x in pe:
        byname[x['name']]=byname.get(x['name'],0)+1;assert hashlib.sha256((A/x['copy']).read_bytes()[x['start']:x['end']]).hexdigest()==x['sha256']
    assert byname=={'lanari':30,'ara':12,'henry':10,'taylor':9,'henry-lanari':9}
    acq=read(A/'private/primary/acquisition.json');acq2=read(A/'private/primary/acquisition-2.json');assert len(acq)==5 and acq2['name']=='henry-lanari'
    for x in acq:
        if 'sha256'in x:assert sha(A/'private/primary'/(x['name']+'.pdf'))==x['sha256']and (A/'private/primary'/(x['name']+'.pdf')).stat().st_size==x['bytes']
    assert sha(A/'private/primary/henry-lanari.pdf')==acq2['sha256']and (A/'private/primary/henry-lanari.pdf').stat().st_size==acq2['bytes']
    ctl=read(A/'private/controls/results.json');assert [(c['case'],c['exit'])for c in ctl['controls']]==[('valid copied packet',0),('damaged copied payload',1),('wrong detached anchor',1)]and ctl['seed_unchanged']is True
    assert all(sha(A/'private/controls/seed'/k)==v for k,v in ctl['seed_anchors'].items())
    # parent independent rechecks of the elementary globular cell counts used by the gluing formulas (not a mathematical gate)
    for j in range(0,8):
        # partial d_{j+1} = d_j amalgam_{partial d_j} d_j
        assert pushout_cells(globe_cells(j),globe_cells(j),boundary_cells(j))==boundary_cells(j+1)
        # the two endpoint j-cells plus the lower boundary cylinder data: D_j+D_j glued along partial D_j + partial D_j adds exactly two top cells
        assert pushout_cells(globe_cells(j),globe_cells(j),[0]*(j+1))[j]==2
    # two-edge arity d_1 amalgam_{d_0} d_1 has 3 objects and 2 one-cells; its two-sided boundary data in the cylinder uses one shared T_0 factor
    assert pushout_cells(globe_cells(1),globe_cells(1),globe_cells(0))==[3,2]
    # two-cube diagnostic: the start point (base 0, fibre (0,1)) lies in cube 1 but outside the closed cube 2 (cube 2 meets cube 1 only along z=0)
    x=(0.0,0.0,1.0);in_cube2=lambda p:0<=p[0]<=1 and 0<=p[1]<=1 and 0<=p[2]<=1 and (p[0]>0 or p[2]==0)
    assert not in_cube2(x)and in_cube2((0.0,0.0,0.0))and all(in_cube2((t,0.0,0.0))for t in(0.25,0.5,1.0))
    assert snap(A)==before and stat.S_IMODE(A.stat().st_mode)==mode
    dump(O/'observed-root.json',{'root':before,'root_mode':mode})
    report={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'detached_anchor_file_matches':True,'artifact_only':True,'author_verifier_stdout':run.stdout.strip(),'packet_files':74,'root_files':77,'canonical_objects':12,'canonical_folder_blobs_exhausted':True,'canonical_matches_complete_pinned_tree':True,'wrapper_anchor':{'path':folder+'build/paper.tex','bytes':811,'git_blob':'4e5dfc67207defee08e240655efe1a6689dab9a0'},'source_text_objects_fully_read':11,'source_pdf_authenticated_only':1,'original_bindings':21,'completed_exception_copies':6,'history_sections':11,'primary_pages':70,'primary_pdfs':5,'copied_controls':3,'parent_exact_rechecks':'globular cell counts of partial d_{j+1}=d_j amalgam_{partial d_j} d_j for j<=7; two top cells added by D_j+D_j; two-edge arity cell counts [3,2]; two-cube diagnostic start point outside the closed second cube while the base path enters it','entire_root_unchanged':True,'parent_semantic_reading':'Complete FINAL, REPORT, DERIVATIONS, COMPARISON, VERIFY.py and openings of INTERFACES and private/READING-LIMITS. Source312 (eleven text objects) and primary (Henry 1609.04622v1, Ara 1206.2941v2, Lanari, Taylor, Henry-Lanari TAC 39) operative reading attributed to the child, not fresh parent protected-body reading. No live Arithmetic156/Arithmetic157 bodies/findings/status/activity inspected or steered.'}
    dump(O/'replay.json',report);print(json.dumps({k:report[k]for k in['packet_files','canonical_objects','original_bindings','history_sections','primary_pages','entire_root_unchanged','artifact_only']}))
if __name__=='__main__':main()
