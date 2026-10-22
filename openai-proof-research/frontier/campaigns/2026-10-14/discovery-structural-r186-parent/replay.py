#!/usr/bin/env python3
"""Read-only Structural186 discovery intake; artifact checks only, no mathematical gate."""
import datetime,hashlib,importlib.util,json,stat,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];A=B/'fresh-structural-discovery-r186'
sp=importlib.util.spec_from_file_location('base',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_bytes())
def dump(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def span(rel,s,e):
    p=P/rel;assert not p.is_symlink()and p.stat().st_nlink==1
    with p.open('rb')as f:f.seek(s);d=f.read(e-s)
    assert len(d)==e-s;return d
def main():
    anchors={'FINAL.md':'f27c24880395fe3bc56e2b2914da37b0bc4b020325abc04fd17ae06656cf04ee','private/MANIFEST.json':'9abca92ba5d37040b9995fc1a597e75b9748fae84e661061743c0a80679dd449','REPORT.md':'4465d43c4a78c21194dbc37e5dc049002389165e3d5e6d9af1c6c8eca8340656'}
    before=snap(A);mode=stat.S_IMODE(A.stat().st_mode);assert all(sha(A/p)==v for p,v in anchors.items())
    detached=read(A/'ANCHORS.json');assert all(detached[p]==v for p,v in anchors.items())
    run=subprocess.run(['python','-I','-B',str(A/'VERIFY.py'),'--final-sha',anchors['FINAL.md'],'--manifest-sha',anchors['private/MANIFEST.json'],'--report-sha',anchors['REPORT.md'],'--originals'],cwd=P,capture_output=True,text=True,check=True);assert not run.stderr
    out=json.loads(run.stdout);assert out['artifact_integrity']=='consistent'and out['payload_files']==79 and out['canonical_git_blobs_checked']==16 and out['explicit_original_spans_checked']is True and out['writes']==0 and out['mathematical_grade']is None
    m=read(A/'private/MANIFEST.json');assert len(m['files'])==79 and m['pin']=='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'and m['disposition']=='PREFREEZE/no nominee'and set(m['excluded_detached_files'])=={'ANCHORS.json','REPORT.md','private/MANIFEST.json'}
    paths=[x['path']for x in m['files']];assert len(set(paths))==79 and all((A/p).is_file()and len((A/p).read_bytes())==x['bytes']and sha(A/p)==x['sha256']for p,x in zip(paths,m['files']))
    tree=read(P/'sources/preprints-tree.json');lookup={e['path']:e for e in tree['tree']};assert len(lookup)==13223 and not tree['truncated']and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    objs=read(A/'private/source310-authentication.json');assert len(objs)==16;canonical=0;folders=set()
    for x in objs:
        p=A/x['local'];d=p.read_bytes();e=lookup[x['path']];folders.add(x['path'].split('/')[1])
        assert p.resolve().is_relative_to(A.resolve())and len(d)==x['bytes']==e['size']and e['type']=='blob'and sha(p)==x['sha256']and hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()==x['git_blob']==e['sha']and x['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+x['path'];canonical+=1
    assert folders=={'Rational-homology-and-Quillens-conjecture-September-24-2026'}
    folder_blobs=[k for k,e in lookup.items()if k.startswith('preprints/Rational-homology-and-Quillens-conjecture-September-24-2026/')and e['type']=='blob'];assert sorted(folder_blobs)==sorted(x['path']for x in objs)
    ranges=read(A/'private/history-extents.json');assert len(ranges)==8;stable={}
    for x in ranges:
        d=span(x['path'],x['start'],x['end']);assert hashlib.sha256(d).hexdigest()==x['sha256']and d==(A/x['local']).read_bytes()
        if x['start']==0 and x['end']==(P/x['path']).stat().st_size:stable[x['path']]=x['sha256']
    comp=read(A/'private/completed-input-anchors.json');assert len(comp)==6
    for x in comp:
        d=(P/x['path']).read_bytes();assert len(d)==x['bytes']and hashlib.sha256(d).hexdigest()==x['sha256']==sha(A/x['local'])and x['path'].startswith(('frontier/campaigns/2026-10-14/discovery-structural-r185-parent/','frontier/campaigns/2026-10-14/fresh-structural-discovery-r185/'))
    direct=read(A/'private/direct-input-anchors.json');assert len(direct)==4
    for x in direct:assert hashlib.sha256(span(x['path'],x['start'],x['end'])).hexdigest()==x['sha256']
    brief=[x for x in direct if x['path'].endswith('fresh-structural-r186-brief.txt')][0];assert brief['end']==(P/brief['path']).stat().st_size==21454
    assert snap(A)==before and stat.S_IMODE(A.stat().st_mode)==mode
    dump(O/'observed-root.json',{'root':before,'root_mode':mode})
    report={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'detached_anchor_file_matches':True,'artifact_only':True,'author_validator_stdout':run.stdout.strip(),'payload_files':79,'canonical_objects':canonical,'canonical_folder_blobs_exhausted':True,'canonical_matches_complete_pinned_tree':True,'selected_history_intervals':8,'whole_original_records':len(stable),'completed_exception_copies':6,'direct_input_anchors':4,'brief_whole_file_anchored':True,'entire_root_unchanged':True,'parent_semantic_reading':'Complete FINAL, REPORT, DERIVATIONS, INTERFACES, COMPARISON and private/READING-LIMITS. Source310 and primary (Piterman 2021, Piterman-Smith, Piterman 2026, Piterman-Welker, Diaz Ramos 2016/2026, Segev-Webb 1994 + correction) operative reading attributed to the child, not fresh parent protected-body reading. Parent recomputed the finite checks: K_{3,3} first Betti number 4, stacked residue rank 4 versus single residue rank 2, Segev-Webb [I I I] rank 2 with beta_1=4, and the symplectic bracket 3/8-3/32-1/4=1/32 at n=3,u=5. No live Arithmetic153/Arithmetic154 bodies/findings/status/activity inspected or steered.'}
    dump(O/'replay.json',report);print(json.dumps({k:report[k]for k in['payload_files','canonical_objects','selected_history_intervals','completed_exception_copies','direct_input_anchors','entire_root_unchanged','artifact_only']}))
if __name__=='__main__':main()
