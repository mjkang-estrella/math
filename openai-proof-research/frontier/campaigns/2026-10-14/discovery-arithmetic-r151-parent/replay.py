#!/usr/bin/env python3
"""Read-only Arithmetic151 r2 recovery intake; artifact checks only, no mathematical gate."""
import datetime,hashlib,importlib.util,json,stat,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];A=B/'fresh-arithmetic-discovery-r151'
sp=importlib.util.spec_from_file_location('base',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_bytes())
def dump(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def main():
    anchors={'FINAL.md':'af2101e1de9cf088cdb065debcee9db76c2ffa4464730f5e28ab546b800e071d','MANIFEST.json':'62b408c068aa43b599824861c70abecaf087e93e9ba42ad5897b2a023f98545b','REPORT.md':'8d82a3f5fd69d228937213005815e98283277425a100ff45aed918a197f294d8'}
    before=snap(A);mode=stat.S_IMODE(A.stat().st_mode);assert all(sha(A/p)==v for p,v in anchors.items())
    detached=read(A/'ANCHORS.json');assert detached==anchors
    run=subprocess.run(['python','-I','-B',str(A/'verify.py'),'--root',str(A),'--final-sha256',anchors['FINAL.md'],'--manifest-sha256',anchors['MANIFEST.json'],'--report-sha256',anchors['REPORT.md']],cwd=P,capture_output=True,text=True,check=True);assert not run.stderr
    out=json.loads(run.stdout);assert out['artifact_integrity']=='matched'and out['members']==77 and out['source_blobs']==25 and out['r1_files_unchanged']==49 and out['mathematical_verdict']is None
    m=read(A/'MANIFEST.json');assert m['schema']=='r151-packet-v1'and len(m['files'])==77
    # packet working-copy bindings: every public packet member equals its working copy
    public=[r for r in m['files']if not r['path'].startswith('private/')];assert all((A/'packet'/r['path']).read_bytes()==(A/r['path']).read_bytes()for r in public)
    tree=read(P/'sources/preprints-tree.json');lookup={e['path']:e for e in tree['tree']};assert len(lookup)==13223 and not tree['truncated']and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    objs=read(A/'private/source-auth.json');assert len(objs)==25;folders=set();canonical=0
    for x in objs:
        p=A/x['local'];d=p.read_bytes();e=lookup[x['path']];folders.add(x['path'].split('/build/')[0])
        assert p.resolve().is_relative_to(A.resolve())and len(d)==x['bytes']==e['size']and sha(p)==x['sha256']and hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()==x['git_blob']==e['sha']and'/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'in x['url'];canonical+=1
    assert len(folders)==2
    ranges=read(A/'private/original-extents.json');auth=read(A/'private/r2-original-auth.json');assert len(ranges)==3 and all(a['fresh_r2_exact_range_matches']for a in auth);stable={}
    for i,x in enumerate(ranges):
        p=P/x['path'];assert not p.is_symlink()and p.stat().st_nlink==1 and sha(p)==x['full_sha256']
        with p.open('rb')as f:f.seek(x['start']);data=f.read(x['end']-x['start'])
        assert len(data)==x['end']-x['start']and hashlib.sha256(data).hexdigest()==x['sha256']==auth[i]['sha256']and data==(A/f'private/original-{i}.txt').read_bytes()
        if x['start']==0 and x['end']==p.stat().st_size:stable[x['path']]=x['sha256']
    completed=['discovery-arithmetic-r149-parent/assessment.md','fresh-arithmetic-discovery-r149/FINAL.md','fresh-arithmetic-discovery-r149/notes/01-operative-map.md','fresh-arithmetic-discovery-r149/notes/02-dynamical-certificate.md','fresh-arithmetic-discovery-r149/notes/03-convex-limit-and-boundary-interface.md','fresh-arithmetic-discovery-r149/READING-ISOLATION.md']
    assert all((A/'private/r2-completed'/c).read_bytes()==(B/c).read_bytes()for c in completed)
    controls=read(A/'private/r2-control-results.json');assert len(controls)==5 and all(c['accepted']==c['expected']for c in controls)and sum(c['expected']for c in controls)==1
    brief=B/'user-resume-2026-10-22-parent/arithmetic151-recovery-r2-brief.txt';assert sha(brief)=='0291883ce2ddbe02bd5bb63d5239b91fa73983400c21318ff7e3b550a0865dd9'and(A/'private/r2-authoritative-brief.txt').read_bytes()==brief.read_bytes()
    assert snap(A)==before and stat.S_IMODE(A.stat().st_mode)==mode
    dump(O/'observed-root.json',{'root':before,'root_mode':mode})
    report={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'detached_anchor_file_matches':True,'artifact_only':True,'author_verifier_stdout':run.stdout.strip(),'packet_members':77,'public_packet_members_match_working_copies':len(public),'canonical_objects':canonical,'canonical_folders':2,'canonical_matches_complete_pinned_tree':True,'selected_history_intervals':3,'whole_original_records':len(stable),'completed_exception_copies':6,'copied_controls':5,'r1_baseline_files_unchanged':49,'authoritative_recovery_brief_copy_matches':True,'entire_root_unchanged':True,'parent_semantic_reading':'Complete FINAL, REPORT, RECOVERY, READING-ISOLATION, verify.py and notes/01-03. Source052 (25 TeX objects) and primary (Horing 2007/2008/2026, Beauville, Muller, Wang, Biswas-Dumitrescu) operative reading attributed to the child, not fresh parent protected-body reading. No live Arithmetic152/Structural186 bodies/findings/status/activity inspected or steered.'}
    dump(O/'replay.json',report);print(json.dumps({k:report[k]for k in['packet_members','canonical_objects','selected_history_intervals','completed_exception_copies','r1_baseline_files_unchanged','entire_root_unchanged','artifact_only']}))
if __name__=='__main__':main()
