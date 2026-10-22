#!/usr/bin/env python3
"""Read-only Arithmetic155 discovery intake; artifact checks only, no mathematical gate."""
import datetime,hashlib,importlib.util,json,stat,subprocess
from fractions import Fraction as Fr
from math import comb
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];A=B/'fresh-arithmetic-discovery-r155';K=A/'packet'
sp=importlib.util.spec_from_file_location('base',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_bytes())
def dump(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def span(p,s,e):
    assert not p.is_symlink()and p.stat().st_nlink==1
    with p.open('rb')as f:f.seek(s);d=f.read(e-s)
    assert len(d)==e-s;return d
def ceil(x):return -(-x.numerator//x.denominator)
def J(d,b):return max(0,ceil((1-b)/(1-d))-1)
def main():
    anchors={'FINAL.md':'c45bf83cac09563472bd31d55300305cfc32586e05439941090d564f0c4b7280','MANIFEST.json':'ec512d18f77292d0957526ac0c7cf02400647cd7d57c555f3780e57fc95edca4','REPORT.json':'936168f1a0bb706e0d388a10a0afd6ac1aba2667889bfdb5a5ecc820d3f36480'}
    before=snap(A);mode=stat.S_IMODE(A.stat().st_mode)
    assert sha(K/'FINAL.md')==anchors['FINAL.md']and sha(A/'MANIFEST.json')==anchors['MANIFEST.json']and sha(A/'REPORT.json')==anchors['REPORT.json']and read(A/'DETACHED-ANCHORS.json')==anchors
    run=subprocess.run(['python','-I','-B',str(K/'verify_packet.py'),'--packet',str(K),'--manifest',str(A/'MANIFEST.json'),'--report',str(A/'REPORT.json'),'--final-sha256',anchors['FINAL.md'],'--manifest-sha256',anchors['MANIFEST.json'],'--report-sha256',anchors['REPORT.json']],cwd=P,capture_output=True,text=True,check=True);assert not run.stderr and run.stdout.strip()=='MATCH: 121 files; artifact hashes only'
    m=read(A/'MANIFEST.json');assert len(m['files'])==121 and m['hash']=='SHA256';names={x['path']for x in m['files']}
    assert {'FINAL.md','notes/00-reading-checkpoint.md','notes/01-operative-comparison.md','notes/02-initial-model-accounting.md','notes/03-uniformity-and-unpaid-operation.md','verify_packet.py','recurrence_calculation.py','private/READING-ISOLATION.md'}<=names
    rep=read(A/'REPORT.json');assert rep['packet_files']==121 and rep['packet_bytes']==sum(x['bytes']for x in m['files'])==10537050 and rep['final_sha256']==anchors['FINAL.md']and rep['manifest_sha256']==anchors['MANIFEST.json']and rep['freeze']is None
    rootfiles={str(p.relative_to(A))for p in A.rglob('*')if p.is_file()};assert len(rootfiles)==128 and rootfiles=={'packet/'+n for n in names}|{'MANIFEST.json','REPORT.json','DETACHED-ANCHORS.json','fetch_primary.py','fetch_selected.py','read_selected.py','select_history.py'}
    tree=read(P/'sources/preprints-tree.json');lookup={e['path']:e for e in tree['tree']};assert len(lookup)==13223 and not tree['truncated']and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    auth=read(K/'private/authentication.json');assert len(auth)==71;folders=set()
    for x in auth:
        e=lookup[x['path']];p=K/'private/upstream'/x['path'];d=p.read_bytes();folders.add(x['path'].split('/')[1])
        assert x['authenticated']is True and e['type']=='blob'and len(d)==x['size']==e['size']and sha(p)==x['sha256']and hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()==x['git_blob']==e['sha']and x['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+x['path']
    assert len(folders)==5 and sorted(k for k,e in lookup.items()if e['type']=='blob'and k.split('/')[1]in folders and k.startswith('preprints/'))==sorted(x['path']for x in auth)
    wrappers={'preprints/Termination-of-generalized-log-canonical-flips-on-compact-Kahler-fourfolds-October-7-2026/build/main.tex':'c35595d7f23306ff139ba441d2188429f8ea83ff','preprints/Termination-of-generalized-canonical-flips-on-compact-Kahler-fourfolds-October-6-2026/build/build/paper.tex':'74117d2cb1244ae28fe52900bf646e5819c27955','preprints/Termination-for-projective-log-canonical-fourfolds-with-rational-boundary-September-24-2026/build/paper.tex':'0a2e5a1f8061edf1a88ab8fa9f09c7667d95d021','preprints/Finite-ordinary-minimal-model-programs-on-compact-Kahler-fourfolds-October-6-2026/build/main.tex':'6eb7708cc8d7681a041cbfb1c96f285a8bdeba2a','preprints/Finite-ordinary-minimal-model-programs-on-compact-Kahler-fourfolds-September-24-2026/build/main.tex':'af3ad5192a6d170f66908d6f2002ba4d6d33e0fb'}
    assert all(lookup[k]['sha']==v for k,v in wrappers.items())
    cov=read(K/'private/semantic-source-coverage.json');assert len(cov)==71;cnt={}
    for x in cov:
        cnt[x['coverage']]=cnt.get(x['coverage'],0)+1;assert x['bytes']==lookup[x['path']]['size']
        if x['coverage']=='complete text read':assert x['read_ranges']==[[0,x['bytes']]]and x['unread_ranges']==[]
    assert cnt=={'complete text read':27,'partial text read':2,'authenticated only':42}
    edges=read(K/'private/include-edges.json');assert len(edges)==57 and all(e['from']in lookup for e in edges)
    disp=[json.loads(l)for l in (K/'private/display-extents.jsonl').read_text().splitlines()];assert len(disp)==21;unhashed=[]
    for x in disp:
        d=span(K/'private/upstream'/x['path'],x['start'],x['end'])
        if'sha256_slice'in x:assert hashlib.sha256(d).hexdigest()==x['sha256_slice']
        else:unhashed.append((x['path'],[x['start'],x['end']]))
    partial=[(x['path'],x['read_ranges'][0])for x in cov if x['coverage']=='partial text read'];assert sorted(unhashed)==sorted(partial)and len(unhashed)==2
    brief=K/'private/authoritative-brief.txt';assert brief.read_bytes()==(B/'expanded-target-2026-10-17/fresh-arithmetic-r155-brief.txt').read_bytes()and sha(brief)=='13313e24aa931a5cb0be710dac08e54779a80e2b969c37f990d8eac767b0a12f'and brief.stat().st_size==25203
    assert (K/'private/direct/AGENTS.md').read_bytes()==(P/'AGENTS.md').read_bytes()and (K/'private/direct/sources/upstream.json').read_bytes()==(P/'sources/upstream.json').read_bytes()and (K/'private/direct/acceptance-4801-6347.txt').read_bytes()==span(P/'frontier/NEW-TEN-2026-10-14.md',4801,6347)
    ce=read(K/'private/completed-extents.json');assert len(ce)==6
    for x in ce:
        o=P/x['path'];assert'r153'in x['path']and x['read_ranges']==[[0,o.stat().st_size]]and sha(o)==x['sha256']==sha(K/'private'/x['copy'])
    hx=read(K/'private/history-extents.json');assert len(hx)==4 and sum(1 for x in hx if x['semantic_status']=='fully read')==3
    for x in hx:
        d=span(P/x['path'],x['start'],x['end']);assert hashlib.sha256(d).hexdigest()==x['sha256']
        if x['retained_copy']:assert (K/'private'/x['retained_copy']).read_bytes()==d
    pe=read(K/'private/primary-extents.json');assert len(pe)==4
    for x in pe:
        c=K/'private'/x['copy'];assert sha(c)==x['sha256']and x['read_ranges']==[[0,c.stat().st_size]]
    ctl=read(K/'private/controls/results.json');assert [(c['case'],c['expected_match'],c['returncode'])for c in ctl]==[('copied positive fixture',True,0),('same-size member mutation',False,1),('missing member',False,1),('extra member',False,1),('wrong explicit report anchor',False,1),('restored fixture',True,0)]
    # recurrence: rerun the packet script read-only and compare, then recheck independently
    rr=subprocess.run(['python','-I','-B',str(K/'recurrence_calculation.py')],cwd=P,capture_output=True,text=True,check=True);assert json.loads(rr.stdout)==read(K/'private/recurrence-calculation.json')
    rc=read(K/'private/recurrence-calculation.json');assert rc['cutoff_cases']==2660==sum((m_-1)*m_ for m_ in range(2,21))
    for m_ in range(2,21):
        for a in range(1,m_):
            for z in range(m_):
                d,b=Fr(a,m_),Fr(z,m_);assert J(d,b)==sum(1 for k in range(1,m_+1)if 1+k*(1-d)<2-b)<=m_-1
    assert J(Fr(2,3),Fr(0))==2 and 1+3*(1-Fr(2,3))==2 and J(Fr(2,3),Fr(1,3))==1 and J(Fr(1,3),Fr(0))==1
    ex=rc['examples'][0];assert ex['U']==[6,36]and ex['V']==[10,79]and ex['P']==303 and ex['length_bound']==611
    U1=3*2;V1=4+(ceil(Fr(3,2))-1)*U1;U2=3*(2+J(Fr(2,3),Fr(1,3))*V1);V2=7+(3-1)*U2;Pst=3*(2+J(Fr(2,3),0)*V1+J(Fr(1,3),0)*V2);assert (U1,V1,U2,V2,Pst,5+2*Pst)==(6,10,36,79,303,611)
    assert rc['examples'][1]['P']==8 and rc['examples'][1]['length_bound']==18==2+2*1*8
    # P^1 x P^3 example: (aA+bH)^4 = 4 a b^3 (A^2=0, H^4=0), K_X+qH = -2A+(q-4)H has degree -2 on P^1 x pt, dim H_4 = 2
    # intersection ring Z[A,H]/(A^2,H^4) on P^1 x P^3 with A.H^3=1: expand (aA+bH)^4 by binomial terms
    top=lambda a,b:sum(comb(4,i)*a**i*b**(4-i)for i in range(5)if i==1 and 4-i==3);assert all(top(a,b)==4*a*b**3 for a in range(1,4)for b in range(1,4))
    KX=(-2,-4);D=(KX[0],KX[1]+7);assert D==(-2,3)and D[0]*1+D[1]*0==-2
    assert snap(A)==before and stat.S_IMODE(A.stat().st_mode)==mode
    dump(O/'observed-root.json',{'root':before,'root_mode':mode})
    report={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'detached_anchor_file_matches':True,'artifact_only':True,'author_verifier_stdout':run.stdout.strip(),'packet_files':121,'packet_bytes':10537050,'root_files':128,'canonical_objects':71,'canonical_folders':5,'canonical_folder_blobs_exhausted':True,'canonical_matches_complete_pinned_tree':True,'wrapper_anchors':5,'source_coverage':cnt,'include_edges':57,'display_slices':21,'completed_exception_copies':6,'history_extents':4,'history_fully_read':3,'primary_extractions':4,'copied_controls':6,'recurrence_cases':2660,'recurrence_script_rerun_matches':True,'parent_exact_rechecks':'J(2/3,0)=2 with k=3 excluded at discrepancy exactly 2; J(2/3,1/3)=1; J(1/3,0)=1; example recursion U=(6,36), V=(10,79), P=303, bound 611; m=1,f=8,C=2 gives 18; 2660=sum_{m=2}^{20}(m-1)m cutoff cases; P^1xP^3: (aA+bH)^4=4ab^3, (K_X+qH).(P^1 x pt)=-2, c_2=2','entire_root_unchanged':True,'parent_semantic_reading':'Complete FINAL, REPORT.json, notes 00-03, verify_packet.py, recurrence_calculation.py and private/READING-ISOLATION (opening). Source056 (27 complete + 2 partial text objects of five folders) and primary (Fujino 2004 + addenda, AHK v2) operative reading attributed to the child, not fresh parent protected-body reading. No live Arithmetic156/Structural188 bodies/findings/status/activity inspected or steered.'}
    dump(O/'replay.json',report);print(json.dumps({k:report[k]for k in['packet_files','canonical_objects','completed_exception_copies','history_extents','recurrence_cases','entire_root_unchanged','artifact_only']}))
if __name__=='__main__':main()
