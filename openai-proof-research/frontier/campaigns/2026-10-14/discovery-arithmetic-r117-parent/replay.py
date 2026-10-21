#!/usr/bin/env python3
"""Completed arithmetic117 byte archive; no mathematical execution or gate."""
import datetime,hashlib,importlib.util,json,shutil,subprocess,sys,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-arithmetic-discovery-r117'
spec=importlib.util.spec_from_file_location('archive_helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'ccd80c8c72d69928a90c95dbd5d17333ab13d8d77ffc8734f0407d4518edafc2','MANIFEST.json':'e55c41f507b32ba76484405f06df94d191aba02c10cafb582423b789e22d0277','REPORT.md':'0dcd50aae28152d17ff423ddba70f4302eda8095378557a6a2fbe7ad92d97529'}
PROTECTED={'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json':'6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9','frontier/iterations/i31-nonconical-no-mcm.md':'d606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
    now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=P)
    assert len(read(B/'tasks.json')['tasks'])==513
    dump('integration-baseline.json',{'observed_utc':now,'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip(),'initial_index_empty':True,'task_count':513,'task_index':510,'protected_unrelated_sha256':PROTECTED})
    before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current completed whole root excluding root-directory mode;no historical whole-project or OS certificate.'})
    st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and not st['hasPendingChildRuns'] and all(v in st['summary'] for v in ANCHORS.values())
    assert all(sha(ROOT/n)==v for n,v in ANCHORS.items())
    m=read(ROOT/'MANIFEST.json');assert m['format']=='r117-exact-v1' and len(m['payload_files'])==66 and len(m['directories'])==9
    assert {p for p,e in before.items() if e['kind']=='file'}==set(m['payload_files'])|set(ANCHORS) and {p for p,e in before.items() if e['kind']=='directory'}==set(m['directories'])
    for n,e in (m['payload_files']|m['envelopes']).items():assert (ROOT/n).stat().st_size==e['size'] and sha(ROOT/n)==e['sha256']
    tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']}
    source=read(ROOT/'packet/source-identities.json');assert len(source)==24
    prefixes=['preprints/A-pointwise-2-converse-for-elliptic-curves-with-rational-two-torsion-October-7-2026/','preprints/Hilberts-tenth-problem-over-the-rational-numbers-October-6-2026/']
    assert {e['canonical_path'] for e in source}=={p for p,e in entries.items() if e['type']=='blob' and any(p.startswith(x) for x in prefixes) and not p.endswith('.pdf')}
    for e in source:
        data=(ROOT/e['selected_copy']).read_bytes();node=entries[e['canonical_path']]
        assert len(data)==e['size']==node['size'] and sha(ROOT/e['selected_copy'])==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['gitblob']==node['sha']
        assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['canonical_path']
    primary=read(ROOT/'packet/primary-identities.json');assert len(primary)==1
    for e in primary:
        p=ROOT/'packet/private/primary'/(e['name']+'.pdf');assert p.stat().st_size==e['size'] and sha(p)==e['sha256'] and sha(p.with_suffix('.txt'))==e['extract_sha256']
    stable=[];excerpts=[];incoming=read(ROOT/'packet/incoming-identities.json');assert len(incoming)==12
    for e in incoming:
        q=ROOT/e['selected_copy'];assert q.stat().st_size==e['selected_size'] and sha(q)==e['selected_sha256']
        if e['selection']=='whole':
            p=P/e['original'];assert p.read_bytes()==q.read_bytes() and p.stat().st_size==e['whole_size'] and sha(p)==e['whole_sha256_at_capture'];stable.append({'path':e['original'],'sha256':e['whole_sha256_at_capture'],'bytes':e['whole_size'],'limit':'Late current whole-copy equality,not first-read/inherited-archive certification or fresh semantic reading.'})
        else:excerpts.append(e|{'limit':'Retained selected excerpt only;old whole observed identity is not a current/future stability input.'})
    assert len(stable)==10 and len(excerpts)==2
    recheck=read(ROOT/'packet/identity-recheck.json');assert recheck['tree_sha256']==sha(tp) and len(recheck['canonical_sources'])==24 and all(e['matches'] for e in recheck['canonical_sources'])
    assert len(recheck['incoming'])==12 and all(e['copy_matches'] for e in recheck['incoming']) and [e['original'] for e in recheck['incoming'] if not e['whole_current_matches_capture']]==['frontier/NEW-TEN-2026-10-14.md']
    ctl=read(ROOT/'packet/artifact-controls.json');fixture=ROOT/'packet/private/control-selection';fm=read(fixture/'MANIFEST.json')
    assert len(ctl['cases'])==7 and len(ctl['selected_originals'])==3 and len(fm['payload_files'])==3
    for n,v in ctl['own_selection_anchors'].items():assert sha(fixture/n)==v
    for n in ctl['selected_originals']:
        copied='packet/'+Path(n).name;assert (fixture/copied).read_bytes()==(ROOT/n).read_bytes() and sha(ROOT/n)==fm['payload_files'][copied]['sha256']
    assert all(e['accepted']==e['expected_accept'] and e['read_only'] for e in ctl['cases'])
    cases=[]
    with tempfile.TemporaryDirectory(prefix='arithmetic117-copy-',dir=O) as temp:
        copy=Path(temp)/'packet';shutil.copytree(ROOT,copy);args=[str(copy),'--final-sha256',ANCHORS['FINAL.md'],'--manifest-sha256',ANCHORS['MANIFEST.json'],'--report-sha256',ANCHORS['REPORT.md']]
        def check(label,want,custom=None):
            state=snap(copy);r=subprocess.run([sys.executable,'-I','-B',str(copy/'packet/code/verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30)
            assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state
            cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
        check('baseline_full_packet',True)
        p=copy/'packet/notes/finite-test-reduction.md';data=p.read_bytes();p.write_bytes(data+b'\nCONTROL\n');check('modified_payload',False);p.unlink();check('missing_payload',False);p.write_bytes(data)
        p=copy/'packet/private/.extra';p.write_text('extra');check('extra_hidden_file',False);p.unlink();p=copy/'packet/private/.empty';p.mkdir();check('extra_empty_directory',False);p.rmdir()
        wrong=args.copy();wrong[4]='0'*64;check('wrong_external_manifest_anchor',False,wrong);check('restored',True);assert snap(copy)==before
    assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in PROTECTED.items())
    dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':5,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Seven complete disposable-copy controls;the child seven selected-copy tests remain separate.Artifact evidence only.'})
    dump('input-authentication.json',{'source_blobs':24,'primary_pdf_files':1,'byte_bound_extracts':1,'byte_bound_renders':3,'stable_whole_original_copies':10,'mutable_original_excerpts':2,'selected_fixture_members':3,'limits':'Local canonical bytes/retained-copy checks only,no fresh network/protected-body semantic/visual reading or inherited whole-archive certificate.'})
    dump('replay.json',{'observed_utc':now,'external_handoff_anchors':ANCHORS,'payload_files':66,'whole_root_files':69,'subdirectories':9,'source_blobs':24,'primary_pdf_files':1,'stable_named_originals':stable,'mutable_original_excerpts':excerpts,'artifact_cases':7,'negative_cases':5,'whole_actual_root_unchanged':True,'limits':'Artifact archive only,no mathematical numerical/formal suite or independent grade.Verifier excludes modes,parent snapshots exclude rootmode.'})
    print(json.dumps({'files':69,'subdirectories':9,'source_blobs':24,'primary_pdfs':1,'stable_whole_originals':10,'excerpts':2,'cases':7}))

if __name__=='__main__':main()
