#!/usr/bin/env python3
"""Completed structural152 artifact/finite archive,no universal mathematical gate."""
import datetime,hashlib,importlib.util,json,shutil,subprocess,sys,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-structural-discovery-r152'
spec=importlib.util.spec_from_file_location('archive_helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'4e99dbc4344d1f018946e29f5961e43f4bb2ad9a6755c7099bb1080f1d2b1812','MANIFEST.json':'43b78fce7b6e61ee5dd676a8a354a49fbbb7e868e071777b2184beacf6347fe3','REPORT.md':'0b431d87521f133d94baaaab926db48f54c64bd5289e6ad5e2e68adde134ea0b'}
PROTECTED={'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json':'6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9','frontier/iterations/i31-nonconical-no-mcm.md':'d606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
    now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=P)
    assert len(read(B/'tasks.json')['tasks'])==514
    dump('integration-baseline.json',{'observed_utc':now,'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip(),'initial_index_empty':True,'task_count':514,'task_index':511,'protected_unrelated_sha256':PROTECTED})
    before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current completed whole-root snapshot excluding root-directory mode;manifest separately names dot root,no historical whole-project or OS certificate.'})
    st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and not st['hasPendingChildRuns'] and all(v in st['summary'] for v in ANCHORS.values())
    assert all(sha(ROOT/n)==v for n,v in ANCHORS.items())
    m=read(ROOT/'MANIFEST.json');assert m['schema']=='r152-exact-payload-v1' and len(m['files'])==62
    assert {p for p,e in before.items() if e['kind']=='file'}==set(m['files'])|set(ANCHORS)
    assert {p for p,e in before.items() if e['kind']=='directory'}|{'.'}==set(m['directories']) and len(m['directories'])==17
    for n,e in m['files'].items():assert (ROOT/n).stat().st_size==e['size'] and sha(ROOT/n)==e['sha256']
    tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']}
    auth=read(ROOT/'private/source-authentication.json');source=auth['files'];assert len(source)==18 and auth['tree_entries']==13223 and auth['tree_sha256']==sha(tp) and auth['pin']=='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
    prefixes={'balanced':'preprints/Balanced-Counterexamples-to-Rysers-Conjecture-at-Prime-Orders-September-27-2026/','extension':'preprints/A-Counterexample-to-Rysers-Covering-Conjecture-September-23-2026/'}
    assert {e['canonical_path'] for e in source}=={p for p,e in entries.items() if any(p.startswith(x) for x in prefixes.values()) and e['type']=='blob' and not p.endswith('.pdf')}
    for e in source:
        data=(ROOT/e['local_path']).read_bytes();node=entries[e['canonical_path']]
        kind,prefix=next((k,p) for k,p in prefixes.items() if e['canonical_path'].startswith(p))
        assert e['local_path']=='private/source/'+kind+'/'+e['canonical_path'][len(prefix):] and len(data)==e['size']==node['size'] and sha(ROOT/e['local_path'])==e['sha256']
        assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob_sha1']==node['sha']
        assert e['url']=='https://raw.githubusercontent.com/openai/math/'+auth['pin']+'/'+e['canonical_path']
    recheck=read(ROOT/'private/source-recheck.json');assert recheck['canonical_nonpdf_files_matched']==18 and recheck['tree_entries']==13223 and recheck['tree_sha256']==sha(tp)
    primary=read(ROOT/'private/primary/receipts.json');assert len(primary)==4
    for e in primary:
        p=ROOT/'private/primary'/(e['name']+'.pdf');assert p.stat().st_size==e['pdf_size'] and sha(p)==e['pdf_sha256'] and sha(p.with_suffix('.txt'))==e['text_sha256']
        assert e['url']=='https://arxiv.org/pdf/'+e['version']
    originals=read(ROOT/'private/incoming-originals.json')['files'];assert len(originals)==13;stable=[]
    for e in originals:
        p=P/e['original_path'];assert p.stat().st_size==e['size'] and sha(p)==e['sha256'];stable.append({'path':e['original_path'],'sha256':e['sha256'],'bytes':e['size'],'limit':'Late current original identity only,not first-read/detached original-archive certification or fresh semantic reading.'})
    copies=read(ROOT/'private/history/selected-copy-membership.json')['files'];assert len(copies)==10
    for e in copies:
        p=ROOT/e['local_path'];assert p.read_bytes()==(P/e['original_path']).read_bytes() and p.stat().st_size==e['size'] and sha(p)==e['sha256']
    assert read(ROOT/'private/incoming-originals-recheck.json')['stable_late_observations_matched']==13
    ctl=read(ROOT/'private/controls/receipt.json');fixture=ROOT/'private/controls/fixture';fm=read(fixture/'MANIFEST.json')
    assert len(ctl['cases'])==8 and len(ctl['selected_original_identities'])==2 and set(fm['files'])==set(ctl['selected_original_identities'])
    for n,v in ctl['detached_fixture_anchors'].items():assert sha(fixture/n)==v
    for n,e in ctl['selected_original_identities'].items():assert (fixture/n).read_bytes()==(P/e['original_path']).read_bytes() and sha(fixture/n)==e['sha256']==fm['files'][n]['sha256']
    assert all((e['exit_code']==0)==e['expected_accept'] and e['read_only_snapshot_equal'] for e in ctl['cases'])
    cases=[]
    with tempfile.TemporaryDirectory(prefix='structural152-copy-',dir=O) as temp:
        copy=Path(temp)/'packet';shutil.copytree(ROOT,copy);args=[str(copy),'--final-sha256',ANCHORS['FINAL.md'],'--manifest-sha256',ANCHORS['MANIFEST.json'],'--report-sha256',ANCHORS['REPORT.md']]
        def check(label,want,custom=None):
            state=snap(copy);r=subprocess.run([sys.executable,'-I','-B',str(copy/'code/verify_packet.py'),*(custom or args)],capture_output=True,text=True,timeout=30)
            assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state
            cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
        check('baseline_full_packet',True)
        p=copy/'notes/02-integrated-reduction-and-gap.md';data=p.read_bytes();p.write_bytes(data+b'\nCONTROL\n');check('modified_payload',False);p.unlink();check('missing_payload',False);p.write_bytes(data)
        p=copy/'private/.extra';p.write_text('extra');check('extra_hidden_file',False);p.unlink();p=copy/'private/.empty';p.mkdir();check('extra_empty_directory',False);p.rmdir()
        wrong=args.copy();wrong[4]='0'*64;check('wrong_external_manifest_anchor',False,wrong)
        p=copy/'REPORT.md';data=p.read_bytes();p.write_bytes(data+b'CONTROL\n');check('changed_outside_REPORT',False);p.write_bytes(data);check('restored',True)
        state=snap(copy);d=subprocess.run([sys.executable,'-I','-B',str(copy/'code/design_diagnostic.py')],capture_output=True,text=True,timeout=60)
        assert d.returncode==0,(d.stdout,d.stderr);result=json.loads(d.stdout);assert result==read(ROOT/'private/design-diagnostic.json') and snap(copy)==state==before
        dump('diagnostic-replay.json',{'program_sha256':sha(ROOT/'code/design_diagnostic.py'),'result':result,'stderr':d.stderr,'disposable_full_copy_unchanged':True,'limits':'Existing bounded stdout-only finite diagnostic replay,no arbitrary-matroid or unconditional performance guarantee and no independent gate.'})
    assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in PROTECTED.items())
    dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':6,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Eight complete disposable-copy controls;child eight selected-copy controls remain separate.Artifact evidence only.'})
    dump('input-authentication.json',{'source_blobs':18,'primary_pdf_text_pairs':4,'byte_bound_render':1,'stable_originals':13,'selected_whole_history_copies':10,'selected_fixture_members':2,'limits':'Local canonical source/blob and retained-copy binding only,no fresh protected-body semantic/remote identity/visual reading or inherited original-archive certificate.'})
    dump('replay.json',{'observed_utc':now,'external_handoff_anchors':ANCHORS,'payload_files':62,'whole_root_files':65,'manifest_directories_including_dot':17,'source_blobs':18,'primary_pdf_text_pairs':4,'stable_named_originals':stable,'selected_history_copies':10,'artifact_cases':8,'negative_cases':6,'whole_actual_root_unchanged':True,'limits':'Artifact and existing bounded finite archive only,no full LR correctness/contribution grade.Verifier excludes modes,parent snapshot excludes rootmode.'})
    print(json.dumps({'files':65,'manifest_directories_including_dot':17,'sources':18,'primary_pairs':4,'stable_originals':13,'whole_copies':10,'cases':8,'finite_diagnostic_matched':True}))

if __name__=='__main__':main()
