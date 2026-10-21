#!/usr/bin/env python3
"""Parent byte authentication and bounded finite replay; no mathematical gate."""
import datetime,hashlib,importlib.util,json,shutil,subprocess,sys,tempfile
from pathlib import Path
OUT=Path(__file__).resolve().parent;BASE=OUT.parent;PROJECT=BASE.parents[2];ROOT=BASE/'fresh-arithmetic-discovery-r112';PACKET=ROOT/'packet'
spec=importlib.util.spec_from_file_location('archive_helpers',BASE/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');helper=importlib.util.module_from_spec(spec);spec.loader.exec_module(helper)
sha,snap=helper.sha,helper.snap
PROTECTED={'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json':'6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9','frontier/iterations/i31-nonconical-no-mcm.md':'d606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a'}
ANCHORS={'FINAL.json':'de8bdc89dbf9c82cbfc19f18d14fb68d3278c568f80a8d84b5855d95c27e9371','MANIFEST.json':'51e40ec7e90a662e7f35be0bfd523feb5670edf903b53fb2e010c0db1fdaaf65','REPORT.md':'b82cd02ee282e58e8a4cb30dc8a278ae199ac1a59d250b75c3e18969982f329b'}
def dump(n,d):(OUT/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
    assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=PROJECT)
    assert all(sha(PROJECT/p)==h for p,h in PROTECTED.items())
    now=datetime.datetime.now(datetime.timezone.utc).isoformat()
    dump('integration-baseline.json',{'observed_utc':now,'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=PROJECT,text=True).strip(),'initial_index_empty':True,'task_count':495,'task_index':490,'protected_unrelated_sha256':PROTECTED})
    before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current whole actual root, not historical whole-parent or OS evidence.'})
    assert all(sha(ROOT/p)==h for p,h in ANCHORS.items())
    terminal=json.loads((OUT/'task-status.json').read_text())['structuredContent']
    assert terminal['status']=='completed' and all(h in terminal['summary'] for h in ANCHORS.values())
    outer=json.loads((ROOT/'MANIFEST.json').read_text());assert outer['schema']=='r112-outside-v1'
    for p,e in outer['bound'].items():assert sha(ROOT/p)==e['sha256'] and (ROOT/p).stat().st_size==e['size']
    m=json.loads((PACKET/'MANIFEST.json').read_text());assert m['schema']=='r112-payload-v1'
    files={e['path']:e for e in m['files']};dirs=m['directories'];assert len(files)==108 and len(dirs)==30
    assert {p for p,e in before.items() if e['kind']=='file'}=={'packet/'+p for p in files}|{'packet/MANIFEST.json'}|set(ANCHORS)
    assert {p for p,e in before.items() if e['kind']=='directory'}=={'packet'}|{'packet/'+p for p in dirs}
    assert all(e['kind'] in ['file','directory'] and (e['kind']!='file' or e['nlink']==1) for e in before.values())
    for p,e in files.items():assert sha(PACKET/p)==e['sha256'] and (PACKET/p).stat().st_size==e['size']
    tp=PROJECT/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree=json.loads(tp.read_text());assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']}
    assert (PACKET/'private/context/2-preprints-tree.json').read_bytes()==tp.read_bytes()
    sources=json.loads((PACKET/'private/source/metadata.json').read_text());assert len(sources)==42
    for e in sources:
        data=(PACKET/e['local']).read_bytes();node=entries[e['path']]
        assert len(data)==e['size']==node['size'] and sha(PACKET/e['local'])==e['sha256']
        assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']==node['sha']
        assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
    primary=[]
    for name in ['CM2011','Dumnicki2007','CM1998v1','DJ2005v1','Dumnicki2005v1','FujinoKV']:
        e=json.loads((PACKET/'private/primary'/(name+'.json')).read_text())
        pdf=PACKET/'private/primary'/(name+'.pdf');txt=pdf.with_suffix('.txt')
        assert sha(pdf)==e['pdf_sha256'] and pdf.stat().st_size==e['pdf_size'] and sha(txt)==e['text_sha256'] and e['extraction_returncode']==0
        primary.append({'name':name,**e})
    originals=json.loads((PACKET/'private/context/original-snapshots.json').read_text())['records'];assert len(originals)==13
    stable=[];mutable=[]
    for e in originals:
        p=PROJECT/e['original'];q=PACKET/e['copy'];assert sha(q)==e['copy_sha256']
        if e['original']=='frontier/NEW-TEN-2026-10-14.md':
            assert q.stat().st_size==e['copy_size'] and q.read_bytes() in p.read_bytes()
            mutable.append({'path':e['original'],'snapshot_sha256':e['original_sha256'],'current_sha256':sha(p),'matches_snapshot_now':sha(p)==e['original_sha256'],'excerpt_sha256':e['copy_sha256'],'excerpt_still_present':True,'not_stability_input':True})
        else:
            assert p.read_bytes()==q.read_bytes() and sha(p)==e['sha256'] and p.stat().st_size==e['size']
            stable.append({'path':e['original'],'sha256':e['sha256'],'size':e['size'],'limit':'Current named whole-file identity, not historical whole incoming packet or first-read authentication.'})
    assert len(stable)==12 and len(mutable)==1
    cases=[]
    with tempfile.TemporaryDirectory(prefix='arithmetic112-copy-',dir=OUT) as temp:
        copy=Path(temp)/'packet-root';shutil.copytree(ROOT,copy)
        args=['--root',str(copy),'--final-sha',ANCHORS['FINAL.json'],'--manifest-sha',ANCHORS['MANIFEST.json'],'--report-sha',ANCHORS['REPORT.md']]
        def check(label,expected,custom=None):
            state=snap(copy);r=subprocess.run([sys.executable,'-B',str(copy/'packet/verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30)
            assert (r.returncode==0)==expected,(label,r.stdout,r.stderr)
            assert snap(copy)==state
            cases.append({'case':label,'expected_pass':expected,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
        check('baseline_full_packet',True)
        p=copy/'packet'/sources[0]['local'];data=p.read_bytes();p.write_bytes(data+b'\nCONTROL\n');check('modified_pinned_payload',False);p.write_bytes(data)
        p=copy/'packet/notes/feasibility.md';data=p.read_bytes();p.unlink();check('missing_payload',False);p.write_bytes(data)
        p=copy/'packet/private/.extra';p.write_text('extra');check('extra_hidden_payload',False);p.unlink()
        wrong=args.copy();wrong[5]='0'*64;check('wrong_external_manifest_anchor',False,wrong);check('restored',True);assert snap(copy)==before
        state=snap(copy);result=subprocess.run([sys.executable,'-B',str(copy/'packet/code/check_diagnostics.py')],capture_output=True,text=True,check=True,timeout=45)
        diagnostic=json.loads(result.stdout);assert diagnostic==json.loads((PACKET/'scratch/finite-replay.json').read_text()) and snap(copy)==state
        assert diagnostic['line_certificates']==18 and diagnostic['exact_rank_defect']==22 and diagnostic['repaired_rank']==24
    assert snap(ROOT)==before and all(sha(PROJECT/e['path'])==e['sha256'] for e in stable)
    assert all(sha(PROJECT/p)==h for p,h in PROTECTED.items())
    dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':4,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Complete copied packet byte/membership controls only; no mathematical gates.'})
    dump('diagnostic-replay.json',{'actual_copied_read_only_replay':diagnostic,'copied_root_unchanged_after_diagnostic':True,'nine_initial_modular_matrix_cases_rechecked':True,'line_certificates_checked':18,'rank_Q':22,'compatible_repaired_rank':24,'row_profile_records':5353,'row_profiles_checked_only_for_record_count':True,'pell_greedy_trials_not_rerun':True,'limits':'Bounded supporting replay only; no unbounded interpolation theorem, full row-profile census validation, proof/contribution gate or new grade.'})
    dump('input-authentication.json',{'source_blobs':42,'complete_canonical_tree_bound_independently':True,'primary_pdf_text_pairs':primary,'selected_copy_records':originals,'stable_named_originals':stable,'mutable_context':mutable,'limits':'Current named original/copy identities separately checked, plus a mutable acceptance excerpt. Acquisition/extraction does not establish faithful glyphs or semantic primary/history reading. No first-read, whole incoming packet or historical whole-parent certificate.'})
    dump('replay.json',{'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'external_handoff_anchors':ANCHORS,'inner_payload_manifest_sha256':sha(PACKET/'MANIFEST.json'),'verifier_sha256':sha(PACKET/'verify.py'),'payload_files':108,'whole_root_files':112,'whole_root_directories':31,'source_blobs':42,'primary_pdf_text_pairs':6,'stable_named_originals':stable,'mutable_context':mutable,'selected_whole_copies':12,'mutable_excerpt':1,'artifact_cases':6,'negative_cases':4,'line_certificates':18,'rank_Q':22,'compatible_repaired_rank':24,'whole_actual_root_unchanged':True,'stable_originals_unchanged':True,'limits':'Artifact bytes and bounded supporting diagnostics only; no frozen theorem/nominee, mathematical/contribution grade, fresh semantic primary/history reading or historical whole-parent/OS certificate.'})
    print(json.dumps({'payloads':108,'whole_files':112,'whole_directories':31,'source_blobs':42,'primary_pairs':6,'stable_originals_and_whole_copies':12,'mutable_excerpt':1,'artifact_cases':6,'negative_cases':4,'line_certificates':18,'rank_Q':22,'repaired_rank':24,'whole_root_unchanged':True}))
if __name__=='__main__':main()
