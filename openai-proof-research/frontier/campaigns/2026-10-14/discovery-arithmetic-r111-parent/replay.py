#!/usr/bin/env python3
"""Parent archive authentication, not a mathematical or contribution gate."""
import datetime,hashlib,importlib.util,json,shutil,subprocess,sys,tempfile
from pathlib import Path
OUT=Path(__file__).resolve().parent;BASE=OUT.parent;PROJECT=BASE.parents[2];ROOT=BASE/'fresh-arithmetic-discovery-r111';PACKET=ROOT/'packet'
spec=importlib.util.spec_from_file_location('archive_helpers',BASE/'discovery-analytic-r139-parent/replay.py');helper=importlib.util.module_from_spec(spec);spec.loader.exec_module(helper)
sha,snap,PROTECTED=helper.sha,helper.snap,helper.PROTECTED
ANCHORS={'FINAL.json':'5b16bd2582f59b008876ad90bd3dcc9a7063843589035126a5a2be767e69290a','MANIFEST.json':'c7b4cf49a2e0ad29c23b40b20df57b364bf429fd810568ec0a53dfe2c102b365','REPORT.md':'a3fce5f511add7b933c8fed01a5fe83a37228f991e3def3e4373292b5f8cb20c'}
def dump(n,d):(OUT/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
    assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=PROJECT)
    assert all(sha(PROJECT/p)==h for p,h in PROTECTED.items())
    now=datetime.datetime.now(datetime.timezone.utc).isoformat()
    dump('integration-baseline.json',{'observed_utc':now,'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=PROJECT,text=True).strip(),'initial_index_empty':True,'task_count':490,'task_index':487,'protected_unrelated_sha256':PROTECTED})
    before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current whole root only, not historical whole-parent or OS evidence.'})
    assert all(sha(ROOT/p)==h for p,h in ANCHORS.items())
    outer=json.loads((ROOT/'MANIFEST.json').read_text());final=json.loads((ROOT/'FINAL.json').read_text())
    assert outer['schema']=='r111-outside-v1' and final['status']=='PREFREEZE/no nominee' and not final['statement_frozen']
    assert sha(PACKET/'manifest.json')==outer['packet_manifest_sha256']==final['packet_manifest_sha256']=='b33ea767a859187bcc74109edeba9febc0e74faf423feadec0f8b18099ead130'
    assert final['manifest_sha256']==ANCHORS['MANIFEST.json'] and final['report_sha256']==outer['report_sha256']==ANCHORS['REPORT.md']
    m=json.loads((PACKET/'manifest.json').read_text());assert m['schema']=='r111-payload-v1' and len(m['files'])==78 and len(m['directories'])==20
    assert {p for p,e in before.items() if e['kind']=='file'}=={'packet/'+e['path'] for e in m['files']}|{'packet/manifest.json'}|set(ANCHORS)
    assert {p for p,e in before.items() if e['kind']=='directory'}=={'packet/'+p for p in m['directories']}|{'packet'}
    for e in m['files']:assert sha(PACKET/e['path'])==e['sha256'] and (PACKET/e['path']).stat().st_size==e['size']
    tp=PROJECT/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'==sha(PACKET/'private/context/preprints-tree.json')
    tree=json.loads(tp.read_text());assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']}
    sources=json.loads((PACKET/'private/source/metadata.json').read_text());assert len(sources)==25
    for e in sources:
        p=PACKET/'private/source'/e['path'];data=p.read_bytes();node=entries[e['path']]
        assert len(data)==e['size']==node['size'] and sha(p)==e['sha256']
        assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']==node['sha']
        assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
    primary=json.loads((PACKET/'private/primary/metadata.json').read_text());assert len(primary)==2
    for e,name in zip(primary,['EEL2020','Pauli-Roblot2001'],strict=True):
        p=PACKET/'private/primary'/name
        assert sha(p.with_suffix('.pdf'))==e['sha256'] and p.with_suffix('.pdf').stat().st_size==e['size']
        assert sha(p.with_suffix('.txt'))==e['text_sha256'] and e['extraction_exit']==0
    history=json.loads((PACKET/'private/history/metadata.json').read_text());assert len(history)==17
    stable=[];mutable=[]
    for e in history:
        assert sha(PACKET/e['snapshot'])==e.get('snapshot_sha256',e['sha256'])
        data=(PROJECT/e['path']).read_bytes()
        if e.get('snapshot_is_excerpt'):
            excerpt=data[data.index(b'## Acceptance and publication'):data.index(b'## Model allocation')]
            assert hashlib.sha256(excerpt).hexdigest()==e['snapshot_sha256']
            assert (PACKET/e['snapshot']).read_bytes()==excerpt
            mutable.append({'path':e['path'],'late_whole_sha256':e['sha256'],'current_whole_sha256':sha(PROJECT/e['path']),'excerpt_matches_current':True,'whole_file_not_stability_input':True})
        else:assert len(data)==e['size'] and sha(PROJECT/e['path'])==e['sha256'];stable.append(e)
    assert len(stable)==16 and len(mutable)==1
    cases=[]
    with tempfile.TemporaryDirectory(prefix='arithmetic111-copy-',dir=OUT) as temp:
        copy=Path(temp)/'packet-root';shutil.copytree(ROOT,copy)
        args=['--root',str(copy),'--final-sha256',ANCHORS['FINAL.json'],'--manifest-sha256',ANCHORS['MANIFEST.json'],'--report-sha256',ANCHORS['REPORT.md'],'--originals',str(PROJECT)]
        def check(label,expected,custom=None):
            state=snap(copy);r=subprocess.run([sys.executable,'-B',str(copy/'packet/scripts/verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30)
            assert (r.returncode==0)==expected,(label,r.stdout,r.stderr)
            assert snap(copy)==state
            cases.append({'case':label,'expected_pass':expected,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
            if expected:
                d=json.loads(r.stdout)['checks'];assert d['source_blobs']==25 and d['primary_pairs']==2 and d['current_named_original_checks']==17 and d['finite_diagnostics']=='replayed'
        check('baseline_complete_packet_and_current_originals',True)
        p=copy/'packet/notes/donovan-feasibility.md';data=p.read_bytes();p.write_bytes(data+b'\nCONTROL\n');check('modified_payload',False);p.unlink();check('missing_payload',False);p.write_bytes(data)
        p=copy/'packet/private/.extra';p.write_text('extra');check('extra_hidden_payload',False);p.unlink()
        wrong=args.copy();wrong[3]='0'*64;check('wrong_external_final_anchor',False,wrong);check('restored',True);assert snap(copy)==before
    assert snap(ROOT)==before and all(sha(PROJECT/e['path'])==e['sha256'] for e in stable)
    assert all(sha(PROJECT/p)==h for p,h in PROTECTED.items())
    dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':4,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Complete copied-packet controls; checker also replays only read-only bounded diagnostics and17explicit original comparisons. No mathematical gate.'})
    dump('diagnostic-replay.json',json.loads((PACKET/'notes/diagnostics.json').read_text()))
    dump('input-authentication.json',{'source_blobs':25,'primary_pairs':primary,'stable_named_originals':stable,'mutable_context':mutable,'limits':'Current selected bytes plus acceptance excerpt, not fresh semantic primary/source/history reading or full-journal stability.'})
    dump('replay.json',{'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'external_handoff_anchors':ANCHORS,'packet_manifest_sha256':sha(PACKET/'manifest.json'),'verifier_sha256':sha(PACKET/'scripts/verify.py'),'payload_files':78,'whole_root_files':82,'whole_root_directories':21,'source_blobs':25,'primary_pdf_text_pairs':2,'stable_named_originals':stable,'mutable_context':mutable,'current_named_original_checks':17,'artifact_cases':6,'negative_cases':4,'finite_order_cases':5,'f4_unit_group_order':48,'f4_sylow_order':16,'whole_actual_root_unchanged':True,'stable_originals_unchanged':True,'limits':'Artifact and bounded diagnostics only; no effective exact group-block algorithm, independent mathematical/contribution gate, fresh full-primary/history reading or historical whole-parent/OS certificate.'})
    print(json.dumps({'payloads':78,'whole_files':82,'source_blobs':25,'primary_pairs':2,'stable_originals':16,'mutable_excerpt':1,'artifact_cases':6,'negative_cases':4,'finite_order_cases':5,'unit_group_order':48,'whole_root_unchanged':True}))
if __name__=='__main__':main()
