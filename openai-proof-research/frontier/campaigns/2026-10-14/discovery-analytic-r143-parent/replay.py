#!/usr/bin/env python3
"""Read-only completed-root archive and proportionate disposable-copy controls."""
import datetime, hashlib, importlib.util, json, shutil, subprocess, sys, tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-analytic-discovery-r143'
spec=importlib.util.spec_from_file_location('archive_helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'b4c67687f1c285e6f150ab5ee08b67642131e536500df9b3f3f636c083c7c68a','MANIFEST.json':'117cd523080e4a8ed9d035d5bc63363c6beb3bf169a7c1f168c464788fd51e4f','REPORT.md':'16caf2627b41770b09f1745b12fce685a667dd18acf8c27922dd96d905431bdc'}
PROTECTED={'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json':'6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9','frontier/iterations/i31-nonconical-no-mcm.md':'d606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
    now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=P)
    t=read(B/'tasks.json');assert len(t['tasks'])==502
    dump('integration-baseline.json',{'observed_utc':now,'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip(),'initial_index_empty':True,'task_count':502,'task_index':500,'protected_unrelated_sha256':PROTECTED})
    before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current whole root snapshot; root-directory mode excluded by reused helper. Not OS or historical whole-project evidence.'})
    st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and not st['hasPendingChildRuns'] and all(v in st['summary'] for v in ANCHORS.values())
    assert all(sha(ROOT/p)==v for p,v in ANCHORS.items())
    m=read(ROOT/'MANIFEST.json');assert m['format']=='r143-exact-payload-v1' and m['outside_envelopes']==sorted(ANCHORS)
    rows=m['files'];assert len(rows)==47 and len({e['path'] for e in rows})==47
    assert {p for p,e in before.items() if e['kind']=='file'}=={e['path'] for e in rows}|set(ANCHORS)
    for e in rows:assert (ROOT/e['path']).stat().st_size==e['size'] and sha(ROOT/e['path'])==e['sha256']
    assert all(e['kind'] in ['file','directory'] and (e['kind']!='file' or e['nlink']==1) for e in before.values())
    tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']}
    source=read(ROOT/'source-authentication.json');assert len(source)==13
    for e in source:
        data=(ROOT/e['local']).read_bytes();node=entries[e['path']]
        assert len(data)==e['size']==node['size'] and sha(ROOT/e['local'])==e['sha256']
        assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['gitblob']==node['sha']
        assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
    primary=read(ROOT/'primary-authentication.json');raw=members=0
    for e in primary:
        assert e['url']=='https://arxiv.org/src/'+e['id']
        if 'failure' in e:assert e['id']=='2006.15328v2' and '404' in e['failure'];continue
        p=ROOT/'private/primary'/e['id']/'raw';assert p.stat().st_size==e['size'] and sha(p)==e['sha256'];raw+=1
        for row in e['members']:assert (ROOT/row['path']).stat().st_size==row['size'] and sha(ROOT/row['path'])==row['sha256'];members+=1
    assert (raw,members)==(5,5)
    auth=read(ROOT/'R3-AUTHENTICATION.json');assert auth['tree_sha256']==sha(tp) and auth['tree_entry_count']==13223
    assert len(auth['source'])==13 and len(auth['primary_bytes_match_saved_ledger'])==10
    for e in auth['source']:
        assert (ROOT/e['path']).stat().st_size==e['size'] and sha(ROOT/e['path'])==e['sha256'] and entries[e['canonical']]['sha']==e['gitblob']
    for e in auth['primary_bytes_match_saved_ledger']:assert (ROOT/e['path']).stat().st_size==e['size'] and sha(ROOT/e['path'])==e['sha256']
    r2=read(ROOT/'RECOVERY-BASELINE.json');r3=read(ROOT/'R3-BASELINE.json');assert len(r2)==31 and len(r3)==33
    for e in r2+r3:assert (ROOT/e['path']).stat().st_size==e['size'] and sha(ROOT/e['path'])==e['sha256']
    stopped=read(B/'server-restart-2026-10-20-parent/analytic143-before-r3.json')['entries'];stopped_files={p:e for p,e in stopped.items() if e['type']=='file'}
    assert set(stopped_files)=={e['path'] for e in r3}
    assert all(stopped_files[e['path']]['sha256']==e['sha256'] and stopped_files[e['path']]['bytes']==e['size'] for e in r3)
    earlier=read(B/'server-restart-2026-10-20-parent/fresh-analytic-discovery-r143-before.json')['snapshot'];earlier_files={p:e for p,e in earlier.items() if e['kind']=='file'}
    assert set(earlier_files)=={e['path'] for e in r2} and all(earlier_files[e['path']]['sha256']==e['sha256'] and earlier_files[e['path']]['bytes']==e['size'] for e in r2)
    fixtures=ROOT/'scratch/control-fixture';fm=read(fixtures/'MANIFEST.json');assert len(fm['files'])==1
    f=fm['files'][0];assert f['path']=='selected-original-prose.md' and (fixtures/f['path']).read_bytes()==(ROOT/'DERIVATION-R3.md').read_bytes()
    historical=read(ROOT/'scratch/control-results.json');assert len(historical['controls'])==7
    assert all((e['exit_code']==0)==e['expected_accept'] for e in historical['controls'])
    for p,v in historical['fixture_anchors'].items():assert sha(fixtures/p)==v
    cases=[]
    with tempfile.TemporaryDirectory(prefix='analytic143-copy-',dir=O) as temp:
        copy=Path(temp)/'packet';shutil.copytree(ROOT,copy)
        args=[str(copy),'--final-sha256',ANCHORS['FINAL.md'],'--manifest-sha256',ANCHORS['MANIFEST.json'],'--report-sha256',ANCHORS['REPORT.md']]
        def check(label,want,custom=None):
            state=snap(copy);r=subprocess.run([sys.executable,'-B',str(copy/'verify.py'),*(custom or args)],text=True,capture_output=True,timeout=30)
            assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state
            cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
        check('baseline_full_packet',True)
        p=copy/'DERIVATION-R3.md';data=p.read_bytes();p.write_bytes(data+b'\nCONTROL\n');check('changed_payload',False);p.unlink();check('missing_payload',False);p.write_bytes(data)
        p=copy/'private/.extra';p.write_text('extra');check('extra_hidden_file',False);p.unlink()
        wrong=args.copy();wrong[4]='0'*64;check('wrong_external_manifest_anchor',False,wrong);check('restored',True)
        assert snap(copy)==before
    assert snap(ROOT)==before and all(sha(P/p)==v for p,v in PROTECTED.items())
    dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':4,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Six complete disposable-copy controls; original seven selected-copy controls remain historical. No mathematical gate.'})
    dump('input-authentication.json',{'source_blobs':13,'primary_raw_versions':5,'primary_selected_members':5,'failed_primary_request':'2006.15328v2 HTTP404','historical_r2_files':31,'historical_r3_files':33,'parent_pre_recovery_inventories_match_author_baselines':True,'limits':'Local tree/blob/byte/selection checks, no fresh network or semantic reads, no external-original-copy claim.'})
    dump('replay.json',{'observed_utc':now,'external_handoff_anchors':ANCHORS,'payload_files':47,'whole_root_files':50,'directories':sum(e['kind']=='directory' for e in before.values()),'source_blobs':13,'primary_raw_versions':5,'primary_selected_members':5,'preserved_historical_r3_files':33,'preserved_historical_r2_files':31,'artifact_cases':6,'negative_cases':4,'whole_actual_root_unchanged':True,'limits':'Artifact archive only. Verifier authenticates files, not directory modes/empty directories/hardlink policy. Parent snapshots check current modes/nlink; no new math/contribution grade or fresh source/primary semantic clearance.'})
    print(json.dumps(read(O/'replay.json')))
if __name__=='__main__':main()
