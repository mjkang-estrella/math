#!/usr/bin/env python3
"""Completed arithmetic113 byte archive and bounded supporting diagnostic."""
import datetime,hashlib,importlib.util,json,shutil,subprocess,sys,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-arithmetic-discovery-r113';PK=ROOT/'packet'
spec=importlib.util.spec_from_file_location('archive_helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.json':'315b604532b3c26a223f5800707dc08d15d5e355cbf23d3b79eb56682fa3effd','MANIFEST.json':'3c0c8cd2d6adbc1d966f51a0f4abfdc3569b7b36f55f4ee8a3fd06d713754e8e','REPORT.md':'cff59eee041757b3d1527087445a96613e8a95508cf4033b1e53ba748cec47c6'}
PROTECTED={'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json':'6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9','frontier/iterations/i31-nonconical-no-mcm.md':'d606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
    now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=P)
    assert len(read(B/'tasks.json')['tasks'])==503
    dump('integration-baseline.json',{'observed_utc':now,'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip(),'initial_index_empty':True,'task_count':503,'task_index':499,'protected_unrelated_sha256':PROTECTED})
    before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current complete root snapshot excluding root-directory mode; no historical whole-project or OS certificate.'})
    st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and not st['hasPendingChildRuns'] and all(v in st['summary'] for v in ANCHORS.values())
    assert all(sha(ROOT/n)==v for n,v in ANCHORS.items())
    outer=read(ROOT/'MANIFEST.json');inner=read(PK/'MANIFEST.json');assert outer['kind']==inner['kind']=='original-r113'
    for n,e in outer['files'].items():assert (ROOT/n).stat().st_size==e['bytes'] and sha(ROOT/n)==e['sha256']
    assert set(outer['files'])=={'FINAL.json','REPORT.md','packet/MANIFEST.json'}
    assert len(inner['files'])==87 and len(inner['directories'])==20
    assert {p for p,e in before.items() if e['kind']=='file'}=={'packet/'+p for p in inner['files']}|{'FINAL.json','REPORT.md','MANIFEST.json','packet/MANIFEST.json'}
    assert {p for p,e in before.items() if e['kind']=='directory'}=={'packet'}|{'packet/'+p for p in inner['directories']}
    for n,e in inner['files'].items():assert (PK/n).stat().st_size==e['bytes'] and sha(PK/n)==e['sha256']
    tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'==sha(PK/'private/source/preprints-tree.json')
    tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']}
    source=read(PK/'private/source/authentication.json');assert len(source)==35
    for e in source:
        data=(PK/e['local']).read_bytes();node=entries[e['path']]
        assert e['local']=='private/source/'+e['path'] and len(data)==e['bytes']==node['size'] and sha(PK/e['local'])==e['sha256']
        assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']==node['sha']
        assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
    primary=read(PK/'private/primary/acquisition.json')+[read(PK/'private/primary/WieserYang-v2-acquisition.json')|{'name':'WieserYang-v2'}]
    for e in primary:
        p=PK/'private/primary'/(e['name']+'.pdf');assert p.stat().st_size==e['bytes'] and sha(p)==e['sha256'] and sha(p.with_suffix('.txt'))==e['text_sha256'] and e['extraction_returncode']==0 and e['stderr']==''
    history=read(PK/'private/history/authentication.json')['records'];assert len(history)==14
    stable=[];excerpt=[]
    for e in history:
        q=PK/e['copy'];assert q.stat().st_size==e['bytes'] and sha(q)==e['sha256']
        if 'kind' in e:excerpt.append({'path':e['original'],'retained_copy_sha256':sha(q),'old_whole_current_sha256':e['whole_current_sha256'],'limit':'Mutable journal retained excerpt only; old whole hash not a current stability input.'});continue
        p=P/e['original'];assert p.read_bytes()==q.read_bytes();stable.append({'path':e['original'],'sha256':sha(p),'bytes':p.stat().st_size,'limit':'Late current whole-original/copy check; no first-read/whole-incoming/history certificate or fresh semantic read.'})
    assert len(stable)==13 and len(excerpt)==1
    r2=read(PK/'notes/recovery-start.json')['historical_checkpoint_files'];r3=read(PK/'notes/recovery-r3-start.json')['files'];assert len(r2)==82 and len(r3)==83
    for n,e in list(r2.items())+list(r3.items()):assert (ROOT/n).stat().st_size==e['bytes'] and sha(ROOT/n)==e['sha256']
    early=read(B/'server-restart-2026-10-20-parent/fresh-arithmetic-discovery-r113-before.json')['snapshot'];early={p:e for p,e in early.items() if e['kind']=='file'}
    late=read(B/'server-restart-2026-10-20-parent/arithmetic113-before-r3.json')['entries'];late={p:e for p,e in late.items() if e['type']=='file'}
    assert set(early)==set(r2) and set(late)==set(r3)
    assert all(early[n]['sha256']==e['sha256'] and early[n]['bytes']==e['bytes'] for n,e in r2.items())
    assert all(late[n]['sha256']==e['sha256'] and late[n]['bytes']==e['bytes'] for n,e in r3.items())
    ctl=read(PK/'notes/control-receipt.json');fixture=PK/'private/control-fixture';assert len(ctl['cases'])==6
    for n,v in ctl['anchors'].items():assert sha(fixture/n)==v
    fm=read(fixture/'packet/MANIFEST.json');assert fm['kind']=='reduced-control'
    for n,e in fm['files'].items():assert (fixture/'packet'/n).stat().st_size==e['bytes'] and sha(fixture/'packet'/n)==e['sha256']
    cases=[]
    with tempfile.TemporaryDirectory(prefix='arithmetic113-copy-',dir=O) as temp:
        copy=Path(temp)/'packet';shutil.copytree(ROOT,copy)
        args=['--root',str(copy),'--final-sha',ANCHORS['FINAL.json'],'--manifest-sha',ANCHORS['MANIFEST.json'],'--report-sha',ANCHORS['REPORT.md']]
        def check(label,want,custom=None):
            state=snap(copy);r=subprocess.run([sys.executable,'-B',str(copy/'packet/tools/verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30)
            assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state
            cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
        check('baseline_full_packet',True)
        p=copy/'packet/notes/recovery-r3-derivation.md';data=p.read_bytes();p.write_bytes(data+b'\nCONTROL\n');check('modified_payload',False);p.unlink();check('missing_payload',False);p.write_bytes(data)
        p=copy/'packet/private/.extra';p.write_text('extra');check('extra_hidden_file',False);p.unlink()
        p=copy/'packet/private/.empty';p.mkdir();check('extra_empty_directory',False);p.rmdir()
        wrong=args.copy();wrong[5]='0'*64;check('wrong_external_manifest_anchor',False,wrong);check('restored',True);assert snap(copy)==before
        state=snap(copy);r=subprocess.run([sys.executable,'-B',str(copy/'packet/tools/finite_diagnostic.py')],capture_output=True,text=True,check=True,timeout=45);diag=json.loads(r.stdout)
        assert diag==read(PK/'notes/finite-diagnostic.json')==read(PK/'notes/recovery-r3-checks.json')['finite_diagnostic'] and snap(copy)==state
    assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in PROTECTED.items())
    dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':5,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Seven full disposable-copy controls; six old reduced-fixture tests remain historical. No mathematical gates.'})
    dump('diagnostic-replay.json',{'diagnostic':diag,'copied_root_unchanged':True,'limits':'Original bounded script on disposable complete copy only; six finite index cases,two finite trace distributions and exact rational margins. No uniform estimate or full proof validation.'})
    dump('input-authentication.json',{'source_blobs':35,'primary_pdf_text_pairs':3,'byte_bound_renders':2,'stable_whole_original_copies':13,'mutable_excerpt_copies':1,'historical_r2_files':82,'historical_r3_files':83,'parent_pre_recovery_inventories_match_author_baselines':True,'limits':'Local source/tree/blob and retained membership checks, not semantic or fresh network reads. Journal old whole hash not a current stability input.'})
    dump('replay.json',{'observed_utc':now,'external_handoff_anchors':ANCHORS,'payload_files':87,'whole_root_files':91,'directories':21,'source_blobs':35,'primary_pdf_text_pairs':3,'stable_named_originals':stable,'mutable_excerpt_copies':excerpt,'preserved_historical_r3_files':83,'preserved_historical_r2_files':82,'artifact_cases':7,'negative_cases':5,'whole_actual_root_unchanged':True,'limits':'Artifact and supporting finite diagnostic only. No correctness/contribution grade, universal estimate proof or fresh primary/source semantic read. Verifier binds directory membership,not modes; root mode excluded from parent snapshots.'})
    print(json.dumps({'files':91,'directories':21,'sources':35,'primary_pairs':3,'stable_originals':13,'historical_preserved':83,'cases':7,'diagnostic_reproduced':True}))
if __name__=='__main__':main()
