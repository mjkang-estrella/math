#!/usr/bin/env python3
"""Parent artifact authentication only; no mathematical gate."""
import datetime,gzip,hashlib,importlib.util,io,json,shutil,subprocess,sys,tarfile,tempfile
from pathlib import Path
OUT=Path(__file__).resolve().parent;BASE=OUT.parent;PROJECT=BASE.parents[2];ROOT=BASE/'fresh-analytic-discovery-r142'
spec=importlib.util.spec_from_file_location('archive_helpers',BASE/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');helper=importlib.util.module_from_spec(spec);spec.loader.exec_module(helper)
sha,snap=helper.sha,helper.snap
PROTECTED={'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json':'6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9','frontier/iterations/i31-nonconical-no-mcm.md':'d606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a'}
ANCHORS={'FINAL.md':'a1582238232ca4924af1848e318b8f1a39d1b885391d7852167b0ef44a68f9f9','MANIFEST.json':'2176ac6ca559a141aa103a9239f8a70aaf7d2e2bcca197f3ee4638bc795a8a1d','REPORT.md':'1eb1a16c756ee980b3256d00269eb1762de2aae2b9fcf35d883cec95f8c0cef1'}
def dump(n,d):(OUT/n).write_text(json.dumps(d,indent=2)+'\n')
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def part(b,a,z):
    lines=b.split(b'\n');return b'\n'.join(lines[a-1:z])+(b'\n' if z<len(lines) else b'')
def main():
    assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=PROJECT)
    assert all(sha(PROJECT/p)==h for p,h in PROTECTED.items())
    now=datetime.datetime.now(datetime.timezone.utc).isoformat()
    dump('integration-baseline.json',{'observed_utc':now,'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=PROJECT,text=True).strip(),'initial_index_empty':True,'task_count':496,'task_index':493,'protected_unrelated_sha256':PROTECTED})
    before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current whole actual root, not historical whole-parent or OS evidence.'})
    assert all(sha(ROOT/p)==h for p,h in ANCHORS.items())
    terminal=json.loads((OUT/'task-status.json').read_text())['structuredContent']
    assert terminal['status']=='completed' and all(h in terminal['summary'] for h in ANCHORS.values())
    m=json.loads((ROOT/'MANIFEST.json').read_text());assert m['schema']=='r142-exact-payload-v1'
    files={e['path']:e for e in m['files']};dirs=m['directories'];assert len(files)==61 and len(dirs)==13
    assert {p for p,e in before.items() if e['kind']=='file'}==set(files)|set(ANCHORS)
    assert {p for p,e in before.items() if e['kind']=='directory'}==set(dirs)
    assert all(e['kind'] in ['file','directory'] and (e['kind']!='file' or e['nlink']==1) for e in before.values())
    for p,e in files.items():assert sha(ROOT/p)==e['sha256'] and (ROOT/p).stat().st_size==e['size']
    tp=PROJECT/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree=json.loads(tp.read_text());assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']}
    assert (ROOT/'private/preprints-tree.json').read_bytes()==tp.read_bytes()
    sources=json.loads((ROOT/'source-authentication.json').read_text());assert len(sources)==12
    for e in sources:
        data=(ROOT/e['local']).read_bytes();node=entries[e['path']]
        assert len(data)==e['size']==node['size'] and sha(ROOT/e['local'])==e['sha256']
        assert blob(data)==e['gitblob']==node['sha']
        assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
    primary=json.loads((ROOT/'primary-authentication.json').read_text());assert len(primary)==3
    extracts=0
    for e in primary:
        raw=ROOT/e['raw'];data=raw.read_bytes();assert len(data)==e['size'] and sha(raw)==e['sha256'] and e['url']=='https://arxiv.org/src/'+e['version']
        if e['format']=='tar':
            with tarfile.open(fileobj=io.BytesIO(data),mode='r:*') as archive:
                for x in e['members']:assert archive.extractfile(x['name']).read()==(ROOT/x['local']).read_bytes()
        else:
            assert e['format']=='gzip-single' and len(e['members'])==1 and gzip.decompress(data)==(ROOT/e['members'][0]['local']).read_bytes()
        for x in e['members']:assert (ROOT/x['local']).stat().st_size==x['size'] and sha(ROOT/x['local'])==x['sha256'];extracts+=1
    assert extracts==5
    originals=json.loads((ROOT/'original-authentication.json').read_text());assert len(originals)==17
    byid={e['id']:e for e in originals};stable=[];mutable=[]
    for e in originals:
        p=PROJECT/e['path'];data=p.read_bytes()
        if e['path']=='frontier/NEW-TEN-2026-10-14.md':
            mutable.append({'path':e['path'],'snapshot_sha256':e['sha256'],'current_sha256':sha(p),'matches_snapshot_now':sha(p)==e['sha256'],'not_stability_input':True})
        else:
            assert len(data)==e['size'] and sha(p)==e['sha256'] and blob(data)==e['gitblob']
            stable.append({'path':e['path'],'sha256':e['sha256'],'size':e['size'],'limit':e['observation']})
    assert len(stable)==16 and len(mutable)==1
    copies=json.loads((ROOT/'selected-copy-membership.json').read_text());assert len(copies)==17
    whole=excerpt=0
    for e in copies:
        original=(PROJECT/byid[e['original_id']]['path']).read_bytes();data=(ROOT/e['local']).read_bytes()
        if e['selection']=='whole':expected=original;whole+=1
        else:expected=part(original,*e['lines']);excerpt+=1
        assert data==expected and len(data)==e['size'] and sha(ROOT/e['local'])==e['sha256'] and blob(data)==e['gitblob']
    assert (whole,excerpt)==(12,5)
    cases=[]
    with tempfile.TemporaryDirectory(prefix='analytic142-copy-',dir=OUT) as temp:
        copy=Path(temp)/'packet';shutil.copytree(ROOT,copy)
        args=[str(copy),'--final-sha',ANCHORS['FINAL.md'],'--manifest-sha',ANCHORS['MANIFEST.json'],'--report-sha',ANCHORS['REPORT.md']]
        def check(label,expected,custom=None):
            state=snap(copy);r=subprocess.run([sys.executable,'-B',str(copy/'verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30)
            assert (r.returncode==0)==expected,(label,r.stdout,r.stderr)
            assert snap(copy)==state
            cases.append({'case':label,'expected_pass':expected,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
        check('baseline_full_packet',True)
        p=copy/sources[0]['local'];data=p.read_bytes();p.write_bytes(data+b'\nCONTROL\n');check('modified_pinned_payload',False);p.write_bytes(data)
        p=copy/'DERIVATION.md';data=p.read_bytes();p.unlink();check('missing_payload',False);p.write_bytes(data)
        p=copy/'private/.extra';p.write_text('extra');check('extra_hidden_payload',False);p.unlink()
        wrong=args.copy();wrong[4]='0'*64;check('wrong_external_manifest_anchor',False,wrong);check('restored',True);assert snap(copy)==before
    assert snap(ROOT)==before and all(sha(PROJECT/e['path'])==e['sha256'] for e in stable)
    assert all(sha(PROJECT/p)==h for p,h in PROTECTED.items())
    dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':4,'copy_removed':True,'whole_actual_root_unchanged':True,'project_option_omitted':True,'limits':'Complete copied packet byte/membership controls only. External originals checked separately with mutable journal separated; no mathematical gates.'})
    dump('input-authentication.json',{'source_blobs':12,'complete_canonical_tree_bound_independently':True,'primary_raw_versions':3,'matching_selected_extracts':5,'original_observations':originals,'stable_named_originals':stable,'mutable_context':mutable,'selected_copy_members':copies,'whole_copies':12,'excerpt_copies':5,'limits':'Current originals and selected copies checked separately. Mutable journal is not a stability input. No fresh source/primary/history semantic reading, first-read, whole incoming packet or historical whole-parent certificate.'})
    dump('replay.json',{'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'external_handoff_anchors':ANCHORS,'verifier_sha256':sha(ROOT/'verify.py'),'payload_files':61,'whole_root_files':64,'directories':13,'source_blobs':12,'primary_raw_versions':3,'matching_selected_extracts':5,'stable_named_originals':stable,'mutable_context':mutable,'selected_copy_members':17,'whole_copies':12,'excerpt_copies':5,'artifact_cases':6,'negative_cases':4,'whole_actual_root_unchanged':True,'stable_originals_unchanged':True,'limits':'Artifact bytes only; no independent verification of the supporting analytic construction, frozen theorem/nominee, correctness/contribution grade, fresh semantic primary/history read or historical whole-parent/OS certificate.'})
    print(json.dumps({'payloads':61,'whole_files':64,'directories':13,'source_blobs':12,'primary_raw_versions':3,'selected_extracts':5,'stable_originals':16,'mutable_journal':1,'whole_copies':12,'excerpt_copies':5,'artifact_cases':6,'negative_cases':4,'whole_root_unchanged':True}))
if __name__=='__main__':main()
