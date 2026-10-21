#!/usr/bin/env python3
"""Parent artifact and bounded exact-diagnostic replay; no mathematical gate."""
import datetime,hashlib,importlib.util,json,shutil,stat,subprocess,sys,tempfile
from fractions import Fraction as F
from pathlib import Path
OUT=Path(__file__).resolve().parent;BASE=OUT.parent;PROJECT=BASE.parents[2];ROOT=BASE/'fresh-structural-discovery-r148'
spec=importlib.util.spec_from_file_location('archive_helpers',BASE/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');helper=importlib.util.module_from_spec(spec);spec.loader.exec_module(helper)
sha=helper.sha
def snap(root):
    result=helper.snap(root);result['.']={'kind':'directory','mode':stat.S_IMODE(root.lstat().st_mode)};return result
PROTECTED={'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json':'6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9','frontier/iterations/i31-nonconical-no-mcm.md':'d606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a'}
ANCHORS={'FINAL.md':'50a726bd0300442d3e218bc19d2c4c0269a193483dca65f55e109618ccb2d793','MANIFEST.json':'a65e9542eb981e87746231a538a3e0e31182272997483c29dde0544f7c3c16cf','REPORT.md':'86775602df74ed07dc0eddbb839616c67cdb0bba3468b75be3174c1ff59f4933'}
def dump(n,d):(OUT/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
    assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=PROJECT)
    assert all(sha(PROJECT/p)==h for p,h in PROTECTED.items())
    now=datetime.datetime.now(datetime.timezone.utc).isoformat()
    dump('integration-baseline.json',{'observed_utc':now,'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=PROJECT,text=True).strip(),'initial_index_empty':True,'task_count':497,'task_index':494,'protected_unrelated_sha256':PROTECTED})
    before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current whole actual root including root-directory mode, not historical whole-parent or OS evidence.'})
    assert all(sha(ROOT/p)==h for p,h in ANCHORS.items())
    terminal=json.loads((OUT/'task-status.json').read_text())['structuredContent']
    assert terminal['status']=='completed' and all(h in terminal['summary'] for h in ANCHORS.values())
    m=json.loads((ROOT/'MANIFEST.json').read_text());assert m['schema']=='r148-exact-payload-v1'
    files=m['files'];dirs=m['directories'];assert len(files)==65 and len(dirs)==27
    assert {p for p,e in before.items() if e['kind']=='file'}==set(files)|set(ANCHORS)
    assert {p for p,e in before.items() if e['kind']=='directory'}==set(dirs)
    assert all(e['kind'] in ['file','directory'] and (e['kind']!='file' or e['nlink']==1) for e in before.values())
    assert all(before[p]['mode']==mode for p,mode in dirs.items())
    for p,e in files.items():assert sha(ROOT/p)==e['sha256'] and (ROOT/p).stat().st_size==e['bytes'] and before[p]['mode']==e['mode']
    tp=PROJECT/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree=json.loads(tp.read_text());assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']}
    sources=json.loads((ROOT/'private/source/receipts.json').read_text());assert len(sources)==14
    for e in sources:
        data=(ROOT/e['local']).read_bytes();node=entries[e['path']]
        assert len(data)==e['size']==node['size'] and sha(ROOT/e['local'])==e['sha256']
        assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']==node['sha']
        assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
    primary=json.loads((ROOT/'private/primary/receipts.json').read_text());assert len(primary)==6
    success=failed=0
    for e in primary:
        if 'error' in e:assert e['name']=='hatami-v3' and '404' in e['error'];failed+=1;continue
        p=ROOT/'private/primary'/(e['name']+'.pdf')
        assert sha(p)==e['sha256'] and p.stat().st_size==e['bytes'] and e['url'].startswith('https://arxiv.org/pdf/')
        assert p.with_suffix('.txt').relative_to(ROOT).as_posix() in files and e['extract_returncode']==0 and e['extract_stderr']=='';success+=1
    assert (success,failed)==(5,1)
    copies=json.loads((ROOT/'private/history/selected-original-receipts.json').read_text());assert len(copies)==10
    stable=[]
    for e in copies:
        p=PROJECT/e['original_path'];q=ROOT/e['copy']
        assert p.read_bytes()==q.read_bytes() and sha(p)==e['original_sha256']==sha(q)==e['copy_sha256_independent_sha256sum'] and p.stat().st_size==e['original_bytes']
        stable.append({'path':e['original_path'],'sha256':e['original_sha256'],'size':e['original_bytes'],'read_extent':e['read_extent'],'limit':e['authentication']})
    cases=[]
    with tempfile.TemporaryDirectory(prefix='structural148-copy-',dir=OUT) as temp:
        copy=Path(temp)/'packet';shutil.copytree(ROOT,copy)
        args=[str(copy),'--final',ANCHORS['FINAL.md'],'--manifest',ANCHORS['MANIFEST.json'],'--report',ANCHORS['REPORT.md']]
        def check(label,expected,custom=None):
            state=snap(copy);r=subprocess.run([sys.executable,'-B',str(copy/'code/verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30)
            assert (r.returncode==0)==expected,(label,r.stdout,r.stderr)
            assert snap(copy)==state
            cases.append({'case':label,'expected_pass':expected,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
        check('baseline_full_packet',True)
        p=copy/'notes/01-prefreeze-calculations.md';data=p.read_bytes();p.write_bytes(data+b'\nCONTROL\n');check('modified_payload',False);p.unlink();check('missing_payload',False);p.write_bytes(data)
        p=copy/'private/.extra';p.write_text('extra');check('extra_hidden_payload',False);p.unlink()
        p=copy/'private/.extra-empty';p.mkdir();check('extra_empty_directory',False);p.rmdir()
        wrong=args.copy();wrong[4]='0'*64;check('wrong_external_manifest_anchor',False,wrong);check('restored',True);assert snap(copy)==before
        state=snap(copy);r=subprocess.run([sys.executable,'-B',str(copy/'code/diagnostic.py')],capture_output=True,text=True,check=True,timeout=45)
        diagnostic=json.loads(r.stdout);assert diagnostic==json.loads((ROOT/'notes/diagnostic-results.json').read_text()) and snap(copy)==state
        assert diagnostic['moment_entry_checks']==32258 and diagnostic['torus']['points']==16
    spin={int(k):v for k,v in diagnostic['tetrahedral_collapsed']['spin_cut_counts'].items()}
    assert sum(spin.values())==64 and all(k%2==0 for k in spin)
    assert F(63)+F(32,2**12)*sum(v*F(1,2)**k for k,v in spin.items())==F(1032617,16384)
    for e in diagnostic['finite_rank_checks']:
        q=e['q'];p=F(q*q-1,2*q**3)
        assert str(p)==e['mass'] and F(1,q**45)*p**-64==F(e['torus_exact_collapse_lower_bound'])
    assert snap(ROOT)==before and all(sha(PROJECT/e['path'])==e['sha256'] for e in stable)
    assert all(sha(PROJECT/p)==h for p,h in PROTECTED.items())
    dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':5,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Complete copied packet byte/mode/membership controls including root mode only; no mathematical gates.'})
    dump('diagnostic-replay.json',{'actual_copied_script_result':diagnostic,'copied_root_unchanged_after_diagnostic':True,'independent_tetrahedral_cut_sum_checked':True,'independent_six_finite_rank_event_formulas_checked':True,'limits':'Bounded exact supporting diagnostics only; not all type maps, full torus density, global sign optimization or independent proof/contribution review.'})
    dump('input-authentication.json',{'source_blobs':14,'complete_canonical_tree_bound_independently':True,'primary_pdf_text_pairs':5,'failed_primary_request':1,'render_files_bound_by_manifest':3,'selected_copy_members':copies,'stable_named_originals':stable,'limits':'Current selected originals and whole-copy memberships checked separately. Copied extents are not semantic read extents. No first-read, whole incoming sealed packet, fresh primary/source/history semantic read, PDF visual or historical whole-parent certificate.'})
    dump('replay.json',{'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'external_handoff_anchors':ANCHORS,'verifier_sha256':sha(ROOT/'code/verify.py'),'payload_files':65,'whole_root_files':68,'directories_including_root':27,'source_blobs':14,'primary_pdf_text_pairs':5,'stable_named_originals':stable,'whole_selected_copies':10,'artifact_cases':7,'negative_cases':5,'moment_entry_checks':32258,'whole_actual_root_unchanged':True,'stable_originals_unchanged':True,'limits':'Artifact bytes/modes and bounded supporting diagnostics only; no frozen theorem/nominee, mathematical/contribution grade, fresh semantic primary/history read or historical whole-parent/OS certificate.'})
    print(json.dumps({'payloads':65,'whole_files':68,'directories_including_root':27,'source_blobs':14,'primary_pairs':5,'stable_originals_and_whole_copies':10,'artifact_cases':7,'negative_cases':5,'moment_entry_checks':32258,'whole_root_unchanged':True}))
if __name__=='__main__':main()
