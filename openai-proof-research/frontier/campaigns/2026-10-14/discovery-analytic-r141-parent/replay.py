#!/usr/bin/env python3
"""Parent artifact replay only; no source-truth or mathematical gate."""
import datetime,gzip,hashlib,importlib.util,io,json,shutil,subprocess,sys,tarfile,tempfile
from pathlib import Path
OUT=Path(__file__).resolve().parent;BASE=OUT.parent;PROJECT=BASE.parents[2];ROOT=BASE/'fresh-analytic-discovery-r141'
spec=importlib.util.spec_from_file_location('archive_helpers',BASE/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');helper=importlib.util.module_from_spec(spec);spec.loader.exec_module(helper)
sha,snap=helper.sha,helper.snap
PROTECTED={'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json':'6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9','frontier/iterations/i31-nonconical-no-mcm.md':'d606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a'}
ANCHORS={'FINAL.md':'1eec0ca8a47f3e4d19c6b0dd7d8b16feacd2744956d7e9ddfdfa7dad14505b47','MANIFEST.json':'7d49819a9fe48bd4454386239fad7d633f000871a7560c7fdb21e4e07cfb008a','REPORT.md':'1498dd12318591e55ea614e23bb66bdfd2605905129e4d6ea74f5f4ce258b45c'}
def dump(n,d):(OUT/n).write_text(json.dumps(d,indent=2)+'\n')
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def main():
    assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=PROJECT)
    assert all(sha(PROJECT/p)==h for p,h in PROTECTED.items())
    now=datetime.datetime.now(datetime.timezone.utc).isoformat()
    dump('integration-baseline.json',{'observed_utc':now,'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=PROJECT,text=True).strip(),'initial_index_empty':True,'task_count':493,'task_index':491,'protected_unrelated_sha256':PROTECTED})
    before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current whole actual root, not historical whole-parent or OS evidence.'})
    assert all(sha(ROOT/p)==h for p,h in ANCHORS.items())
    terminal=json.loads((OUT/'task-status.json').read_text())['structuredContent']
    assert terminal['status']=='completed' and all(h in terminal['summary'] for h in ANCHORS.values())
    m=json.loads((ROOT/'MANIFEST.json').read_text());assert m['schema']=='r141-exact-payload-v1'
    files=m['files'];dirs=m['directories'];assert len(files)==122 and len(dirs)==32
    assert {p for p,e in before.items() if e['kind']=='file'}==set(files)|set(ANCHORS)
    assert {p for p,e in before.items() if e['kind']=='directory'}==set(dirs)
    assert all(e['kind'] in ['file','directory'] and (e['kind']!='file' or e['nlink']==1) for e in before.values())
    for p,e in files.items():assert sha(ROOT/p)==e['sha256'] and (ROOT/p).stat().st_size==e['size']
    tp=PROJECT/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree=json.loads(tp.read_text());assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']}
    assert (ROOT/'private/original-selections/02-preprints-tree.json').read_bytes()==tp.read_bytes()
    source=json.loads((ROOT/'source-authentication.json').read_text());sources=source['files'];assert len(sources)==73 and source['pin']=='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
    for e in sources:
        data=(ROOT/e['local']).read_bytes();node=entries[e['path']]
        assert len(data)==e['size']==node['size'] and sha(ROOT/e['local'])==e['sha256']
        assert blob(data)==e['git_blob']==node['sha']
        assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
    primary=json.loads((ROOT/'primary-authentication.json').read_text());assert len(primary)==5
    raw_count=extracts=failed=pdfpairs=0
    for e in primary:
        if 'raw_sha256' not in e:
            assert e['name']=='bgh' and '404' in e['error'];failed+=1;continue
        raw=ROOT/'private/primary'/e['name']/'raw'
        assert sha(raw)==e['raw_sha256'] and raw.stat().st_size==e['raw_size'];raw_count+=1
        data=raw.read_bytes()
        for x in e['members']:assert sha(ROOT/x['path'])==x['sha256'] and (ROOT/x['path']).stat().st_size==x['size']
        if e['name']=='bessa':
            assert data==(ROOT/'private/primary/bessa/paper.pdf').read_bytes() and data.startswith(b'%PDF');pdfpairs+=1;continue
        try:
            with tarfile.open(fileobj=io.BytesIO(data),mode='r:*') as archive:
                members={v.name:archive.extractfile(v).read() for v in archive.getmembers() if v.isfile() and v.name.endswith(('.tex','.bib','.bbl'))}
            for x in e['members']:
                name=x['path'].split('/extracted/',1)[1];assert members[name]==(ROOT/x['path']).read_bytes();extracts+=1
        except tarfile.ReadError:
            assert len(e['members'])==1 and gzip.decompress(data)==(ROOT/e['members'][0]['path']).read_bytes();extracts+=1
    assert (raw_count,extracts,failed,pdfpairs)==(4,3,1,1)
    originals=json.loads((ROOT/'original-authentication.json').read_text())['files'];assert len(originals)==13
    stable=[]
    for e in originals:
        p=Path(e['canonical_original_path']);rel=p.relative_to(PROJECT).as_posix();data=p.read_bytes()
        assert len(data)==e['size'] and sha(p)==e['sha256'] and blob(data)==e['computed_git_blob']
        stable.append({'path':rel,'sha256':e['sha256'],'size':e['size'],'late_observation_utc':e['observation_utc']})
    copies=json.loads((ROOT/'selected-copy-membership.json').read_text())['files'];assert len(copies)==13
    whole_declared=ranged=whole_bytes=0
    for e in copies:
        original=Path(e['original_path']).read_bytes();data=(ROOT/e['selected_path']).read_bytes()
        assert hashlib.sha256(original).hexdigest()==e['original_sha256']
        if e['selection']=='whole-byte copy':expected=original;whole_declared+=1
        else:
            lines=original.splitlines(keepends=True);expected=b''.join(b''.join(lines[a-1:z]) for a,z in e['selection']['one_based_inclusive_lines']);ranged+=1
        assert data==expected and len(data)==e['size'] and sha(ROOT/e['selected_path'])==e['sha256']
        whole_bytes+=data==original
    assert (whole_declared,ranged,whole_bytes)==(8,5,9)
    cases=[]
    with tempfile.TemporaryDirectory(prefix='analytic141-copy-',dir=OUT) as temp:
        copy=Path(temp)/'packet';shutil.copytree(ROOT,copy)
        args=[str(copy),'--final-sha256',ANCHORS['FINAL.md'],'--manifest-sha256',ANCHORS['MANIFEST.json'],'--report-sha256',ANCHORS['REPORT.md']]
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
    dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':4,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Complete copied packet byte controls only; no mathematical gates.'})
    dump('input-authentication.json',{'source_blobs':73,'complete_canonical_tree_bound_independently':True,'primary_successful_raw_objects':4,'arxiv_versions_and_matching_extracts':3,'publisher_pdf_text_pair':1,'publisher_render_bound_by_manifest':1,'failed_primary_request':1,'selected_copy_members':copies,'stable_named_originals':stable,'declared_whole_copies':8,'line_range_selections':5,'actual_whole_file_selections':9,'proper_excerpt_selections':4,'limits':'Current originals and selected-copy membership separately checked. I80 line range contains its complete file. Copied extents differ from read extents. No fresh primary/source/history semantic reading, first-read, PDF visual or historical whole-parent certificate.'})
    dump('replay.json',{'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'external_handoff_anchors':ANCHORS,'verifier_sha256':sha(ROOT/'verify.py'),'payload_files':122,'whole_root_files':125,'directories':32,'source_blobs':73,'primary_successful_raw_objects':4,'arxiv_versions_and_matching_extracts':3,'publisher_pdf_text_pair':1,'stable_named_originals':stable,'selected_copy_members':13,'actual_whole_file_selections':9,'proper_excerpt_selections':4,'artifact_cases':6,'negative_cases':4,'whole_actual_root_unchanged':True,'stable_originals_unchanged':True,'limits':'Artifact bytes only; no frozen theorem/nominee, mathematical/contribution grade, fresh semantic primary/history reading or historical whole-parent/OS certificate.'})
    print(json.dumps({'payloads':122,'whole_files':125,'directories':32,'source_blobs':73,'arxiv_versions_and_extracts':3,'publisher_pdf_pair':1,'stable_originals':13,'actual_whole_selections':9,'proper_excerpts':4,'artifact_cases':6,'negative_cases':4,'whole_root_unchanged':True}))
if __name__=='__main__':main()
