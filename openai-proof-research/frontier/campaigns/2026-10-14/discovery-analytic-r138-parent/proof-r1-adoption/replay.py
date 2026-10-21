#!/usr/bin/env python3
"""Read-only parent artifact intake; analytic review supplies the separate verdict."""
import datetime,gzip,hashlib,importlib.util,io,json,shutil,subprocess,sys,tarfile,tempfile
from pathlib import Path
OUT=Path(__file__).resolve().parent;BASE=OUT.parent.parent;PROJECT=BASE.parents[2]
ROOT=BASE/'h138-proof-r1';AUTHOR=BASE/'fresh-analytic-discovery-r138'
spec=importlib.util.spec_from_file_location('h138_intake_helpers',OUT.parent/'replay.py');helper=importlib.util.module_from_spec(spec);spec.loader.exec_module(helper)
sha,snap=helper.sha,helper.snap
PROTECTED=helper.helper.PROTECTED
ANCHORS={'FINAL.json':'f3e0d02590b1c39488bbbeb593cd98ce43e550fd517b817fe9179533528a48ad','MANIFEST.json':'791aacae52d698e03639acafe9bde4262700a7f5a3d5cff761a78a888dc31e16','REPORT.md':'c3fe604edb3710e78bf380020f25c98abb81b0e5b4b40264f3fa4e204986aa19'}
def dump(n,d):(OUT/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
    assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=PROJECT)
    assert all(sha(PROJECT/p)==h for p,h in PROTECTED.items())
    now=datetime.datetime.now(datetime.timezone.utc).isoformat()
    dump('integration-baseline.json',{'observed_utc':now,'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=PROJECT,text=True).strip(),'initial_index_empty':True,'task_count':485,'task_index':483,'protected_unrelated_sha256':PROTECTED})
    before,author_before=snap(ROOT),snap(AUTHOR)
    assert author_before==json.loads((OUT.parent/'observed-root.json').read_text())['root']
    dump('observed-roots.json',{'observed_utc':now,'review_root':before,'author_root':author_before,'limits':'Current complete roots; author matches earlier parent intake. Reviewer only claimed selected original authentication, not whole author inventory. No historical whole-parent or OS claim.'})
    assert all(sha(ROOT/p)==h for p,h in ANCHORS.items())
    m=json.loads((ROOT/'MANIFEST.json').read_text());assert m['schema']==1 and len(m['files'])==79 and len(m['directories'])==30
    assert {p for p,e in before.items() if e['kind']=='file'}==set(m['files'])|set(ANCHORS)
    assert {p for p,e in before.items() if e['kind']=='directory'}==set(m['directories'])
    for p,e in m['files'].items():assert sha(ROOT/p)==e['sha256'] and (ROOT/p).stat().st_size==e['size']
    assert sha(AUTHOR/'H-SCOPE.md')==helper.SCOPE and sha(AUTHOR/'AUTHOR-PROOF.md')==helper.PROOF and sha(AUTHOR/'DERIVATION.md')==helper.DERIVATION
    final=json.loads((ROOT/'FINAL.json').read_text());assert final['correctness']=='PASS' and final['scope_unchanged'] and final['contribution']=='UNREVIEWED'
    assert final['scope_sha256']==helper.SCOPE and final['author_proof_sha256']==helper.PROOF
    assert not final['mathematical_repairs'] and not final['remaining_mathematical_objections'] and final['coverage']==['C'+str(i) for i in range(1,10)]
    tp=PROJECT/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'==sha(ROOT/'private/preprints-tree.json')
    tree=json.loads(tp.read_text());assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']}
    sources=json.loads((ROOT/'source-reading.json').read_text());assert len(sources)==24
    for e in sources:
        data=(ROOT/e['copy']).read_bytes();node=entries[e['canonical_path']]
        assert len(data)==e['size']==node['size'] and sha(ROOT/e['copy'])==e['sha256']
        assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob_sha1']==node['sha']
        assert e['canonical_pin']=='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
        assert e['pinned_url']=='https://raw.githubusercontent.com/openai/math/'+e['canonical_pin']+'/'+e['canonical_path']
    members=json.loads((ROOT/'incoming-membership.json').read_text());assert len(members['members'])==54
    assert all(sha(AUTHOR/p)==h for p,h in members['anchors'].items())
    am=json.loads((AUTHOR/'MANIFEST.json').read_text())['files']
    for e in members['members']:
        origin=Path(e['origin']);assert origin.is_relative_to(PROJECT)
        assert sha(origin)==sha(ROOT/e['copy'])==e['sha256'] and origin.stat().st_size==e['size']
        if origin.is_relative_to(AUTHOR) and origin.name not in members['anchors']:
            assert am[origin.relative_to(AUTHOR).as_posix()]=={'size':e['size'],'sha256':e['sha256']}
    primary=json.loads((ROOT/'primary-reading.json').read_text());assert len(primary)==4
    for e in primary:
        raw=ROOT/'private/incoming/private/primary'/e['version']/'raw.bin'
        assert sha(raw)==e['raw_sha256'] and raw.stat().st_size==e['raw_size'] and e['versioned_original_url']=='https://arxiv.org/src/'+e['version']
        dec=gzip.decompress(raw.read_bytes())
        try:
            with tarfile.open(fileobj=io.BytesIO(dec),mode='r:') as archive:
                files={v.name:archive.extractfile(v).read() for v in archive.getmembers() if v.isfile() and any(Path(v.name).name==Path(x['path']).name for x in e['extracts'])}
        except tarfile.ReadError:files={'main.tex':dec}
        for x in e['extracts']:
            data=(ROOT/x['path']).read_bytes();matched=[v for k,v in files.items() if Path(k).name==Path(x['path']).name]
            assert len(matched)==1 and matched[0]==data
            assert len(data)==x['size'] and sha(ROOT/x['path'])==x['sha256']
    selected=json.loads((ROOT/'private/selected-originals-unchanged.json').read_text())['selected_checks']
    assert len(selected)==54 and all(sha(Path(e['origin']))==e['sha256'] for e in selected)
    original_context=json.loads((ROOT/'original-reading.json').read_text());observations=[]
    for e in original_context:
        path=Path(e['origin']);old=e.get('sha256',e.get('original_sha256'));mutable=path==PROJECT/'frontier/NEW-TEN-2026-10-14.md'
        current=sha(path)
        if not mutable:assert current==old,e['origin']
        if 'copy' in e:assert sha(ROOT/e['copy'])==old
        if 'selected_copy' in e:
            lo,hi=e['read_lines_in_decoded_field'];text='\n'.join(json.loads(path.read_text())[e['decoded_field']].splitlines()[lo-1:hi])+'\n'
            assert (ROOT/e['selected_copy']).read_bytes()==text.encode() and sha(ROOT/e['selected_copy'])==e['selected_sha256']
        observations.append({'origin':e['origin'],'observed_sha256':current,'retained_metadata_sha256':old,'matches_retained_metadata_now':current==old,'mutable_journal_not_stability_input':mutable})
    cases=[]
    with tempfile.TemporaryDirectory(prefix='h138-proof-copy-',dir=OUT) as temp:
        copy=Path(temp)/'packet';shutil.copytree(ROOT,copy)
        args=['--root',str(copy),'--final-sha256',ANCHORS['FINAL.json'],'--manifest-sha256',ANCHORS['MANIFEST.json'],'--report-sha256',ANCHORS['REPORT.md']]
        def check(label,expected,custom=None):
            state=snap(copy)
            r=subprocess.run([sys.executable,'-B',str(copy/'verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30)
            assert (r.returncode==0)==expected,(label,r.stdout,r.stderr)
            assert snap(copy)==state
            cases.append({'case':label,'expected_pass':expected,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
        check('baseline_complete_packet',True)
        p=copy/'REVIEW.md';data=p.read_bytes();p.write_bytes(data+b'\nCONTROL\n');check('modified_review',False);p.unlink();check('missing_review',False);p.write_bytes(data)
        p=copy/'private/.extra.json';p.write_text('{}');check('extra_hidden_payload',False);p.unlink()
        wrong=args.copy();wrong[5]='0'*64;check('wrong_external_manifest_anchor',False,wrong)
        check('restored',True);assert snap(copy)==before
    assert snap(ROOT)==before and snap(AUTHOR)==author_before
    assert all(sha(Path(e['origin']))==e['sha256'] for e in members['members'])
    assert all(sha(PROJECT/p)==h for p,h in PROTECTED.items())
    dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':4,'copy_removed':True,'whole_review_and_author_roots_unchanged':True,'limits':'Complete copied-review artifact byte controls only; no mathematical gate.'})
    dump('input-authentication.json',{'source_blobs':24,'raw_primary_versions':4,'matching_archive_extracts':sum(len(e['extracts']) for e in primary),'selected_members':members['members'],'additional_original_context_observations':observations,'limits':'Selected current byte observations only; mutable journal may drift and is not a stability input. No fresh semantic primary/source/history reading.'})
    dump('replay.json',{'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'external_review_anchors':ANCHORS,'verifier_sha256':sha(ROOT/'verify.py'),'frozen_scope_sha256':helper.SCOPE,'author_proof_sha256':helper.PROOF,'prefreeze_derivation_sha256':helper.DERIVATION,'payload_files':79,'whole_review_files':82,'review_directories':30,'whole_author_files':76,'source_blobs':24,'raw_primary_versions':4,'matching_archive_extracts':5,'stable_selected_members':54,'additional_stable_parent_intake_copies':3,'original_context_observations':observations,'artifact_cases':6,'negative_cases':4,'whole_roots_unchanged':True,'earlier_author_snapshot_matches':True,'stable_selected_members_unchanged':True,'limits':'Artifact byte evidence only; independent C1-C9 analytic verdict adopted separately. Reviewer selective incoming copy differs from whole author packet; copied original manifest is reference only. Parent no new source/primary/history semantic reads, perfect search/isolation, first-read, OS/whole-parent or priority certificate.'})
    print(json.dumps({'payloads':79,'whole_files':82,'source_blobs':24,'raw_primary_versions':4,'stable_selected_members':54,'artifact_cases':6,'negative_cases':4,'whole_roots_unchanged':True,'mutable_journal_comparison':[e['matches_retained_metadata_now'] for e in observations if e['mutable_journal_not_stability_input']]}))
if __name__=='__main__':main()
