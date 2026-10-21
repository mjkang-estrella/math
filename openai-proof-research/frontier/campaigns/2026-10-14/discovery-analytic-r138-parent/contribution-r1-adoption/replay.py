#!/usr/bin/env python3
"""Read-only parent artifact intake; analytic review supplies the separate verdict."""
import datetime,gzip,hashlib,importlib.util,io,json,shutil,subprocess,sys,tarfile,tempfile
from pathlib import Path
OUT=Path(__file__).resolve().parent;BASE=OUT.parent.parent;PROJECT=BASE.parents[2]
ROOT=BASE/'h138-contribution-r1';AUTHOR=BASE/'fresh-analytic-discovery-r138'
spec=importlib.util.spec_from_file_location('h138_intake_helpers',OUT.parent/'replay.py');helper=importlib.util.module_from_spec(spec);spec.loader.exec_module(helper)
sha,snap=helper.sha,helper.snap
PROTECTED=helper.helper.PROTECTED
ANCHORS={'FINAL.json':'ca7069ed0b20a5d8870761fcde2332707c43906a926766b1ea76ee9b2c3440fa','MANIFEST.json':'1159fdae68f3e97b4aee4dd3aebb292e1f11366d63880591bda819449cd09c49','REPORT.md':'25c7536c4c930920d25ffe3e74e157747f637dba4f8938774d6580b04a2c5bc1'}
def dump(n,d):(OUT/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
    assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=PROJECT)
    assert all(sha(PROJECT/p)==h for p,h in PROTECTED.items())
    now=datetime.datetime.now(datetime.timezone.utc).isoformat()
    dump('integration-baseline.json',{'observed_utc':now,'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=PROJECT,text=True).strip(),'initial_index_empty':True,'task_count':485,'task_index':482,'protected_unrelated_sha256':PROTECTED})
    before,author_before=snap(ROOT),snap(AUTHOR)
    assert author_before==json.loads((OUT.parent/'observed-root.json').read_text())['root']
    dump('observed-roots.json',{'observed_utc':now,'review_root':before,'author_root':author_before,'limits':'Current complete roots; author matches earlier parent intake. Reviewer only claimed selected original authentication, not whole author inventory. No historical whole-parent or OS claim.'})
    assert all(sha(ROOT/p)==h for p,h in ANCHORS.items())
    m=json.loads((ROOT/'MANIFEST.json').read_text());assert m['schema']==1 and len(m['files'])==83 and len(m['directories'])==28
    assert {p for p,e in before.items() if e['kind']=='file'}==set(m['files'])|set(ANCHORS)
    assert {p for p,e in before.items() if e['kind']=='directory'}==set(m['directories'])
    for p,e in m['files'].items():assert sha(ROOT/p)==e['sha256'] and (ROOT/p).stat().st_size==e['size']
    assert sha(AUTHOR/'H-SCOPE.md')==helper.SCOPE and sha(AUTHOR/'AUTHOR-PROOF.md')==helper.PROOF and sha(AUTHOR/'DERIVATION.md')==helper.DERIVATION
    final=json.loads((ROOT/'FINAL.json').read_text());assert final['contribution']=='TECHNICAL' and final['correctness']=='UNREVIEWED'
    assert final['scope_sha256']==helper.SCOPE and final['author_proof_sha256']==helper.PROOF
    assert not final['suspected_material_new_proof_gaps_established'] and not final['accepted'] and final['count_change']==0
    tp=PROJECT/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'==sha(ROOT/'private/originals/sources/preprints-tree.json')
    tree=json.loads(tp.read_text());assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']}
    sources=json.loads((ROOT/'source-authentication.json').read_text())['files'];assert len(sources)==17
    for e in sources:
        data=(ROOT/e['copy']).read_bytes();node=entries[e['canonical_path']]
        assert len(data)==e['size']==node['size'] and sha(ROOT/e['copy'])==e['sha256']
        assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob_sha1']==node['sha']
        assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['canonical_path']
    members=json.loads((ROOT/'input-membership.json').read_text());assert len(members)==52
    for e in members:
        origin=PROJECT/e['original'];data=origin.read_bytes()
        assert sha(origin)==sha(ROOT/e['copy'])==e['sha256'] and len(data)==e['size']
        assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob_sha1']
    auth=json.loads((ROOT/'incoming-authentication.json').read_text())
    assert all(sha(AUTHOR/p)==h for p,h in auth['external_anchors'].items())
    assert len(auth['original_root_manifest_selected_authentication'])==62 and len(auth['excluded_unopened'])==11
    am=json.loads((AUTHOR/'MANIFEST.json').read_text())['files']
    for e in auth['original_root_manifest_selected_authentication']:
        assert sha(AUTHOR/e['path'])==e['sha256'] and am[e['path']]=={'size':e['size'],'sha256':e['sha256']}
    primary=json.loads((ROOT/'primary-authentication.json').read_text())['versions'];assert len(primary)==4
    for e in primary:
        raw=ROOT/e['raw'];assert sha(raw)==e['sha256'] and raw.stat().st_size==e['size'] and e['url']=='https://arxiv.org/src/'+e['id']
        dec=gzip.decompress(raw.read_bytes())
        try:
            with tarfile.open(fileobj=io.BytesIO(dec),mode='r:') as archive:
                files={v.name:archive.extractfile(v).read() for v in archive.getmembers() if v.isfile() and any(Path(v.name).name==Path(x['path']).name for x in e['extracts'])}
        except tarfile.ReadError:files={'main.tex':dec}
        for x in e['extracts']:
            data=(ROOT/x['path']).read_bytes();matched=[v for k,v in files.items() if Path(k).name==Path(x['path']).name]
            assert len(matched)==1 and matched[0]==data and len(data)==x['size'] and sha(ROOT/x['path'])==x['sha256']
    selected=json.loads((ROOT/'final-input-observations.json').read_text())['selected_originals']
    assert len(selected)==52 and all(sha(PROJECT/e['original'])==e['sha256'] for e in selected)
    readings=json.loads((ROOT/'reading-ledger.json').read_text())['entries']
    for e in readings:
        data=(ROOT/e['copy']).read_bytes();assert hashlib.sha256(data).hexdigest()==e['sha256']
        if 'read_ranges' in e:
            lines=data.splitlines()
            for rr in e['read_ranges']:assert hashlib.sha256(b'\n'.join(lines[rr['start']-1:rr['end']])).hexdigest()==rr['raw_line_join_sha256']
        if 'decoded_field' in e:
            lo,hi=e['decoded_lines'];text='\n'.join(json.loads(data)[e['decoded_field']].splitlines()[lo-1:hi])
            assert hashlib.sha256(text.encode()).hexdigest()==e['decoded_passage_sha256']
            assert (ROOT/e['extract']).read_bytes()==(text+'\n').encode()
    proof_before=snap(BASE/'h138-proof-r1');adoption_before=snap(OUT.parent/'proof-r1-adoption')
    assert proof_before==json.loads((OUT.parent/'proof-r1-adoption/observed-roots.json').read_text())['review_root']
    dump('historical-proof-observation.json',{'review_root':proof_before,'adoption_root':adoption_before,'proof_disposition_sha256':sha(OUT.parent/'proof-r1-disposition.md'),'limits':'Earlier correctness packet remains historical with its then-pending contribution status.'})
    cases=[]
    with tempfile.TemporaryDirectory(prefix='h138-contribution-copy-',dir=OUT) as temp:
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
        p=copy/'private/extra-empty-directory';p.mkdir();check('extra_empty_directory',False);p.rmdir()
        wrong=args.copy();wrong[5]='0'*64;check('wrong_external_manifest_anchor',False,wrong)
        check('restored',True);assert snap(copy)==before
    assert snap(ROOT)==before and snap(AUTHOR)==author_before
    assert snap(BASE/'h138-proof-r1')==proof_before and snap(OUT.parent/'proof-r1-adoption')==adoption_before
    assert all(sha(PROJECT/e['original'])==e['sha256'] for e in members)
    assert all(sha(PROJECT/p)==h for p,h in PROTECTED.items())
    dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':5,'copy_removed':True,'whole_review_and_author_roots_unchanged':True,'limits':'Complete copied-review artifact byte controls only; no mathematical gate.'})
    dump('input-authentication.json',{'source_blobs':17,'raw_primary_versions':4,'matching_archive_extracts':sum(len(e['extracts']) for e in primary),'selected_members':members,'permitted_author_payloads':62,'reviewer_unopened_author_payloads':11,'read_ledger_passage_hashes_verified':True,'limits':'Current selected byte observations only; no mutable journal stability or fresh semantic source/primary/history reading.'})
    dump('replay.json',{'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'external_review_anchors':ANCHORS,'verifier_sha256':sha(ROOT/'verify.py'),'frozen_scope_sha256':helper.SCOPE,'author_proof_sha256':helper.PROOF,'prefreeze_derivation_sha256':helper.DERIVATION,'payload_files':83,'whole_review_files':86,'review_directories':28,'whole_author_files':76,'source_blobs':17,'raw_primary_versions':4,'matching_archive_extracts':5,'stable_selected_members':52,'reviewer_permitted_author_payloads':62,'reviewer_unopened_author_payloads':11,'artifact_cases':7,'negative_cases':5,'whole_roots_unchanged':True,'earlier_author_snapshot_matches':True,'earlier_correctness_review_and_adoption_unchanged':True,'stable_selected_members_unchanged':True,'limits':'Artifact evidence only; full TECHNICAL contribution disposition adopted separately, and prior correctness PASS discharges its condition only. Reviewer selective copy is not whole author packet. Parent adds no new semantic source/primary/history reading, exhaustive search, first-read, OS/whole-parent or priority certificate.'})
    print(json.dumps({'payloads':83,'whole_files':86,'source_blobs':17,'raw_primary_versions':4,'stable_selected_members':52,'artifact_cases':7,'negative_cases':5,'whole_roots_unchanged':True}))
if __name__=='__main__':main()
