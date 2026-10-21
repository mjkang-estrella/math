#!/usr/bin/env python3
"""Parent byte authentication only; no source-truth or mathematical gate."""
import datetime,gzip,hashlib,importlib.util,io,json,shutil,subprocess,sys,tarfile,tempfile
from pathlib import Path
OUT=Path(__file__).resolve().parent;BASE=OUT.parent;PROJECT=BASE.parents[2];ROOT=BASE/'fresh-analytic-discovery-r139'
spec=importlib.util.spec_from_file_location('archive_helpers',BASE/'discovery-structural-r145-parent/replay.py');helper=importlib.util.module_from_spec(spec);spec.loader.exec_module(helper)
sha,snap,PROTECTED=helper.sha,helper.snap,helper.PROTECTED
ANCHORS={'FINAL.md':'0e01a01d860308b7bc1bcf2fa252570eff7c4a19126a4e3dea307df8288deb2f','MANIFEST.json':'e571d577e4c42d56ab3f22538a395dc6c2f11d80bfecf028533834df808c9675','REPORT.md':'8dce1ee569febde1e34fd3558f76d20077ac1b51357412e113b1a0488cfd2f61'}
def dump(n,d):(OUT/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
    assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=PROJECT)
    assert all(sha(PROJECT/p)==h for p,h in PROTECTED.items())
    now=datetime.datetime.now(datetime.timezone.utc).isoformat()
    dump('integration-baseline.json',{'observed_utc':now,'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=PROJECT,text=True).strip(),'initial_index_empty':True,'task_count':489,'task_index':486,'protected_unrelated_sha256':PROTECTED})
    before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current whole actual root, not historical whole-parent or OS evidence.'})
    assert all(sha(ROOT/p)==h for p,h in ANCHORS.items())
    m=json.loads((ROOT/'MANIFEST.json').read_text());assert m['schema']=='r139-exact-payload-v1'
    files=m['inventory']['files'];dirs=m['inventory']['directories'];assert len(files)==84 and len(dirs)==30
    assert {p for p,e in before.items() if e['kind']=='file'}==set(files)|set(ANCHORS)
    assert {p for p,e in before.items() if e['kind']=='directory'}==set(dirs)
    for p,e in files.items():assert sha(ROOT/p)==e['sha256'] and (ROOT/p).stat().st_size==e['size']
    tp=PROJECT/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree=json.loads(tp.read_text());assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']}
    sources=json.loads((ROOT/'source-ledger.json').read_text());assert len(sources)==9
    for e in sources:
        data=(ROOT/e['local']).read_bytes();node=entries[e['path']]
        assert len(data)==e['size']==node['size'] and sha(ROOT/e['local'])==e['sha256']
        assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']==node['sha']
        assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
    primary=json.loads((ROOT/'primary-ledger.json').read_text());assert len(primary)==5
    extracted=0
    for e in primary:
        raw=ROOT/'private/primary'/(e['id']+'.raw');assert sha(raw)==e['sha256'] and raw.stat().st_size==e['size'] and e['url']=='https://arxiv.org/src/'+e['id']
        data=raw.read_bytes()
        try:
            with tarfile.open(fileobj=io.BytesIO(data),mode='r:*') as archive:
                members={v.name:archive.extractfile(v).read() for v in archive.getmembers() if v.isfile() and any(v.name==x['member'] for x in e['files'])}
        except tarfile.ReadError:members={'single-gzip':gzip.decompress(data)}
        for x in e['files']:
            text=(ROOT/x['path']).read_bytes();assert members[x['member']]==text and len(text)==x['size'] and sha(ROOT/x['path'])==x['sha256'];extracted+=1
    assert extracted==19
    copies=json.loads((ROOT/'input-membership.json').read_text())['members'];assert len(copies)==20
    for e in copies:assert sha(PROJECT/e['original'])==sha(ROOT/e['copy'])==e['sha256'] and (ROOT/e['copy']).stat().st_size==e['size']
    observations=json.loads((ROOT/'original-current-bindings.json').read_text())['records'];stable=[];mutable=[]
    for e in observations:
        current=sha(PROJECT/e['original'])
        if e['original']=='frontier/NEW-TEN-2026-10-14.md':mutable.append({'path':e['original'],'late_sha256':e['sha256'],'current_sha256':current,'matches_late_observation_now':current==e['sha256'],'not_stability_input':True})
        else:
            data=(PROJECT/e['original']).read_bytes();assert current==e['sha256'] and len(data)==e['size']
            assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob_computed'];stable.append(e)
    assert len(stable)==20 and len(mutable)==1
    for e in json.loads((ROOT/'private/named-context-metadata.json').read_text()):assert sha(PROJECT/e['path'])==e['sha256']
    readings=json.loads((ROOT/'reading-ledger.json').read_text())['actual_primary_passages']
    for e in readings:
        lines=(ROOT/e['path']).read_bytes().splitlines(keepends=True)
        assert hashlib.sha256(b''.join(lines[e['first_line']-1:e['last_line']])).hexdigest()==e['sha256_passage']
    cases=[]
    with tempfile.TemporaryDirectory(prefix='analytic139-copy-',dir=OUT) as temp:
        copy=Path(temp)/'packet';shutil.copytree(ROOT,copy)
        args=['--root',str(copy),'--final-sha',ANCHORS['FINAL.md'],'--manifest-sha',ANCHORS['MANIFEST.json'],'--report-sha',ANCHORS['REPORT.md']]
        def check(label,expected,custom=None):
            state=snap(copy);r=subprocess.run([sys.executable,'-B',str(copy/'verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30)
            assert (r.returncode==0)==expected,(label,r.stdout,r.stderr)
            assert snap(copy)==state
            cases.append({'case':label,'expected_pass':expected,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
        check('baseline_full_packet',True)
        p=copy/'DERIVATION.md';data=p.read_bytes();p.write_bytes(data+b'\nCONTROL\n');check('modified_payload',False);p.unlink();check('missing_payload',False);p.write_bytes(data)
        p=copy/'private/.extra';p.write_text('extra');check('extra_hidden_payload',False);p.unlink()
        wrong=args.copy();wrong[5]='0'*64;check('wrong_external_manifest_anchor',False,wrong);check('restored',True);assert snap(copy)==before
    assert snap(ROOT)==before and all(sha(PROJECT/e['original'])==e['sha256'] for e in stable)
    assert all(sha(PROJECT/p)==h for p,h in PROTECTED.items())
    dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':4,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Complete copied packet byte controls only; no mathematical gates.'})
    dump('input-authentication.json',{'source_blobs':9,'primary_raw_versions':5,'matching_archive_extracts':19,'selected_copy_members':copies,'stable_named_originals':stable,'mutable_context':mutable,'read_passage_hashes_verified':True,'limits':'Current selected bytes and archive extraction only; no fresh source/primary/history semantic read or journal stability claim.'})
    dump('replay.json',{'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'external_handoff_anchors':ANCHORS,'verifier_sha256':sha(ROOT/'verify.py'),'payload_files':84,'whole_root_files':87,'directories':30,'source_blobs':9,'primary_raw_versions':5,'matching_archive_extracts':19,'stable_named_originals':stable,'mutable_context':mutable,'selected_copy_members':20,'artifact_cases':6,'negative_cases':4,'whole_actual_root_unchanged':True,'stable_originals_unchanged':True,'limits':'Artifact byte evidence only; no frozen theorem/nominee, independent correctness/contribution gate, fresh semantic primary/history reading or historical whole-parent/OS certificate.'})
    print(json.dumps({'payloads':84,'whole_files':87,'source_blobs':9,'primary_versions':5,'archive_extracts':19,'stable_originals':20,'mutable_journal':1,'artifact_cases':6,'negative_cases':4,'whole_root_unchanged':True}))
if __name__=='__main__':main()
