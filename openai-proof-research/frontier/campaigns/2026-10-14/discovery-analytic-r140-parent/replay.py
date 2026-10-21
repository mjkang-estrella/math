#!/usr/bin/env python3
"""Parent byte authentication only; no source-truth or mathematical gate."""
import datetime,gzip,hashlib,importlib.util,io,json,shutil,subprocess,sys,tarfile,tempfile
from pathlib import Path
OUT=Path(__file__).resolve().parent;BASE=OUT.parent;PROJECT=BASE.parents[2];ROOT=BASE/'fresh-analytic-discovery-r140'
spec=importlib.util.spec_from_file_location('archive_helpers',BASE/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');helper=importlib.util.module_from_spec(spec);spec.loader.exec_module(helper)
sha,snap=helper.sha,helper.snap
PROTECTED={'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json':'6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9','frontier/iterations/i31-nonconical-no-mcm.md':'d606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a'}
ANCHORS={'FINAL.md':'b95b390781d6b5ccd2cc7a194a7d9195979c7b5ace645369c5c674804c986be1','MANIFEST.json':'797991d6ae838bb83350734bf6e2f054b3289b66ab39828be46895787583cc4d','REPORT.md':'2f8b987ef2b22839b0ea12b679c584da9fb40638acb874442f4557d8b869ae53'}
def dump(n,d):(OUT/n).write_text(json.dumps(d,indent=2)+'\n')
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def main():
    assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=PROJECT)
    assert all(sha(PROJECT/p)==h for p,h in PROTECTED.items())
    now=datetime.datetime.now(datetime.timezone.utc).isoformat()
    dump('integration-baseline.json',{'observed_utc':now,'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=PROJECT,text=True).strip(),'initial_index_empty':True,'task_count':491,'task_index':489,'protected_unrelated_sha256':PROTECTED})
    before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current whole actual root, not historical whole-parent or OS evidence.'})
    assert all(sha(ROOT/p)==h for p,h in ANCHORS.items())
    recovered=json.loads((OUT/'terminal-anchor-recovery.json').read_text())
    assert all(h in json.dumps(recovered) for h in ANCHORS.values())
    m=json.loads((ROOT/'MANIFEST.json').read_text());assert m['schema']=='r140.exact-payload.v1'
    files=m['files'];dirs=m['directories'];assert len(files)==109 and len(dirs)==24
    assert {p for p,e in before.items() if e['kind']=='file'}==set(files)|set(ANCHORS)
    assert {p for p,e in before.items() if e['kind']=='directory'}==set(dirs)
    for p,e in files.items():assert sha(ROOT/p)==e['sha256'] and (ROOT/p).stat().st_size==e['size']
    tp=PROJECT/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree=json.loads(tp.read_text());assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']}
    auth=json.loads((ROOT/'source-authentication.json').read_text());sources=auth['files'];assert len(sources)==33
    selected=json.loads((ROOT/'private/selected-source-tree.json').read_text())['tree'];assert len(selected)==33
    assert all(e==entries[e['path']] for e in selected)
    for e in sources:
        data=(ROOT/e['local']).read_bytes();node=entries[e['path']]
        assert len(data)==e['size']==node['size'] and sha(ROOT/e['local'])==e['sha256']
        assert blob(data)==e['gitblob']==node['sha']
        assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
    primary=json.loads((ROOT/'primary-authentication.json').read_text());assert len(primary)==4
    raw_count=extracted=failed=0
    for e in primary:
        if 'raw' not in e:
            assert e['id']=='1701.03015v2' and '404' in e['error'];failed+=1;continue
        raw=ROOT/e['raw'];assert sha(raw)==e['sha256'] and raw.stat().st_size==e['size'] and e['url']=='https://arxiv.org/src/'+e['id'];raw_count+=1
        data=raw.read_bytes()
        try:
            with tarfile.open(fileobj=io.BytesIO(data),mode='r:*') as archive:
                members={v.name:archive.extractfile(v).read() for v in archive.getmembers() if v.isfile()}
            for x in e['members']:
                name=x['path'].split(e['id']+'/',1)[1];assert members[name]==(ROOT/x['path']).read_bytes()
        except tarfile.ReadError:
            assert len(e['members'])==1 and gzip.decompress(data)==(ROOT/e['members'][0]['path']).read_bytes()
        for x in e['members']:
            assert (ROOT/x['path']).stat().st_size==x['size'] and sha(ROOT/x['path'])==x['sha256'];extracted+=1
    assert (raw_count,extracted,failed)==(3,5,1)
    keel=json.loads((ROOT/'private/primary/Keel-Tao-auth.json').read_text());pdf=ROOT/'private/primary/Keel-Tao-author.pdf'
    assert keel['url']=='https://www-users.cse.umn.edu/~keel/endpoint.pdf' and sha(pdf)==keel['sha256'] and pdf.stat().st_size==keel['size']
    keel_derivatives=['private/primary/Keel-Tao-author.txt','private/primary/Keel-Tao-page-02.png']
    assert all(p in files for p in keel_derivatives)
    originals=json.loads((ROOT/'original-current-bindings.json').read_text());assert len(originals)==12
    stable=[]
    for e in originals:
        data=(PROJECT/e['canonical_path']).read_bytes()
        assert len(data)==e['size'] and sha(PROJECT/e['canonical_path'])==e['sha256'] and blob(data)==e['gitblob']
        stable.append({'path':e['canonical_path'],'sha256':e['sha256'],'size':e['size'],'read_extent':e['read_extent']})
    copies=json.loads((ROOT/'selected-copy-membership.json').read_text());assert len(copies)==12
    for e in copies:
        data=(ROOT/e['path']).read_bytes();original=(PROJECT/e['original']).read_bytes()
        expected=original if e['selection']=='whole named file' else b''.join(original.splitlines(keepends=True)[:100])
        assert data==expected and len(data)==e['size'] and sha(ROOT/e['path'])==e['sha256']
    cases=[]
    with tempfile.TemporaryDirectory(prefix='analytic140-copy-',dir=OUT) as temp:
        copy=Path(temp)/'packet';shutil.copytree(ROOT,copy)
        args=['--root',str(copy),'--final',ANCHORS['FINAL.md'],'--manifest',ANCHORS['MANIFEST.json'],'--report',ANCHORS['REPORT.md']]
        def check(label,expected,custom=None):
            state=snap(copy);r=subprocess.run([sys.executable,'-B',str(copy/'verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30)
            assert (r.returncode==0)==expected,(label,r.stdout,r.stderr)
            assert snap(copy)==state
            cases.append({'case':label,'expected_pass':expected,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
        check('baseline_full_packet',True)
        p=copy/'DERIVATION.md';data=p.read_bytes();p.write_bytes(data+b'\nCONTROL\n');check('modified_payload',False);p.unlink();check('missing_payload',False);p.write_bytes(data)
        p=copy/'private/.extra';p.write_text('extra');check('extra_hidden_payload',False);p.unlink()
        wrong=args.copy();wrong[5]='0'*64;check('wrong_external_manifest_anchor',False,wrong);check('restored',True);assert snap(copy)==before
    assert snap(ROOT)==before and all(sha(PROJECT/e['path'])==e['sha256'] for e in stable)
    assert all(sha(PROJECT/p)==h for p,h in PROTECTED.items())
    dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':4,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Complete copied packet byte controls only; no mathematical gates.'})
    dump('input-authentication.json',{'source_blobs':33,'complete_canonical_tree_bound_independently':True,'private_tree_is_only_selected_subset':True,'primary_raw_versions':3,'matching_archive_or_single_tex_extracts':5,'failed_primary_request':1,'keel_tao_pdf':keel,'keel_tao_derivatives_bound_by_manifest':keel_derivatives,'selected_copy_members':copies,'stable_named_originals':stable,'whole_copies':11,'selected_excerpts':1,'limits':'Current selected bytes and archive extraction only; no fresh source/primary/history semantic reading, PDF render/visual claim, initial-read or historical whole-parent certificate.'})
    dump('replay.json',{'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'external_handoff_anchors':ANCHORS,'anchor_source':'Earlier untruncated same original completed run handoff; final task summary omitted anchors. See terminal-anchor-recovery.json.','verifier_sha256':sha(ROOT/'verify.py'),'payload_files':109,'whole_root_files':112,'directories':24,'source_blobs':33,'primary_raw_versions':3,'matching_archive_or_single_tex_extracts':5,'keel_tao_pdf_text_render':1,'stable_named_originals':stable,'selected_copy_members':12,'artifact_cases':6,'negative_cases':4,'whole_actual_root_unchanged':True,'stable_originals_unchanged':True,'limits':'Artifact byte evidence only; no frozen theorem/nominee, independent correctness/contribution gate, fresh semantic primary/history reading or historical whole-parent/OS certificate.'})
    print(json.dumps({'payloads':109,'whole_files':112,'source_blobs':33,'primary_versions':3,'archive_or_single_extracts':5,'keel_tao_pdf':1,'stable_originals':12,'whole_copies':11,'excerpt_copies':1,'artifact_cases':6,'negative_cases':4,'whole_root_unchanged':True}))
if __name__=='__main__':main()
