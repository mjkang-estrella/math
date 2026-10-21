#!/usr/bin/env python3
"""Parent archive authentication only; no mathematical or contribution gate."""
import datetime
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

OUT = Path(__file__).resolve().parent
BASE = OUT.parent
PROJECT = BASE.parents[2]
ROOT = BASE / 'fresh-arithmetic-discovery-r110'
HELPER = BASE / 'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py'
spec = importlib.util.spec_from_file_location('archive_snapshot_helpers', HELPER)
helper = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helper)
sha, snap = helper.sha, helper.snap
ANCHORS = {
    'FINAL.json': '792470c2ec04f552aabfae0a7623bda74b5608ba31c9a75e48d9b9ea96302c6f',
    'MANIFEST.json': '54f395d992bf8eb50e6ded400722ea73bb1febd122b06c883513a3fdd7995fcc',
    'REPORT.md': 'ac27dec875f56154abc9093fa9e4e3abdb216a3a71a3018eceee5c9c758b5c5d',
}
PROTECTED = {
    'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json': '6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9',
    'frontier/iterations/i31-nonconical-no-mcm.md': 'd606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a',
}


def dump(name, value):
    (OUT / name).write_text(json.dumps(value, indent=2) + '\n')


def main():
    assert not subprocess.check_output(['git', 'diff', '--cached', '--name-only'], cwd=PROJECT)
    assert all(sha(PROJECT / p) == h for p, h in PROTECTED.items())
    now = datetime.datetime.now(datetime.timezone.utc).isoformat()
    dump('integration-baseline.json', {'observed_utc': now,
         'head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=PROJECT, text=True).strip(),
         'initial_index_empty': True, 'task_count': 487, 'task_index': 484,
         'protected_unrelated_sha256': PROTECTED,
         'tasks_sha256': sha(BASE / 'tasks.json'),
         'journal_sha256': sha(PROJECT / 'frontier/NEW-TEN-2026-10-14.md')})
    before = snap(ROOT)
    dump('observed-root.json', {'observed_utc': now, 'root': before,
         'limits': 'Current whole actual root including outside copied controls; not historical whole-parent or OS evidence.'})
    assert all(sha(ROOT / p) == h for p, h in ANCHORS.items())
    manifest = json.loads((ROOT / 'MANIFEST.json').read_text())
    assert manifest['schema']=='r110-exact-payload-v1' and len(manifest['files'])==83 and manifest['excluded_root']=='scratch/'
    expected={e['path'] for e in manifest['files']}|set(manifest['outside_payload'])
    assert {p for p,e in before.items() if e['kind']=='file' and not p.startswith('scratch/')}==expected
    for e in manifest['files']:
        assert sha(ROOT/e['path'])==e['sha256'] and (ROOT/e['path']).stat().st_size==e['bytes']
    selected=json.loads((ROOT/'private/history/metadata.json').read_text());assert len(selected)==24
    stable=[];mutable=[]
    for e in selected:
        assert sha(ROOT/e['local'])==e['sha256'] and (ROOT/e['local']).stat().st_size==e['bytes']
        if e['original']=='frontier/NEW-TEN-2026-10-14.md':
            assert (ROOT/e['local']).read_bytes().splitlines()==(PROJECT/e['original']).read_bytes().splitlines()[18:27]
            mutable.append({'original':e['original'],'late_whole_sha256':e['whole_original_sha256'],'current_whole_sha256':sha(PROJECT/e['original']),'retained_extent':'lines19-27','excerpt_matches_current':True,'whole_file_is_not_stability_input':True})
        else:
            assert sha(PROJECT/e['original'])==e['sha256'],e['original'];stable.append(e)
    assert len(stable)==23 and len(mutable)==1
    treefile=PROJECT/'sources/preprints-tree.json'
    assert sha(treefile)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree=json.loads(treefile.read_text());assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']}
    sources=json.loads((ROOT/'private/source/metadata.json').read_text())+json.loads((ROOT/'private/source/kurosh-metadata.json').read_text());assert len(sources)==34
    import hashlib
    for e in sources:
        data=(ROOT/e['local']).read_bytes();t=entries[e['canonical_path']]
        assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==t['sha']==e['git_blob_sha1']
        assert len(data)==t['size']==e['bytes'] and sha(ROOT/e['local'])==e['sha256']
        assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['canonical_path']
    primary=json.loads((ROOT/'private/primary/metadata.json').read_text());successes=[e for e in primary if 'pdf' in e];failures=[e for e in primary if 'error' in e]
    assert len(successes)==3 and len(failures)==1
    for e in successes:
        assert sha(ROOT/e['pdf'])==e['sha256'] and (ROOT/e['pdf']).stat().st_size==e['bytes']
        assert sha(ROOT/e['text'])==e['text_sha256'] and (ROOT/e['text']).stat().st_size==e['text_bytes']
    cases=[]
    with tempfile.TemporaryDirectory(prefix='arithmetic110-copy-',dir=OUT) as temp:
        copy=Path(temp)/'packet'
        for p in sorted(expected):
            dst=copy/p;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(ROOT/p,dst)
        pristine=snap(copy)
        args=[str(copy),'--final-hash',ANCHORS['FINAL.json'],'--manifest-hash',ANCHORS['MANIFEST.json'],'--report-hash',ANCHORS['REPORT.md']]
        def check(label, expected_pass, custom=None):
            state=snap(copy)
            r=subprocess.run([sys.executable,'-B',str(copy/'code/verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30)
            assert (r.returncode==0)==expected_pass,(label,r.stdout,r.stderr)
            assert snap(copy)==state
            cases.append(dict(case=label,expected_pass=expected_pass,returncode=r.returncode,fixture_unchanged=True,stdout=r.stdout.strip(),stderr=r.stderr.strip()))
        check('baseline_declared_packet',True)
        diag=subprocess.run([sys.executable,'-B',str(copy/'code/flow_diagnostic.py')],capture_output=True,text=True,timeout=30)
        assert diag.returncode==0 and json.loads(diag.stdout)==json.loads((ROOT/'notes/diagnostics.json').read_text())
        assert snap(copy)==pristine
        p=copy/'notes/kurosh-feasibility.md';data=p.read_bytes();p.write_bytes(data+b'\nCONTROL\n')
        check('modified_payload',False);p.unlink();check('missing_payload',False);p.write_bytes(data)
        p=copy/'private/.extra-control.json';p.write_text('{}');check('extra_hidden_payload',False);p.unlink()
        wrong=args.copy();wrong[2]='0'*64;check('wrong_external_final_anchor',False,wrong)
        check('restored',True);assert snap(copy)==pristine
    assert snap(ROOT)==before
    assert all(sha(PROJECT/e['original'])==e['sha256'] for e in stable)
    dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':4,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Complete declared packet copied; outside scratch subtree omitted. Artifact controls only.'})
    dump('diagnostic-replay.json',json.loads(diag.stdout))
    dump('input-authentication.json',{'source_blobs':34,'primary_versions':successes,'failed_acquisitions':failures,'stable_named_originals':stable,'mutable_context':mutable,'limits':'Byte binding only; no fresh semantic source/primary/history reading or historical isolation claim.'})
    dump('replay.json',{'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'external_handoff_anchors':ANCHORS,'verifier_sha256':sha(ROOT/'code/verify.py'),'payload_files':83,'whole_root_files':sum(e['kind']=='file' for e in before.values()),'canonical_pinned_source_blobs':34,'primary_pdf_text_pairs':3,'failed_primary_requests':1,'stable_named_originals':stable,'mutable_context':mutable,'artifact_cases':6,'negative_cases':4,'bounded_diagnostics':{'cyclic_graph_cases':7,'valuation_inequalities':41984},'whole_actual_root_unchanged':True,'stable_originals_unchanged':True,'limits':'Artifact and bounded diagnostics only; no mathematical/contribution gate, whole-primary/history or mutable-journal stability certificate.'})
    print(json.dumps({'payloads':83,'sources':34,'primary_pairs':3,'stable_originals':23,'mutable_excerpt':1,'artifact_cases':6,'negative_cases':4,'whole_root_unchanged':True}))

if __name__=='__main__':main()
