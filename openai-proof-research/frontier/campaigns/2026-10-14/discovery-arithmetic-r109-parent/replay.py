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
ROOT = BASE / 'fresh-arithmetic-discovery-r109'
HELPER = BASE / 'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py'
spec = importlib.util.spec_from_file_location('archive_snapshot_helpers', HELPER)
helper = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helper)
sha, snap = helper.sha, helper.snap
ANCHORS = {
    'FINAL.md': '6c1fb2f4e6fd1013b3e1233a38031e890ae961a75c3f6a62bf5c4a8d25beddb8',
    'MANIFEST.json': '10b898c77283a7c83b3f181c43e278f32dca4e89109658b81019a73532a0f8af',
    'REPORT.md': 'b709fb426f96b0e5d1f1d39cd2cbb6cd8e06302c0d6ff27c6b40d4ec924e562e',
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
         'initial_index_empty': True, 'task_count': 484, 'task_index': 479,
         'protected_unrelated_sha256': PROTECTED,
         'tasks_sha256': sha(BASE / 'tasks.json'),
         'journal_sha256': sha(PROJECT / 'frontier/NEW-TEN-2026-10-14.md')})
    before = snap(ROOT)
    dump('observed-root.json', {'observed_utc': now, 'root': before,
         'limits': 'Current whole actual root including outside copied controls; not historical whole-parent or OS evidence.'})
    assert all(sha(ROOT / p) == h for p, h in ANCHORS.items())
    manifest = json.loads((ROOT / 'MANIFEST.json').read_text())
    assert manifest['format'] == 'r109-exact-payload-v1' and len(manifest['files']) == 80
    assert manifest['outside_control_subtree'] == 'scratch/copied-controls'
    expected = {e['path'] for e in manifest['files']} | set(manifest['outside_envelopes'])
    assert {p for p, e in before.items() if e['kind'] == 'file' and not p.startswith('scratch/copied-controls/')} == expected
    for e in manifest['files']:
        assert sha(ROOT / e['path']) == e['sha256'] and (ROOT / e['path']).stat().st_size == e['bytes']
    selected = sum([json.loads((ROOT / ('private/history/' + n)).read_text()) for n in ['initial-metadata.json', 'late-metadata.json']], [])
    assert len(selected) == 16
    for e in selected:
        assert sha(PROJECT / e['path']) == sha(ROOT / e['copy']) == e['sha256'], e['path']
    treefile = PROJECT / 'sources/preprints-tree.json'
    assert sha(treefile) == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree = json.loads(treefile.read_text()); assert len(tree['tree']) == 13223 and not tree['truncated']
    entries = {e['path']: e for e in tree['tree']}
    sources = json.loads((ROOT / 'private/source/metadata.json').read_text())
    import hashlib
    for e in sources:
        data = (ROOT / e['local']).read_bytes(); t = entries[e['path']]
        assert hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == t['sha'] == e['git_blob']
        assert len(data) == t['size'] == e['bytes'] and sha(ROOT / e['local']) == e['sha256']
        assert e['url'] == 'https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' + e['path']
    primary = json.loads((ROOT / 'private/primary/metadata.json').read_text())
    for n in ['mermin-murai-retry.json','mermin-murai-v1-metadata.json','chapman-kuo-metadata.json','transitive-metadata.json']:
        e=json.loads((ROOT / 'private/primary' / n).read_text()); primary += e if isinstance(e,list) else [e]
    successes=[e for e in primary if 'pdf' in e]; failures=[e for e in primary if 'failure' in e]
    assert len(successes)==7 and len(failures)==2
    for e in successes:
        assert sha(ROOT / e['pdf'])==e['sha256'] and (ROOT/e['pdf']).stat().st_size==e['bytes']
        assert sha(ROOT / e['text'])==e['text_sha256']
    cases=[]
    with tempfile.TemporaryDirectory(prefix='arithmetic109-copy-',dir=OUT) as temp:
        copy=Path(temp)/'packet'
        for p in sorted(expected):
            dst=copy/p;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(ROOT/p,dst)
        pristine=snap(copy)
        args=['--root',str(copy),'--final-sha256',ANCHORS['FINAL.md'],'--manifest-sha256',ANCHORS['MANIFEST.json'],'--report-sha256',ANCHORS['REPORT.md']]
        def check(label, expected_pass, custom=None):
            state=snap(copy)
            r=subprocess.run([sys.executable,'-B',str(copy/'code/verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30)
            assert (r.returncode==0)==expected_pass,(label,r.stdout,r.stderr)
            assert snap(copy)==state
            cases.append(dict(case=label,expected_pass=expected_pass,returncode=r.returncode,fixture_unchanged=True,stdout=r.stdout.strip(),stderr=r.stderr.strip()))
        check('baseline_declared_packet',True)
        diag=subprocess.run([sys.executable,'-B',str(copy/'code/diagnostics.py')],capture_output=True,text=True,timeout=30)
        assert diag.returncode==0 and json.loads(diag.stdout)==json.loads((ROOT/'notes/diagnostics.json').read_text())
        assert snap(copy)==pristine
        p=copy/'notes/characteristic-feasibility.md';data=p.read_bytes();p.write_bytes(data+b'\nCONTROL\n')
        check('modified_payload',False);p.unlink();check('missing_payload',False);p.write_bytes(data)
        p=copy/'private/.extra-control.json';p.write_text('{}');check('extra_hidden_payload',False);p.unlink()
        wrong=args.copy();wrong[3]='0'*64;check('wrong_external_final_anchor',False,wrong)
        check('restored',True);assert snap(copy)==pristine
    assert snap(ROOT)==before
    assert all(sha(PROJECT/e['path'])==e['sha256'] for e in selected)
    dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':4,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Complete declared packet copied; outside disposable subtree omitted. Artifact controls only.'})
    dump('diagnostic-replay.json',json.loads(diag.stdout))
    dump('input-authentication.json',{'source_blobs':len(sources),'primary_versions':successes,'failed_acquisitions':failures,'current_named_originals':selected,'limits':'Byte binding only; no fresh semantic source/primary/history reading or historical isolation claim.'})
    dump('replay.json',{'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'external_handoff_anchors':ANCHORS,'verifier_sha256':sha(ROOT/'code/verify.py'),'payload_files':80,'whole_root_files':sum(e['kind']=='file' for e in before.values()),'canonical_pinned_source_blobs':25,'primary_pdf_text_pairs':7,'failed_primary_requests':2,'current_named_originals':selected,'artifact_cases':6,'negative_cases':4,'bounded_diagnostics':{'flat_koszul_cases':10,'binary_no_carry_cases':76,'frobenius_curve_identities':20},'whole_actual_root_unchanged':True,'selected_originals_unchanged':True,'limits':'Artifact and bounded diagnostics only; no mathematical/contribution gate or whole-primary/history reading.'})
    print(json.dumps({'payloads':80,'sources':25,'primary_pairs':7,'stable_originals':16,'artifact_cases':6,'negative_cases':4,'whole_root_unchanged':True}))

if __name__ == '__main__':
    main()
