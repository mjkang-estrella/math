#!/usr/bin/env python3
"""Parent correctness intake: current bytes, not mathematical gates."""
import datetime
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

OUT = Path(__file__).resolve().parent
BASE = OUT.parent.parent
PROJECT = BASE.parents[2]
ROOT = BASE / 't185r144-proof-r1'
CONTRIBUTION = BASE / 't185r144-contribution-r1'
AUTHOR = BASE / 'fresh-structural-discovery-r144'
spec = importlib.util.spec_from_file_location('intake_helpers', OUT.parent / 'replay.py')
helper = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helper)
sha, snap = helper.sha, helper.snap
ANCHORS = {
    'FINAL.md': '387c1eecd30a687da20424f70d56ca7211e2b2801a581b0ce406e389d6686df0',
    'MANIFEST.json': '729fa034e5ffd2fef0d7d85c1e5b51471ea428a3bb01b02373b402898109e65b',
    'REPORT.md': '44d89f8f802fc06ca2bb67ae9a951214e119dfb8d12f86d7fdae2c1f3faec74b',
}


def dump(n, v):
    (OUT / n).write_text(json.dumps(v, indent=2) + '\n')


def main():
    assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=PROJECT)
    assert all(sha(PROJECT/p)==h for p,h in helper.PROTECTED.items())
    now=datetime.datetime.now(datetime.timezone.utc).isoformat()
    dump('integration-baseline.json',{'observed_utc':now,'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=PROJECT,text=True).strip(),'initial_index_empty':True,'task_count':485,'task_index':481,'protected_unrelated_sha256':helper.PROTECTED})
    before,author_before,contrib_before=snap(ROOT),snap(AUTHOR),snap(CONTRIBUTION)
    assert author_before==json.loads((OUT.parent/'observed-root.json').read_text())['root']
    assert contrib_before==json.loads((OUT.parent/'contribution-r1-adoption/observed-roots.json').read_text())['review_root']
    historical=snap(OUT.parent/'contribution-r1-adoption')
    dump('observed-roots.json',{'observed_utc':now,'review_root':before,'author_root':author_before,'contribution_root':contrib_before,'historical_contribution_adoption_root':historical,'historical_contribution_disposition_sha256':sha(OUT.parent/'contribution-r1-disposition.md'),'limits':'Current complete roots and earlier author/contribution comparisons, not historical whole-parent or OS evidence.'})
    assert all(sha(ROOT/p)==h for p,h in ANCHORS.items())
    assert sha(ROOT/'tools/verify.py')=='1d5eefe26ff2f98b432ccf11f6e293e4f0d1678e680dce630898c619f893db24'
    m=json.loads((ROOT/'MANIFEST.json').read_text())
    assert m['schema']=='t185r144-proof-r1-exact-v1' and len(m['files'])==54 and len(m['directories'])==33
    assert {p for p,e in before.items() if e['kind']=='file'}=={e['path'] for e in m['files']}|set(m['outer_files'])
    assert {p for p,e in before.items() if e['kind']=='directory'}==set(m['directories'])
    for e in m['files']:
        assert sha(ROOT/e['path'])==e['sha256'] and (ROOT/e['path']).stat().st_size==e['bytes']
    assert sha(AUTHOR/'notes/03-frozen-scope.md')==helper.SCOPE and sha(AUTHOR/'notes/04-author-proof.md')==helper.PROOF
    tp=PROJECT/'sources/preprints-tree.json'
    assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree=json.loads(tp.read_text());assert len(tree['tree'])==13223 and not tree['truncated']
    entries={e['path']:e for e in tree['tree']}
    sources=json.loads((ROOT/'private/receipts/source-reuse.json').read_text());assert len(sources)==4
    for e in sources:
        data=(ROOT/e['local']).read_bytes();t=entries[e['canonical_path']]
        assert len(data)==t['size']==e['tree_size']
        assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']==t['sha']
        assert sha(ROOT/e['local'])==e['sha256']==sha(Path(e['reused_from']))
        assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['canonical_path']
    primary=json.loads((ROOT/'private/receipts/primary-reuse.json').read_text())
    for e in primary:
        p=ROOT/e['file'];assert p.stat().st_size==e['bytes'] and sha(p)==e['sha256']==sha(Path(e['reused_from']))
    for name in ['gollin-joo-v1','bowler-geschke-author7','axioms-v3']:
        assert sha(ROOT/'private/primary'/(name+'.txt'))==sha(ROOT/'private/primary'/(name+'-own-extract.txt'))
    originals=json.loads((ROOT/'private/receipts/selected-originals.json').read_text())['files'];assert len(originals)==18
    for e in originals:
        data=(PROJECT/e['original']).read_bytes()
        assert len(data)==e['bytes'] and sha(PROJECT/e['original'])==sha(ROOT/e['snapshot'])==e['sha256']
        assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['gitblob']
    anchorcheck=json.loads((ROOT/'private/receipts/incoming-anchor-check.json').read_text())
    assert all(sha(AUTHOR/p)==h for p,h in anchorcheck['external_anchors'].items())
    am=json.loads((AUTHOR/'MANIFEST.json').read_text());am={e['path']:e for e in am['files']}
    for path in anchorcheck['manifest_selected_payload_matches']:
        assert sha(AUTHOR/path)==am[path]['sha256']
    completion=json.loads((ROOT/'private/receipts/review-completion.json').read_text())
    assert completion['mathematical_disposition']=='PASS_FULL_UNCHANGED_FROZEN_SCOPE'
    assert not completion['unresolved_issues'] and not completion['needed_repairs']
    cases=[]
    with tempfile.TemporaryDirectory(prefix='t185-proof-copy-',dir=OUT) as temp:
        copy=Path(temp)/'packet';shutil.copytree(ROOT,copy)
        args=[str(copy),'--manifest-sha256',ANCHORS['MANIFEST.json'],'--final-sha256',ANCHORS['FINAL.md'],'--report-sha256',ANCHORS['REPORT.md']]
        def check(label,expected,custom=None):
            state=snap(copy)
            r=subprocess.run([sys.executable,'-B',str(copy/'tools/verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30)
            assert (r.returncode==0)==expected,(label,r.stdout,r.stderr)
            assert snap(copy)==state
            cases.append(dict(case=label,expected_pass=expected,returncode=r.returncode,fixture_unchanged=True,stdout=r.stdout.strip(),stderr=r.stderr.strip()))
        check('baseline',True)
        p=copy/'notes/01-correctness-assessment.md';data=p.read_bytes();p.write_bytes(data+b'\nCONTROL\n')
        check('modified_payload',False);p.unlink();check('missing_payload',False);p.write_bytes(data)
        p=copy/'.extra-control.json';p.write_text('{}');check('extra_hidden_payload',False);p.unlink()
        wrong=args.copy();wrong[2]='0'*64;check('wrong_external_manifest_anchor',False,wrong)
        check('restored',True);assert snap(copy)==before
    assert snap(ROOT)==before and snap(AUTHOR)==author_before and snap(CONTRIBUTION)==contrib_before
    assert snap(OUT.parent/'contribution-r1-adoption')==historical
    assert all(sha(PROJECT/e['original'])==e['sha256'] for e in originals)
    dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':4,'copy_removed':True,'whole_review_author_contribution_roots_unchanged':True,'limits':'Artifact byte controls only, not independent mathematical gates.'})
    dump('input-authentication.json',{'sources':sources,'primary_reuse_records':primary,'selected_originals':originals,'incoming_anchor_check':anchorcheck,'limits':'Byte binding only; parent no new semantic source/primary/history/renders reading.'})
    dump('replay.json',{'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'external_review_anchors':ANCHORS,'frozen_scope_sha256':helper.SCOPE,'author_proof_sha256':helper.PROOF,'payload_files':54,'whole_review_files':58,'directories':33,'whole_author_files':69,'whole_contribution_files':120,'canonical_source185_blobs':4,'operative_primary_versions':3,'matching_reused_text_extractions':3,'selected_current_originals':originals,'stable_selected_inputs':18,'artifact_cases':6,'negative_cases':4,'whole_roots_and_historical_contribution_adoption_unchanged':True,'limits':'Current artifact byte evidence only. Reviewer selected18manifest payloads and did not execute author checker or copy whole author packet. Parent independently observes whole actual author69 unchanged against earlier intake. No fresh primary/history or parent visual read, historical OS/whole-parent or priority claim.'})
    print(json.dumps({'payloads':54,'whole_files':58,'source_blobs':4,'primary_versions':3,'stable_originals':18,'artifact_cases':6,'negative_cases':4,'whole_roots_unchanged':True}))

if __name__=='__main__':
    main()
