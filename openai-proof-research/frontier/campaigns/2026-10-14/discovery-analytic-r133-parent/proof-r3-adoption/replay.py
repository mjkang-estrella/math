#!/usr/bin/env python3
"""Parent replay on disposable copies; independent review adoption is separate."""
import hashlib, importlib.util, json, shutil, stat, subprocess, sys, tempfile
from pathlib import Path
sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PROJECT = HERE.parents[4]
BASE = PROJECT / 'frontier/campaigns/2026-10-14'
REVIEW = BASE / 't088p133-proof-r3'
ANCHORS = {
    'FINAL.json': '1de166996e1131bb730501cc1c22ea09b0b3418ec3b266ce63ecedb4f6d25a88',
    'packet/MANIFEST.json': '407a6065cd2e44824701ec63459003f740d2c343cf5aca7e84450a84a2c34695',
    'REPORT.md': '1dbc83e2768d52df28a4475d3d572fa2c90264632ef85b7f5d2be12775e2422c',
}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def snapshot(root):
    out = {}
    for p in [root, *root.rglob('*')]:
        s = p.lstat()
        v = {'mode': stat.S_IMODE(s.st_mode), 'type': stat.S_IFMT(s.st_mode)}
        if p.is_symlink(): v['target'] = str(p.readlink())
        elif p.is_file(): v.update(bytes=s.st_size, sha256=sha(p), nlink=s.st_nlink)
        out[str(p.relative_to(root))] = v
    return out
def run(args):
    r = subprocess.run(args, capture_output=True, text=True)
    assert r.returncode == 0, (args, r.returncode, r.stderr)
    return {'exit': r.returncode, 'stdout': r.stdout, 'stderr': r.stderr}
def main():
    roots = [BASE / x for x in ['fresh-analytic-discovery-r133', 't088p133-proof-r1', 't088p133-proof-r2', 't088p133-proof-r3']]
    before = {str(p): snapshot(p) for p in roots}
    for rel, h in ANCHORS.items(): assert sha(REVIEW / rel) == h, rel
    assert sha(REVIEW/'packet/public/review.md') == '953ecc91d19c5a7e5d6f6b2de3b9d4f7460a74289550834bb05a142378870635'
    assert sha(REVIEW/'packet/public/verdict.json') == 'c4659d34230aacc61764c69fd03eb84d068143d3ccc6637a7f8d7fc2c8e4b90c'
    result = {'anchors': ANCHORS, 'kind': 'PARENT_REPLAY_NOT_FULL_ANALYTIC_OR_FORMAL_PROOF'}
    with tempfile.TemporaryDirectory(prefix='copy-', dir=HERE) as td:
        copy = Path(td)/'review'; copy.mkdir()
        shutil.copytree(REVIEW/'packet', copy/'packet')
        for rel in ['FINAL.json', 'REPORT.md']: shutil.copy2(REVIEW/rel, copy/rel)
        baseline = snapshot(copy)
        spec = importlib.util.spec_from_file_location('parent_readonly_review_verifier', copy/'packet/public/verify.py')
        v = importlib.util.module_from_spec(spec); spec.loader.exec_module(v)
        anchors = list(ANCHORS.values())
        result['verification'] = v.verify(copy, *anchors, PROJECT)
        result['controls'] = []
        def case(name, expected, mutation=None, anchor_values=None, originals=PROJECT):
            c = Path(td)/name; shutil.copytree(copy, c)
            if mutation: mutation(c)
            state = snapshot(c)
            try:
                v.verify(c, *(anchor_values or anchors), originals)
                accepted = True
            except (ValueError, KeyError, OSError, json.JSONDecodeError): accepted = False
            assert accepted == expected, name
            assert snapshot(c) == state, name+' verifier wrote copy'
            result['controls'].append({'case': name, 'accepted': accepted, 'as_expected': True, 'copy_unchanged': True})
        case('baseline', True)
        case('wrong_final_anchor', False, anchor_values=['0'*64, *anchors[1:]])
        for label, rel in [('final', 'FINAL.json'), ('manifest', 'packet/MANIFEST.json'), ('outside_report', 'REPORT.md'), ('review', 'packet/public/review.md'), ('private_body', 'packet/private/upstream/preprints/A-product-counterexample-to-the-simplex-maximum-for-projection-body-volume-September-24-2026/build/main.tex')]:
            case('modified_'+label, False, lambda c, rel=rel: (c/rel).write_bytes((c/rel).read_bytes()+b'\nTAMPER\n'))
        case('deleted_payload', False, lambda c: (c/'packet/public/verdict.json').unlink())
        case('extra_payload', False, lambda c: (c/'packet/public/EXTRA').write_text('extra\n'))
        case('extra_empty_directory', False, lambda c: (c/'packet/EXTRA').mkdir())
        def linked(c):
            p=c/'packet/public/review.md'; p.unlink(); p.symlink_to(c/'packet/public/verdict.json')
        case('linked_payload', False, linked)
        def forged(c):
            p=c/'packet/public/review.md'; p.write_text('locally forged\n')
            m=json.loads((c/'packet/MANIFEST.json').read_text());m['files']['packet/public/review.md'].update(bytes=p.stat().st_size,sha256=sha(p))
            (c/'packet/MANIFEST.json').write_text(json.dumps(m))
            f=json.loads((c/'FINAL.json').read_text());f.update(manifest_sha256=sha(c/'packet/MANIFEST.json'),review_sha256=sha(p))
            (c/'FINAL.json').write_text(json.dumps(f))
        case('forged_local_reseal', False, forged)
        originals=Path(td)/'copied-originals'; originals.mkdir()
        bindings=json.loads((copy/'packet/private/original-bindings-start.json').read_text())
        for rel, m in bindings.items():
            target=originals/rel
            if m['type']=='dir': target.mkdir(parents=True,exist_ok=True);target.chmod(m['mode'])
            else: target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(PROJECT/rel,target)
        first=next(rel for rel,m in bindings.items() if m['type']=='file')
        (originals/first).write_bytes((originals/first).read_bytes()+b'\nCOPIED TAMPER\n')
        case('changed_copied_original',False,originals=originals)
        output=Path(td)/'certificate-witness.json'
        result['recurrence']=run([sys.executable,'-B',str(copy/'packet/public/independent_certificate.py'),str(output)])
        witness=json.loads(output.read_text())
        assert witness==json.loads((copy/'packet/public/certificate-witness.json').read_text())
        result['exact_crosscheck']=run([sys.executable,'-B',str(copy/'packet/public/crosscheck.py')])
        for w in witness:
            k,l,z=w['pattern'];assert k+l+z==4
            terms={tuple(e):c for e,c in w['T']};assert terms and all(c>0 for c in terms.values())
            e=[0]*(k+l);e[k-1]=2*k*l+1;assert terms[tuple(e)]>0
        result['ten_patterns_and_pure_positive_endpoint_witnesses']=True
        assert snapshot(copy)==baseline
    acquisitions=json.loads((REVIEW/'packet/private/acquisition.json').read_text())
    tree=json.loads((PROJECT/'sources/preprints-tree.json').read_text())
    assert len(tree['tree'])==13223 and not tree['truncated']
    assert sha(PROJECT/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    canonical={x['path']:x for x in tree['tree']};source_count=0
    pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
    for a in acquisitions:
        p=REVIEW/a['path'];assert sha(p)==a['sha256']
        if '/'+pin+'/' in a['url']:
            rel=a['url'].split('/'+pin+'/')[1];body=p.read_bytes();t=canonical[rel]
            assert len(body)==t['size'] and hashlib.sha1(b'blob '+str(len(body)).encode()+b'\0'+body).hexdigest()==t['sha']==a['git_blob'];source_count+=1
    result.update(canonical_source_bodies=source_count, acquisition_records=len(acquisitions), packet_payloads=48, copied_controls=len(result['controls']), original_bindings=len(bindings),original_file_bindings=sum(x['type']=='file' for x in bindings.values()))
    result['original_roots_unchanged']={str(p):snapshot(p)==before[str(p)] for p in roots}
    assert all(result['original_roots_unchanged'].values())
    result['coverage_limits']='Sealed packet bytes and exact packet path sets plus94 actual-original bindings/layouts; outside work/notes unsealed, payload modes/hardlink counts not authenticated by original verifier. Parent complete root snapshots confirm current preservation, not historical reading or syscall denial. Exact recurrence/crosscheck does not replace the independent analytic review or Lean formalization.'
    result['all_expected']=True
    (HERE/'replay.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['all_expected','packet_payloads','copied_controls','canonical_source_bodies','acquisition_records','original_bindings','original_file_bindings','ten_patterns_and_pure_positive_endpoint_witnesses']}))
if __name__=='__main__': main()
