#!/usr/bin/env python3
"""Preparation-only clean-tree/negative controls; never awards the final gate. Myeongjin Kang 2026; MIT."""
import argparse
from pathlib import Path
import stat
import subprocess
import sys
import tempfile
import warnings
import zipfile
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import release_common as c
from assemble import build_contents
from reproduce_finite import reproduce
from verify_bundle import extract_checked, verify_tree
from rebuild_lean import rebuild


def checks(lean=None, cache=None):
    root = c.ROOT
    payload = c.frozen_selection(root)
    owned = c.owned_selection(root)
    reports = []
    def passed(label):
        reports.append({'check': label, 'status': 'PASS'})
    def rejects(label, fn):
        try:
            fn()
        except (ValueError, FileExistsError):
            passed(label)
        else:
            raise ValueError('Negative case was accepted: ' + label)
    passed('130 selected snapshots: exact lengths/hashes, trust anchors, historical output membership, exact formal manuscript snapshot')
    for path in ['../x', '/x', 'a/../x', 'a//x', './a', 'a\\x', 'a/', 'C:/x', 'a\nb', 'a\x7fb']:
        rejects('reject unsafe path ' + repr(path), lambda p=path: c.name(p))
    rejects('reject duplicate JSON keys', lambda: c.decode(b'{"x":1,"x":2}'))
    row = c.record('review.md', b'actual bytes')
    rejects('reject duplicate manifest entries', lambda: c.rows_map([row, row]))
    rejects('reject normalized relative/project manifest aliases', lambda: c.manifest_rows(
        c.encode([row, dict(row, path=c.REVIEW+'/review.md')]), c.REVIEW))
    rejects('reject ambiguous files/outputs manifest', lambda: c.manifest_rows(
        c.encode({'files': [], 'outputs': []}), c.REVIEW))
    rejects('reject boolean byte length', lambda: c.valid_record(dict(row, bytes=True)))
    # Real reviewed members exercise the same parser used by the later final gate.
    real = c.manifest_rows(c.selected(root, c.FORMAL_REVIEW+'/output-manifest.json'), c.FORMAL_REVIEW)
    c.require(real[c.FORMAL_REVIEW+'/review.md'] == payload[c.FORMAL_REVIEW+'/review.md'], 'Real membership mismatch')
    passed('actual scoped review manifest membership authenticates actual review artifact')
    with tempfile.TemporaryDirectory(prefix='.PREPARATION_ONLY-', dir=c.HERE) as d:
        work = Path(d)
        # This archive has no approving gate or invented reviewer identity.
        rows = {**payload, **owned}
        contents = {p:c.selected(root,p) for p in payload}
        contents.update({p:c.read(root,p) for p in owned})
        contents['BUNDLE-MANIFEST.json'] = c.encode({
            'schema':'staircase-preparation-transport-v1', 'kind':'PREPARATION_ONLY_NOT_FINAL',
            'final_manuscript_gate':'pending', 'files':[rows[p] for p in sorted(rows)]})
        first, second = work/'PREPARATION_ONLY-a.zip', work/'PREPARATION_ONLY-b.zip'
        c.archive_write(first, contents); c.archive_write(second, contents)
        c.require(first.read_bytes()==second.read_bytes(), 'Nondeterministic writer')
        passed('deterministic ZIP bytes for identical explicitly labeled preparation transport')
        original = first.read_bytes()
        rejects('reject existing ZIP destination', lambda: c.archive_write(first, contents))
        c.require(first.read_bytes()==original, 'Existing archive modified')
        dest = work/'clean'; dest.mkdir()
        extract_checked(c.archive_read(first),dest)
        c.require(c.frozen_selection(dest)==payload and c.owned_selection(dest)==owned, 'Clean selection differs')
        passed('clean extracted preparation tree: exact selected and owned inventories/hashes')
        rejects('production verifier rejects preparation archive kind', lambda: verify_tree(dest,'0'*64))
        # Execute the actual complete frozen scoped review verifier from arbitrary extraction.
        process = subprocess.run([sys.executable,'-I',str(dest/c.FORMAL_REVIEW/'verify_review.py')],
                                 cwd=work,capture_output=True,text=True,timeout=60)
        c.require(process.returncode==0, process.stderr)
        passed('actual default frozen formal-review verifier passes in clean extracted tree')
        finite = reproduce(dest)
        passed('clean extraction: two full historical finite outputs and 3072 interface controls reproduce')
        # Run the historical runner against a wrong expected receipt to ensure mismatch is rejected.
        expected = dest/c.PAPER/'checks/expected-proof_controls.json'
        expected.write_bytes(expected.read_bytes()+b'\n')
        process = subprocess.run([sys.executable,'-I',str(dest/c.PAPER/'support/reproduce.py')],
                                 cwd=work,capture_output=True,text=True,timeout=180)
        c.require(process.returncode!=0 and 'differs from frozen expected output' in process.stderr,
                  'Corrupt expected finite receipt was accepted')
        passed('finite reproduction rejects altered expected receipt')
        expected.write_bytes(contents[c.PAPER+'/checks/expected-proof_controls.json'])
        # Copy runner wrote reproduction.json; restore historical bytes before integrity checks.
        (dest/c.PAPER/'checks/reproduction.json').write_bytes(contents[c.PAPER+'/checks/reproduction.json'])
        paper = dest/c.PAPER/'main.tex'; actual = paper.read_bytes()
        paper.write_bytes(actual+b'\n')
        rejects('reject changed frozen manuscript bytes',lambda:c.frozen_selection(dest))
        paper.write_bytes(actual)
        paper.unlink(); paper.symlink_to(work/'not-a-payload-file')
        rejects('reject payload file symlink',lambda:c.frozen_selection(dest))
        paper.unlink(); paper.write_bytes(actual)
        component=dest/c.PAPER/'support'; moved=work/'moved-support'; component.rename(moved); component.symlink_to(moved,target_is_directory=True)
        rejects('reject payload directory symlink',lambda:c.frozen_selection(dest))
        component.unlink(); moved.rename(component)
        formal_log=dest/c.FORMAL_REVIEW/'logs/review-types.log'; original_log=formal_log.read_bytes(); formal_log.write_bytes(original_log+b'\n')
        process = subprocess.run([sys.executable,'-I',str(dest/c.FORMAL_REVIEW/'verify_review.py')],
                                 cwd=work,capture_output=True,text=True,timeout=60)
        c.require(process.returncode!=0 and 'hash mismatch' in process.stderr,'Corrupt formal log accepted')
        passed('actual frozen formal verifier rejects altered compiler log')
        formal_log.write_bytes(original_log)
        pending=c.decode(c.read(root,c.RELEASE+'/gate-pending.json'))
        gp=c.PARENT+'/PREPARATION_ONLY-manuscript-negative-gate.json'
        (dest/gp).parent.mkdir(parents=True,exist_ok=True); (dest/gp).write_bytes(c.encode(pending))
        rejects('production assembler rejects pending manuscript gate',lambda:build_contents(dest,gp,'0'*64))
        changed=dict(pending,state='integrated',bound_paper=dict(c.FROZEN))
        changed['bound_paper'][c.PAPER+'/main.tex']='0'*64
        (dest/gp).write_bytes(c.encode(changed))
        rejects('reject gate bound to wrong paper hash',lambda:c.gate_records(dest,gp,'0'*64))
        # An ACTUAL scoped-formal PASS is insufficient for the full manuscript gate.
        pp=c.PARENT+'/PREPARATION_ONLY-manuscript-wrong-scope-disposition.json'
        pd=c.selected(root,c.PARENT+'/formal-review-disposition.json'); (dest/pp).write_bytes(pd)
        insufficient={'schema':'staircase-release-gate-v1','state':'integrated', 'bound_paper':c.FROZEN,
                      'parent_disposition':c.record(pp,pd)}
        (dest/gp).write_bytes(c.encode(insufficient))
        rejects('reject parent disposition not matching independent trusted digest',lambda:c.gate_records(dest,gp,'0'*64))
        rejects('reject actual scoped-formal PASS used as full manuscript PASS',lambda:c.gate_records(dest,gp,c.sha(pd)))
        # Ensure prerequisites and original runner path setup are portable on clean selected extraction.
        setup_result = None
        if lean is not None and cache is not None:
            setup_result = rebuild(dest,lean,cache,True)
            passed('clean extraction: pinned compiler/all nine pins and copied independent runner path setup, no fresh compilation')
        for label,filename,make in [
            ('duplicate','duplicate.zip',lambda z:(z.writestr('x',b'a'),z.writestr('x',b'b'))),
            ('traversal','traversal.zip',lambda z:z.writestr('../escape',b'a')),
            ('symlink','symlink.zip',lambda z:write_symlink(z))]:
            path=work/filename
            with warnings.catch_warnings():
                warnings.simplefilter('ignore',UserWarning)
                with zipfile.ZipFile(path,'w') as z:
                    make(z)
            rejects('reject ZIP '+label,lambda p=path:c.archive_read(p))
        extra=dict(contents,UNREVIEWED=b'not allowed')
        bad=work/'extra'; bad.mkdir()
        rejects('reject archive with unlisted extra file',lambda:extract_checked(extra,bad))
        altered=dict(contents); altered[c.PAPER+'/main.tex']=b'altered'
        bad2=work/'altered'; bad2.mkdir()
        rejects('reject ZIP selected-byte corruption',lambda:extract_checked(altered,bad2))
    return {'schema':'staircase-preparation-checks-v1','status':'PASS: preparation checks only',
            'checks':reports,'checks_passed':len(reports),'selected_files':len(payload),
            'finite_reproduction':finite,'lean_setup':setup_result,
            'actual_manuscript_gate_tested':False,'final_integrated_end_to_end_pass':False,
            'test_archives':'PREPARATION_ONLY_NOT_FINAL; removed with disposable tree',
            'full_staircase_formalization':False,'acceptance_awarded':False,'count_change':0}


def write_symlink(z):
    info=zipfile.ZipInfo('link'); info.create_system=3; info.external_attr=(stat.S_IFLNK|0o777)<<16
    z.writestr(info,b'/outside')


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--lean',type=Path); p.add_argument('--cache',type=Path)
    p.add_argument('--record',action='store_true',help='Write preparation-checks.json after tests; parent must refresh output manifest')
    a=p.parse_args(); c.require((a.lean is None)==(a.cache is None),'Supply both --lean and --cache or neither')
    result=checks(a.lean,a.cache)
    if a.record:
        (c.HERE/'preparation-checks.json').write_bytes(c.encode(result))
    print(c.encode(result).decode(),end='')
