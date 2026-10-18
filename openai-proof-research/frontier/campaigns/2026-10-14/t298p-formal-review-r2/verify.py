#!/usr/bin/env python3
"""Read-only external-anchor, payload and recorded-evidence verification.

This does not run Lean, rebuild dependencies or certify the analytic theorem.
"""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re

HERE=Path(__file__).resolve().parent
STANDARD={'propext','Classical.choice','Quot.sound'}
AUTHOR_NAMES={
 'T298P.coefficient_isometry','T298P.leading_score_energy',
 'T298P.gap_transfer','T298P.strict_gap',
 'T298PControls.wrong_normalization','T298PControls.missing_comparison',
 'T298PControls.wrong_gap_sign','T298PControls.equality_errors_not_strict'}
REVIEW_NAMES={'T298PReview.'+n for n in [
 'real_column_gram','nonorthogonal','nonorthogonal_isometry','positive_energy',
 'zero_epsilon_total_division','bad_gram_changes_energy','nonvacuous_strict_gap',
 'endpoint_is_needed','reversed_gap_is_false','weak_error_allows_equality']}
NEGATIVE={'denominator-k2','no-column-gram','no-endpoint','reversed-gap','weak-error'}

def require(condition,message):
    if not condition: raise ValueError(message)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def payload(root,anchor,reject_all_symlinks=False):
    require(re.fullmatch('[0-9a-f]{64}',anchor),'invalid anchor')
    require(sha(root/'MANIFEST.json')==anchor,'manifest anchor mismatch: '+str(root))
    files=json.loads((root/'MANIFEST.json').read_text())['files']
    entries=list(root.rglob('*'))
    if reject_all_symlinks:
        require(not any(p.is_symlink() for p in entries),'symlink in review payload')
    actual={p.relative_to(root).as_posix() for p in entries if p.is_file()}
    require(actual==set(files)|{'MANIFEST.json'},'payload membership mismatch: '+str(root))
    for name,digest in files.items():
        rel=PurePosixPath(name)
        require(not rel.is_absolute() and '..' not in rel.parts and str(rel)==name,'unsafe manifest name')
        p=root/name
        require(not p.is_symlink() and p.resolve().is_relative_to(root),'unsafe payload file')
        require(sha(p)==digest,'payload digest mismatch: '+name)

def receipt(where,status,expected_names,expected_steps,sources,negatives=False):
    r=json.loads((where/'receipt.json').read_text())
    require(r['status']==status,'wrong receipt status')
    require(r['full_theorem_formalized'] is False,'full-theorem claim')
    require(r['network_used'] is False,'network receipt mismatch')
    require(set(r['kernel_dependencies'])==expected_names,'declaration-name mismatch')
    for axioms in r['kernel_dependencies'].values():
        require(set(axioms)<=STANDARD,'nonstandard recorded axiom')
    require(set(r['sources'])==set(sources),'compiled source-name mismatch')
    for name,path in sources.items():
        require(sha(path)==r['sources'][name],'compiled source hash mismatch: '+name)
    require({row['step'] for row in r['runs']}==expected_steps and len(r['runs'])==len(expected_steps),'build step mismatch')
    for row in r['runs']:
        require(row['exit_code']==0,'recorded failed positive build')
        require(sha(where/(row['step']+'.log'))==row['output_sha256'],'positive log mismatch')
    if negatives:
        require(r['independent_review'] is True,'missing independent flag')
        rows=r['expected_rejections']
        require(len(rows)==5 and {x['step'] for x in rows}==NEGATIVE,'negative step mismatch')
        for row in rows:
            log=where/(row['step']+'.log')
            require(row['exit_code']!=0 and 'error:' in log.read_text(),'negative control not rejected')
            require(sha(log)==row['output_sha256'],'negative log mismatch')
    return r

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--anchor',required=True)
    p.add_argument('--repo',required=True,type=Path)
    a=p.parse_args();repo=a.repo.resolve()
    payload(HERE,a.anchor,True)
    b=json.loads((HERE/'binding.json').read_text())
    require(b['full_theorem_formalized'] is False,'incorrect binding coverage')
    for ref in b['references']:
        require(sha(repo/ref['path'])==ref['sha256'],'bound reference mismatch: '+ref['path'])
    author=repo/b['author_package']['path']
    payload(author,b['author_package']['manifest_sha256'])
    for ref in json.loads((author/'binding.json').read_text())['references']:
        require(sha(repo/ref['path'])==ref['sha256'],'author reference mismatch: '+ref['path'])
    for path in (HERE/'copied-author').iterdir():
        require(sha(path)==sha(author/path.name),'author copy mismatch: '+path.name)
    sources={n:HERE/'copied-author'/n for n in ['T298P.lean','Controls.lean']}
    fresh=receipt(HERE/'fresh-build','PASS_SCOPED_SOURCE_BUILD_TYPES_AND_STANDARD_AXIOMS',AUTHOR_NAMES,
                  {'support','controls','types-axioms'},sources)
    independent=receipt(HERE/'independent-build','PASS_INDEPENDENT_SCOPED_AUDIT_BUILD_AND_SENSITIVITY',AUTHOR_NAMES|REVIEW_NAMES,
                        {'T298P','Controls','Independent','types-axioms'},dict(sources,**{'Independent.lean':HERE/'Independent.lean'}),True)
    require(fresh['dependencies']==independent['dependencies'],'dependency revision mismatch')
    require(fresh['lean_version']==independent['lean_version'] and fresh['lean_binary_sha256']==independent['lean_binary_sha256'],'compiler mismatch')
    v=json.loads((HERE/'verdict.json').read_text())
    require(v['verdict']=='PASS' and v['required_findings']==[],'verdict mismatch')
    require(v['full_theorem_formalized'] is False and v['acceptance_claimed'] is False and v['count_credit_claimed'] is False,'scope overclaim')
    print('PASS: external anchor, exact review/author payloads, bound references, 8/18 theorem receipts, 5 expected rejections; scoped support only')

if __name__=='__main__':main()
