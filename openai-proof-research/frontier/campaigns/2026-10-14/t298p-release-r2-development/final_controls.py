#!/usr/bin/env python3
"""Actual-r4 gate and final-archive controls. MIT, Myeongjin Kang.
Semantic rejection fixtures are ephemeral in-memory mutations of the actual r4
schema, never a substituted real review or fabricated acceptance artifact.
"""
import argparse
import copy
import json
from pathlib import Path
import subprocess
import sys

HERE=Path(__file__).absolute().parent
ns={'__file__':str(HERE/'release.py'),'__name__':'final_controls_import'}
exec(compile((HERE/'release.py').read_bytes(),str(HERE/'release.py'),'exec'),ns)
r=type('Release',(),ns)

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--prepared',type=Path,required=True)
    p.add_argument('--preparation-anchor',required=True)
    p.add_argument('--final',type=Path,required=True)
    p.add_argument('--anchor',required=True)
    p.add_argument('--review',type=Path,required=True)
    p.add_argument('--review-anchor',required=True)
    p.add_argument('--policy',type=Path,required=True)
    p.add_argument('--policy-anchor',required=True)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    out=r.new_output(a.output,[a.prepared,a.final,a.review,a.policy.parent]);out.mkdir()
    mf,payload=r.verify(a.final/'payload',a.anchor)
    raw=a.policy.read_bytes();policy=r.parse(raw)
    original={'MANIFEST.json':r.read(a.review,'MANIFEST.json')}
    original.update({name:r.read(a.review,name) for name in policy['include']})
    r.review_gate(original.__getitem__,a.review_anchor,raw,a.policy_anchor)
    rows=[{'control':'actual-r4-PASS-empty-required-active-r2','status':'PASS'}]
    def reject(label,fn,expected=None):
        try:fn()
        except (ValueError,OSError,KeyError) as error:
            if expected:assert expected in str(error),(label,str(error))
            rows.append({'control':label,'status':'EXPECTED_REJECTION','reason':str(error)})
        else:raise AssertionError('accepted '+label)
    # Rebind ephemeral test manifests to deliberately changed verdicts so tests
    # reach semantic checks instead of merely failing the outer hash first.
    def changed(field,value):
        fixture=dict(original);verdict=r.parse(fixture['verdict.json']);verdict[field]=value
        fixture['verdict.json']=r.encoded(verdict)
        manifest=r.parse(fixture['MANIFEST.json']);manifest['files']['verdict.json']=r.record(fixture['verdict.json'])
        fixture['MANIFEST.json']=r.encoded(manifest)
        pol=copy.deepcopy(policy);pol['review_anchor']=r.sha(fixture['MANIFEST.json'])
        policy_bytes=r.encoded(pol)
        return lambda:r.review_gate(fixture.__getitem__,pol['review_anchor'],policy_bytes,r.sha(policy_bytes))
    reject('required-findings-nonempty',changed('required',[{'id':'BLOCKER'}]),'required findings')
    reject('required-count-zero-is-not-array',changed('required',0),'required findings')
    reject('required-null-is-not-array',changed('required',None),'required findings')
    reject('required-false-is-not-array',changed('required',False),'required findings')
    reject('real-schema-mutated-NEEDS_REVISION',changed('verdict','NEEDS_REVISION'),'did not PASS')
    reject('wrong-PASS-scope',changed('verdict','PASS_SCOPED_SUPPORT'),'did not PASS')
    reject('old-r1-manuscript-binding',changed('manuscript_manifest_sha256','24a3e405e1bceda384a8b6a4e28f610809a4c9ec5b32b0a66e0277b24b2124fe'),'does not bind')
    reject('wrong-actual-review-anchor',lambda:r.review_gate(original.__getitem__,'0'*64,raw,a.policy_anchor))
    reject('wrong-actual-policy-anchor',lambda:r.review_gate(original.__getitem__,a.review_anchor,raw,'0'*64))
    linked=out/'linked-parent';linked.symlink_to(out,target_is_directory=True)
    reject('symlink-output-ancestor',lambda:r.new_output(linked/'child',[a.final]))
    # Repeat real assembly into disjoint scratch and require the identical archive.
    args=type('Args',(),dict(prepared=a.prepared,preparation_anchor=a.preparation_anchor,
        output=out/'repeat-final',manuscript_review=a.review,review_anchor=a.review_anchor,
        review_policy=a.policy,policy_anchor=a.policy_anchor))
    r.assemble(args)
    assert (out/'repeat-final/t298p-release.zip').read_bytes()==(a.final/'t298p-release.zip').read_bytes()
    assert (out/'repeat-final/payload/MANIFEST.json').read_bytes()==payload['MANIFEST.json']
    rows.append({'control':'actual-final-deterministic-repeated-assembly','status':'PASS'})
    # Additional selected finite diagnostics, explicitly not analytic proofs.
    for script,reference in [('paper/check_arithmetic.py','paper/validation/arithmetic.json'),('paper/check_pairing.py','paper/validation/pairing.json'),('reviews/manuscript/original/check_revised_score.py','reviews/manuscript/original/checks/revised-score.json')]:
        run=subprocess.run([sys.executable,'-I','-B',str(a.final/'payload'/script)],capture_output=True,text=True,check=True)
        assert not run.stderr
        assert r.parse(run.stdout)==r.parse(payload[reference]),script
        rows.append({'control':'finite-diagnostic:'+script,'status':'PASS','output_sha256':r.sha(run.stdout.encode())})
    r.verify(a.final/'payload',a.anchor)
    result={'status':'PASS_ACTUAL_FINAL_CONTROLS','manifest_sha256':a.anchor,
        'archive_sha256':r.sha((a.final/'t298p-release.zip').read_bytes()),'review_anchor':a.review_anchor,
        'policy_anchor':a.policy_anchor,'accepted':False,'published':False,'count_change':0,
        'full_theorem_formalized':False,'semantic_negative_fixture_scope':'ephemeral mutations of actual r4 verdict schema; no fake review retained',
        'controls':rows,'control_count':len(rows)}
    (out/'final-controls-receipt.json').write_bytes(r.encoded(result))
    print(json.dumps({'status':result['status'],'controls':len(rows)}))

if __name__=='__main__':main()
