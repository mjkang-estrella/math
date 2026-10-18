#!/usr/bin/env python3
"""Mutation controls on a full copied payload; external anchor required.
Copyright Myeongjin Kang. SPDX-License-Identifier: MIT
"""
import argparse,json,pathlib,runpy,shutil,tempfile

p=argparse.ArgumentParser();p.add_argument('--expected',required=True);a=p.parse_args()
root=pathlib.Path(__file__).resolve().parent
v=runpy.run_path(str(root/'verify_seal.py'),run_name='seal_library')
seal=json.loads((root.parent/'seal.json').read_text())
results=[]
with tempfile.TemporaryDirectory(prefix='r22-full-copy-',dir=root.parent) as tmp:
    copy=pathlib.Path(tmp)/'payload';shutil.copytree(root,copy)
    def run(name,expect_reject=False,expected=a.expected,use_seal=seal):
        try:v['verify'](copy,use_seal,expected)
        except ValueError:
            if not expect_reject:raise
            results.append({'case':name,'result':'EXPECTED_REJECTION'})
        else:
            if expect_reject:raise ValueError('mutation accepted: '+name)
            results.append({'case':name,'result':'PASS'})
    run('full_copy_positive')
    run('wrong_external_anchor',True,'0'*64)
    f=copy/'robust-ostmann-screen.md';data=f.read_bytes();f.write_bytes(data+b'\nmutation\n')
    run('changed_proof_bytes',True)
    forged=v['inventory'](copy)
    run('recomputed_seal_original_external_anchor',True,use_seal={'inventory':forged,'inventory_sha256':v['digest'](forged)})
    f.write_bytes(data)
    extra=copy/'unlisted';extra.write_text('extra');run('unlisted_file',True);extra.unlink()
    f.unlink();run('missing_proof_file',True);f.write_bytes(data)
    link=copy/'linked';link.symlink_to('checkpoint.md');run('symlink',True);link.unlink()
    run('restored_full_copy')
print(json.dumps({'status':'PASS','controls':results,'meaning':'exact-inventory integrity only; no mathematical acceptance'},indent=2))
