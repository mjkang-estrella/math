#!/usr/bin/env python3
"""Artifact controls on isolated copies only. MIT, copyright 2026 Myeongjin Kang."""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import shutil

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
spec = importlib.util.spec_from_file_location('trusted_verifier', HERE/'verify.py')
v = importlib.util.module_from_spec(spec)
spec.loader.exec_module(v)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--final-sha256', required=True)
    ap.add_argument('--manifest-sha256', required=True)
    ap.add_argument('--report-sha256', required=True)
    a = ap.parse_args()
    out = a.output.resolve()
    v.require(out.is_relative_to(ROOT/'work'), 'controls must be under package-root/work')
    out.mkdir(parents=True, exist_ok=False)
    anchors = (a.final_sha256, a.manifest_sha256, a.report_sha256)
    # Authenticate the source before making copies; all later mutations target new copies.
    v.verify(ROOT, *anchors)
    results = []
    cases = {
        'clean': None,
        'changed_source': 'payload metadata/hash mismatch',
        'missing_source': 'packet path set mismatch',
        'extra_payload': 'packet path set mismatch',
        'changed_mode': 'payload metadata/hash mismatch',
        'symlink_payload': 'linked payload',
        'hardlink_payload': 'payload metadata/hash mismatch',
        'changed_final': 'external anchor mismatch: FINAL.json',
        'changed_manifest': 'external anchor mismatch: packet/MANIFEST.json',
        'changed_report': 'external anchor mismatch: REPORT.md',
        'forged_local_reseal': 'external anchor mismatch: FINAL.json',
    }
    for case, reason in cases.items():
        dst = out/case
        dst.mkdir()
        for f in ['FINAL.json','REPORT.md']:
            shutil.copy2(ROOT/f,dst/f)
        shutil.copytree(ROOT/'packet',dst/'packet')
        p = dst/'packet/public/T088P133.lean'
        if case == 'changed_source':
            p.write_bytes(p.read_bytes()+b'\n-- copied alteration\n')
        elif case == 'missing_source':
            p.unlink()
        elif case == 'extra_payload':
            (dst/'packet/EXTRA').write_text('copied addition\n')
        elif case == 'changed_mode':
            p.chmod(0o600)
        elif case == 'symlink_payload':
            backing = dst/'copied-body.lean'
            p.rename(backing)
            p.symlink_to('../../copied-body.lean')
        elif case == 'hardlink_payload':
            os.link(p,dst/'copied-hardlink.lean')
        elif case in ['changed_final','changed_manifest','changed_report']:
            q = dst/ {'changed_final':'FINAL.json','changed_manifest':'packet/MANIFEST.json',
                      'changed_report':'REPORT.md'}[case]
            q.write_bytes(q.read_bytes()+b'\n')
        elif case == 'forged_local_reseal':
            p.write_bytes(p.read_bytes()+b'\n-- copied alteration with reseal\n')
            mpath = dst/'packet/MANIFEST.json'
            m = json.loads(mpath.read_text())
            m['entries']['packet/public/T088P133.lean'] = v.record(p)
            mpath.write_text(json.dumps(m,indent=2)+'\n')
            fpath = dst/'FINAL.json'
            f = json.loads(fpath.read_text())
            f['manifest_sha256'] = v.sha(mpath)
            fpath.write_text(json.dumps(f,indent=2)+'\n')
        try:
            result = v.verify(dst,*anchors)
        except Exception as exc:
            message = str(exc)
            v.require(reason is not None and reason in message, 'unexpected rejection: '+case+': '+message)
            results.append({'case':case,'expected':'reject','observed_reason':message,'matched':True})
        else:
            v.require(reason is None,'tampered copy accepted: '+case)
            results.append({'case':case,'expected':'accept','matched':True,'result':result})
    v.verify(ROOT,*anchors)
    (out/'results.json').write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps({'cases':len(results),'all_matched':True,'results':str(out/'results.json')}))

if __name__ == '__main__':
    main()
