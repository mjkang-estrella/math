#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. MIT.
"""Assemble explicit original payloads only after an externally bound final gate."""
import argparse
from pathlib import Path
import sys
sys.dont_write_bytecode = True
import zipfile
from bundle_common import public_path, bound_anchors, check, directory_set, gate_check, parse, read, require, safe, sha
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE if (HERE / "frontier").is_dir() else HERE.parents[3]
OWN = ['README.md', 'RIGHTS.md', 'FORMAL-COVERAGE.md', 'REPRODUCTION.md',
       'bundle_common.py', 'verify_bundle.py', 'assemble.py', 'payload-selection.json',
       'PROVENANCE.txt', 'preparation.json', 'verify_preparation.py', 'release_checks.py',
       'selection-audit.json', 'preparation-checks.json', 'helper-adaptation.json', 'CORRECTIONS.md', 'verify_release_preparation.py', 'seal_controls.py']


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--gate',type=Path,required=True)
    p.add_argument('--gate-sha256',required=True)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    raw=a.gate.read_bytes();require(sha(raw)==a.gate_sha256,'external gate hash mismatch')
    gate=parse(raw);gate_check(gate)
    selection=parse((HERE/'payload-selection.json').read_bytes())
    payload={}
    for row in selection['files']+gate['artifacts']:
        name=row['path'];public_path(name);data=read(ROOT,name);check(data,row)
        require(name not in payload,'duplicate payload path: '+name);payload[name]=data
    for name in OWN:
        require(name not in payload,'duplicate release path');payload[name]=read(HERE,name)
    payload['FINAL-GATE.json']=raw
    bound_anchors(payload.__getitem__,gate)
    records=[dict(path=name,bytes=len(data),sha256=sha(data)) for name,data in sorted(payload.items())]
    manifest=dict(schema=1,scope='Reviewed local release; external publication not performed',
                  gate_sha256=a.gate_sha256,files=records,directories=sorted(directory_set(payload)))
    payload['BUNDLE-MANIFEST.json']=(json.dumps(manifest,indent=2)+'\n').encode()
    a.output.parent.mkdir(parents=True,exist_ok=True)
    with zipfile.ZipFile(a.output,'x',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as archive:
        for name,data in sorted(payload.items()):
            safe(name);info=zipfile.ZipInfo(name,date_time=(2026,10,18,0,0,0))
            info.compress_type=zipfile.ZIP_DEFLATED;info.external_attr=0o100644<<16
            archive.writestr(info,data)
    print(json.dumps(dict(archive=str(a.output.resolve()),bytes=a.output.stat().st_size,
                         sha256=sha(a.output.read_bytes()),manifest_sha256=sha(payload['BUNDLE-MANIFEST.json']),
                         gate_sha256=a.gate_sha256,files=len(payload)),indent=2))


if __name__=='__main__':
    try: main()
    except (OSError,ValueError,KeyError,TypeError) as exc:sys.exit('ASSEMBLY REFUSED: '+str(exc))
