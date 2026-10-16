#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. MIT License.
"""Seal this independent review's exact noncircular output inventory."""
from pathlib import Path
import hashlib
import json

OWN=Path(__file__).resolve().parents[1]


def entry(p):
    data=p.read_bytes()
    return dict(path=p.relative_to(OWN).as_posix(),bytes=len(data),sha256=hashlib.sha256(data).hexdigest())


def main():
    unchanged=json.loads((OWN/'receipts/unchanged-inputs.json').read_text())
    assert unchanged['status']=='PASS_UNCHANGED' and unchanged['all_fixed_inputs_unchanged']
    for path in OWN.rglob('*'):
        assert not path.is_symlink(),path
        assert path.is_file() or path.is_dir(),path
        assert '__pycache__' not in path.parts,path
    excluded={'output-manifest.json','SHA256SUMS'}
    files=sorted((p for p in OWN.rglob('*') if p.is_file() and p.name not in excluded),key=lambda p:p.relative_to(OWN).as_posix())
    assert not any((OWN/'work').rglob('*')), 'Disposable test copies remain'
    manifest=dict(schema=1,scope='Independent manuscript revision review r2, exact file inventory',
                  excluded_from_this_manifest=['output-manifest.json','SHA256SUMS'],
                  rights='Original prose CC BY 4.0; original code MIT; third-party rights retained.',
                  verdict='PASS_REVISION',files=[entry(p) for p in files])
    (OWN/'output-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    all_entries=[entry(p) for p in files]+[entry(OWN/'output-manifest.json')]
    (OWN/'SHA256SUMS').write_text(''.join(r['sha256']+'  '+r['path']+'\n' for r in all_entries))
    # Read every sealed output back and check exact membership.
    loaded=json.loads((OWN/'output-manifest.json').read_bytes())
    assert {r['path'] for r in loaded['files']}|excluded=={p.relative_to(OWN).as_posix() for p in OWN.rglob('*') if p.is_file()}
    for r in loaded['files']:
        assert entry(OWN/r['path'])==r,r['path']
    print(json.dumps(dict(status='SEALED',payload_records=len(files),total_files=len(files)+2,
                         externally_report=[entry(OWN/name) for name in ['review.md','input-manifest.json','output-manifest.json']]),indent=2))


if __name__=='__main__':main()
