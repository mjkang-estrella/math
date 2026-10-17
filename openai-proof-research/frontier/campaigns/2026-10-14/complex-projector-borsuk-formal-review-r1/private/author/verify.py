#!/usr/bin/env python3
"""Copyright 2026 Myeongjin Kang. MIT. Externally anchored identity verification only."""
import argparse,hashlib,json
from pathlib import Path,PurePosixPath

def require(ok,message):
    if not ok: raise ValueError(message)

def digest(data): return hashlib.sha256(data).hexdigest()

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--anchor',required=True,help='SHA256 of output-manifest.json, supplied independently')
    ap.add_argument('--check-inputs',action='store_true',help='Also check fixed external campaign inputs')
    args=ap.parse_args();root=Path(__file__).resolve().parent
    raw=(root/'output-manifest.json').read_bytes()
    require(digest(raw)==args.anchor,'external manifest anchor mismatch')
    manifest=json.loads(raw);expected={}
    for item in manifest['files']:
        name=item['path'];p=PurePosixPath(name)
        require(str(p)==name and not p.is_absolute() and '..' not in p.parts,'noncanonical path')
        require(name!='output-manifest.json' and name not in expected,'duplicate/reserved path')
        require(p.parts[0]!='.replays','replay output is not sealed input')
        expected[name]=item
    actual=set();dirs=set()
    for path in root.rglob('*'):
        rel=path.relative_to(root)
        require(not path.is_symlink(),'symlink is not permitted')
        if rel.parts[0]=='.replays': continue
        if path.is_dir(): dirs.add(rel.as_posix())
        else:
            require(path.is_file(),'special file')
            if rel.as_posix()!='output-manifest.json': actual.add(rel.as_posix())
    require(actual==set(expected),'exact file membership mismatch')
    require(dirs==set(manifest['directories']),'exact directory membership mismatch')
    for name,item in expected.items():
        b=(root/name).read_bytes();require(len(b)==item['bytes'] and digest(b)==item['sha256'],'changed payload: '+name)
    source_hash=digest((root/'BorsukLocal.lean').read_bytes())
    for run in ['first-build','clean-rebuild']:
        receipt=json.loads((root/'logs'/run/'receipt.json').read_text())
        require(receipt['status'].startswith('PASS '),'build did not pass')
        require(receipt['source_sha256']['BorsukLocal.lean']==source_hash,'build/source mismatch')
        require(receipt['full_B8C_theorem_formalized'] is False,'scope flag changed')
    mutation=json.loads((root/'logs/mutations/receipt.json').read_text())
    require(mutation['source_sha256']==source_hash and len(mutation['cases'])==5,'mutation/source mismatch')
    require(all(x['result']=='EXPECTED_PROOF_REJECTION' for x in mutation['cases']),'bad mutation control')
    if args.check_inputs:
        for item in json.loads((root/'input-manifest.json').read_text()):
            b=(root/item['path']).read_bytes();require(len(b)==item['bytes'] and digest(b)==item['sha256'],'external input changed: '+item['path'])
    print(json.dumps({'status':'PASS integrity only','payloads':len(expected),'external_inputs_checked':args.check_inputs,
                      'replay_outputs_excluded':True,'full_B8C_formalized':False,'count_change':0}))

if __name__=='__main__':
    try: main()
    except (ValueError,OSError,KeyError,TypeError) as error: raise SystemExit('REJECT: '+str(error))
