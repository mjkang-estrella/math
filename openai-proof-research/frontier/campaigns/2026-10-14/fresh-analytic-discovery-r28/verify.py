#!/usr/bin/env python3
"""Offline read-only exact-membership verifier. Original code Myeongjin Kang, MIT.
Integrity/finite diagnostics only; not a mathematical or contribution verdict.
"""
import argparse,hashlib,json,pathlib,subprocess,sys
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
ROOT=pathlib.Path(__file__).resolve().parent

def sha(b):return hashlib.sha256(b).hexdigest()
def fail(message):raise ValueError(message)
def relfile(s):
    p=pathlib.PurePosixPath(s)
    if p.is_absolute() or '..' in p.parts or not p.parts:fail('invalid relative path')
    return ROOT.joinpath(*p.parts)
def read_json(s):return json.loads(relfile(s).read_bytes())

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--anchor',required=True);args=ap.parse_args()
    raw=(ROOT/'output-manifest.json').read_bytes()
    if sha(raw)!=args.anchor:fail('external manifest anchor mismatch')
    manifest=json.loads(raw)
    if manifest['source_pin']!=PIN:fail('source pin mismatch')
    files={};dirs=[]
    for p in ROOT.rglob('*'):
        if p.is_symlink():fail('symlink disallowed: '+str(p))
        s=p.relative_to(ROOT).as_posix()
        if p.is_dir():dirs.append(s)
        elif p.is_file() and s!='output-manifest.json':files[s]=sha(p.read_bytes())
    if sorted(dirs)!=manifest['directories']:fail('directory membership mismatch')
    if files!=manifest['files']:fail('file membership or digest mismatch')
    inputs=read_json('input-bindings.json')
    for r in inputs:
        if sha(relfile(r['snapshot']).read_bytes())!=r['sha256']:fail('input binding mismatch')
    trees=[r for r in inputs if r['original_path']=='sources/preprints-tree.json']
    if len(trees)!=1:fail('tree binding missing')
    tree=json.loads(relfile(trees[0]['snapshot']).read_bytes())
    if tree.get('truncated',False) or len(tree['tree'])!=13223:fail('incomplete preprint inventory')
    blobs={r['path']:r['sha'] for r in tree['tree'] if r['type']=='blob'}
    sources=read_json('source-receipts.json')
    for r in sources:
        b=relfile(r['local']).read_bytes()
        blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        if sha(b)!=r['sha256'] or blob!=r['git_blob'] or blobs.get(r['path'])!=blob:fail('pinned blob mismatch')
        if r['url']!='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+r['path']:fail('raw URL pin mismatch')
    freeze=read_json('freeze-receipt.json')
    for s,d in freeze['files'].items():
        if sha(relfile(s).read_bytes())!=d:fail('frozen scope/chronology changed')
    primary=read_json('primary-receipts.json')
    for r in primary:
        p=relfile(r['local'])
        if sha(p.read_bytes())!=r['sha256']:fail('primary PDF binding mismatch')
        text=p.with_suffix('.txt').read_bytes()
        proc=subprocess.run(['pdftotext','-layout',str(p),'-'],capture_output=True,check=True)
        if proc.stdout!=text:fail('PDF extraction replay mismatch: '+r['local'])
    proc=subprocess.run([sys.executable,'-B',str(ROOT/'diagnostics.py')],capture_output=True,text=True,check=True)
    if json.loads(proc.stdout)!=read_json('diagnostics-result.json'):fail('finite diagnostic replay mismatch')
    if files.get('original-scope.md')!=manifest['scope_sha256'] or files.get('candidate.md')!=manifest['candidate_sha256']:fail('scope/proof pointers mismatch')
    print(json.dumps({'status':'verified identity and finite diagnostics only','external_anchor':args.anchor,'payloads':len(files),'directories':len(dirs),'pinned_source_blobs':len(sources),'primary_pdfs':len(primary),'input_snapshots':len(inputs),'candidate_sha256':manifest['candidate_sha256'],'scope_sha256':manifest['scope_sha256']},indent=2))
if __name__=='__main__':
    try:main()
    except Exception as e:
        print('VERIFICATION FAILED: '+str(e),file=sys.stderr);sys.exit(1)
