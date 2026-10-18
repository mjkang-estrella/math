"""Read-only identity/provenance verifier. Does not certify mathematical claims."""
import argparse, hashlib, json, re
from pathlib import Path
TREE='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
SCOPE='676eed9172e85a2c99a7ff52dbe911cae036c104dba0bb409a2b158e4791f29e'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
PREFIX='preprints/Cyclic-Length-and-Chromatic-Fixed-Point-Loss-September-24-2026/'
def sha(b):return hashlib.sha256(b).hexdigest()
def need(ok,reason):
    if not ok:raise ValueError(reason)
def verify(root,expected,tree):
    need(isinstance(expected,str) and re.fullmatch('[0-9a-f]{64}',expected),'EXPECTED_ANCHOR')
    raw=(root/'MANIFEST.json').read_bytes();need(sha(raw)==expected,'MANIFEST_ANCHOR');m=json.loads(raw)
    allpaths=list(root.rglob('*'));need(not any(x.is_symlink() for x in allpaths),'SYMLINK')
    actual={str(x.relative_to(root)) for x in allpaths if x.is_file()}-{'MANIFEST.json'}
    need(actual==set(m['files']),'FILE_MEMBERSHIP')
    dirs=sorted(str(x.relative_to(root)) for x in allpaths if x.is_dir());need(dirs==m['directories'],'DIRECTORY_MEMBERSHIP')
    for f,h in m['files'].items():
        need(not Path(f).is_absolute() and '..' not in Path(f).parts,'UNSAFE_PATH')
        need(sha((root/f).read_bytes())==h,'PAYLOAD_HASH')
    need(sha((root/'original-scope.md').read_bytes())==SCOPE,'SCOPE_ANCHOR')
    tb=tree.read_bytes();need(sha(tb)==TREE,'TREE_ANCHOR');t=json.loads(tb)
    need(t['truncated'] is False and len(t['tree'])==13223,'TREE_SHAPE')
    canon={x['path']:x for x in t['tree']};need(len(canon)==13223,'TREE_UNIQUE')
    sources=json.loads((root/'source-receipts.json').read_text())
    selected={x['path'] for x in t['tree'] if x['type']=='blob' and x['path'].startswith(PREFIX) and not x['path'].endswith('.pdf')}
    need(len(sources)==12 and {x['path'] for x in sources}==selected,'SOURCE_MEMBERSHIP')
    for x in sources:
        need(x['git_blob']==canon[x['path']]['sha'],'SOURCE_CANONICAL')
        need(x['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+x['path'],'SOURCE_URL')
        b=(root/x['copy']).read_bytes()
        need(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob'],'SOURCE_GIT')
        need(sha(b)==x['sha256'],'SOURCE_SHA')
    prim=json.loads((root/'primary-receipts.json').read_text())
    for x in prim:
        if 'private_pdf' in x:
            b=(root/x['private_pdf']).read_bytes();need(b.startswith(b'%PDF'),'PRIMARY_PDF')
            need(sha(b)==x['sha256'] and sha((root/x['private_text']).read_bytes())==x['text_sha256'],'PRIMARY_SHA')
        else:need(sha((root/x['private_copy']).read_bytes())==x['sha256'],'FAILED_RETRIEVAL_SHA')
    return {'identity':'verified','payloads':len(actual),'source_blobs':12,'primary_pdfs':3,'limits':'identity and provenance only; no proof, contribution, formal or acceptance verdict'}
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--expected',required=True);ap.add_argument('--tree',type=Path,required=True);ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);a=ap.parse_args()
    try:print(json.dumps(verify(a.root,a.expected,a.tree),sort_keys=True))
    except (ValueError,OSError,KeyError,json.JSONDecodeError) as e:print('REJECT: '+str(e));raise SystemExit(1)
