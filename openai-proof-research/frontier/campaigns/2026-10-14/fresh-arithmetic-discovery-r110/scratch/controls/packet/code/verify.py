"""Read-only packet verifier. External anchors are required, never self-trusted."""
import argparse, hashlib, json, os, re
from pathlib import Path, PurePosixPath

ACTIVE = re.compile(r'h138-|analytic.*r13[89]|t185r144-|structural.*r14[45]', re.I)
BROAD = re.compile(r'arithmetic.*r10[789]|structural.*r143|t177c143-|analytic.*r13[567]|t373e135-|k369r134-|t088p133-', re.I)
OUTER = {'MANIFEST.json', 'FINAL.json', 'REPORT.md'}
TREE_SHA = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'

def digest(data): return hashlib.sha256(data).hexdigest()
def safe(name):
    p = PurePosixPath(name)
    assert name and not p.is_absolute() and '..' not in p.parts and str(p) == name, 'unsafe relative path'
    assert not any(ACTIVE.search(c) or BROAD.search(c) for c in p.parts), 'excluded component'
    return p

def inventory(root):
    """Reject forbidden names before descent/read; exclude only root scratch and outer files."""
    result = []
    for here, dirs, files in os.walk(root, followlinks=False):
        for name in list(dirs):
            q = Path(here)/name
            assert not q.is_symlink(), 'directory symlink'
            rel = q.relative_to(root).as_posix(); safe(rel)
            if rel == 'scratch': dirs.remove(name)
        for name in files:
            q = Path(here)/name
            rel = q.relative_to(root).as_posix(); safe(rel)
            assert not q.is_symlink() and q.is_file(), 'nonregular file'
            if rel not in OUTER: result.append(rel)
    return sorted(result)

def verify(root, anchors):
    assert root.is_dir() and not root.is_symlink(), 'bad root'
    for name in OUTER:
        q=root/name
        assert q.is_file() and not q.is_symlink(), 'outer missing/symlink'
        assert re.fullmatch('[0-9a-f]{64}', anchors[name]), 'invalid external anchor'
        assert digest(q.read_bytes()) == anchors[name], 'external anchor mismatch: '+name
    m=json.loads((root/'MANIFEST.json').read_text()); f=json.loads((root/'FINAL.json').read_text())
    assert m['schema']=='r110-exact-payload-v1' and m['excluded_root']=='scratch/'
    assert f['status']=='PREFREEZE/no nominee' and f['frozen_statement'] is None
    assert f['manifest_sha256']==anchors['MANIFEST.json'] and f['outside_report_sha256']==anchors['REPORT.md']
    entries=m['files']; names=[e['path'] for e in entries]
    assert names==sorted(set(names)) and names==inventory(root), 'exact membership mismatch'
    for e in entries:
        safe(e['path']); data=(root/e['path']).read_bytes()
        assert len(data)==e['bytes'] and digest(data)==e['sha256'], 'payload mismatch: '+e['path']
    treebytes=(root/'private/history/named-02.json').read_bytes()
    assert digest(treebytes)==TREE_SHA
    tree=json.loads(treebytes); assert not tree['truncated'] and len(tree['tree'])==13223
    indexed={e['path']:e for e in tree['tree']}
    count=0
    for file in ['private/source/metadata.json','private/source/kurosh-metadata.json']:
        for e in json.loads((root/file).read_text()):
            safe(e['local']); data=(root/e['local']).read_bytes(); t=indexed[e['canonical_path']]
            blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
            assert len(data)==e['bytes']==t['size'] and blob==e['git_blob_sha1']==t['sha']
            assert digest(data)==e['sha256']; count+=1
    assert count==34
    return {'artifact_integrity':'verified','payload_files':len(entries),'pinned_acquisitions':count,'mathematical_gate':False}

if __name__=='__main__':
    ap=argparse.ArgumentParser(); ap.add_argument('root',type=Path)
    for key in ['final','manifest','report']: ap.add_argument('--'+key+'-hash',required=True)
    a=ap.parse_args()
    try:
        print(json.dumps(verify(a.root,{'FINAL.json':a.final_hash,'MANIFEST.json':a.manifest_hash,'REPORT.md':a.report_hash}),sort_keys=True))
    except (AssertionError,ValueError,KeyError,OSError) as e:
        ap.exit(1,'REJECT: '+str(e)+'\n')
