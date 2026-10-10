"""Offline READ-ONLY I116 verifier. No downloads, writes, caches, bytecode or resealing.
Integrity and finite diagnostics only, not proof/priority/contribution certification.
"""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import hashlib,json,runpy,re

ROOT=Path(__file__).resolve().parents[3]
S='frontier/sources/i116_robust_prophet_continuation'
E='frontier/experiments/i116_robust_prophet_continuation'
REPORT='frontier/iterations/i116-robust-prophet-continuation.md'
SEAL=S+'/seal.json'
OLD_S='frontier/sources/i113_online_optimization_discovery'
OLD_E='frontier/experiments/i113_online_optimization_discovery'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
DRIFT={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}


def require(c,msg):
    if not c:raise ValueError(msg)


def read(rel):
    p=Path(rel)
    require(not p.is_absolute() and '..' not in p.parts,'unsafe path '+rel)
    f=ROOT/p
    require(f.is_file() and not f.is_symlink(),'missing/nonregular '+rel)
    return f.read_bytes()


def sha(b):return hashlib.sha256(b).hexdigest()

def obj(p):return json.loads(read(p))

def checked(p,digest,size=None):
    b=read(p);require(sha(b)==digest,'hash mismatch '+p)
    if size is not None:require(len(b)==size,'byte count '+p)
    return b


def owned_paths():
    paths={REPORT}
    for root in [S,E]:
        for p in (ROOT/root).rglob('*'):
            require(not p.is_symlink(),'owned symlink '+str(p))
            if p.is_file():paths.add(str(p.relative_to(ROOT)))
    return paths


def inventory(seal,unsealed=False):
    require(seal['schema']=='i116-exact-owned-v1' and seal['pin']==PIN,'seal metadata')
    require(seal['roots']==[REPORT,S+'/',E+'/'],'seal roots')
    rows=seal['files'];paths=[d['path'] for d in rows]
    require(paths==sorted(set(paths)) and SEAL not in paths,'noncanonical seal inventory')
    expected=set(paths)|(set() if unsealed else {SEAL})
    require(owned_paths()==expected,'owned inventory mismatch '+str(sorted(owned_paths()^expected)))
    for d in rows:checked(d['path'],d['sha256'],d['bytes'])
    return {'owned_files_excluding_seal':len(rows),'seal_is_inventory_envelope':True}


def core():
    results={}
    inp=obj(S+'/inputs.json')
    require({d['original'] for d in inp if d['may_drift']}==DRIFT,'ledger drift allowlist')
    drift=[]
    for d in inp:
        checked(d['snapshot'],d['sha256'])
        if d['may_drift']:
            if sha(read(d['original']))!=d['sha256']:drift.append(d['original'])
        else:checked(d['original'],d['sha256'])
    require(obj('sources/upstream.json')['commit']==PIN,'source pin')
    results['snapshots']=len(inp);results['allowed_live_ledger_drift']=sorted(drift)

    # All inherited owned files, including executable code, are checked before loading it.
    refs=obj(S+'/inherited-references.json')
    require(len(refs)==50,'inherited inventory count')
    for d in refs:checked(d['path'],d['sha256'],d['bytes'])
    oldseal=obj(OLD_S+'/seal.json')
    expected={d['path'] for d in oldseal['files']}|{OLD_S+'/seal.json'}
    require({d['path'] for d in refs}==expected,'inherited exact owned inventory binding')
    for d in obj(S+'/reading-references.json'):checked(d['path'],d['sha256'],d['bytes'])
    results['inherited_owned_references']=len(refs)

    domain=obj(OLD_S+'/search-domain.json');mapped={d['local']:d for d in domain}
    readings=obj(S+'/read-manifest.json')['passages']
    for d in readings:
        txt=checked(d['path'],d['sha256']).decode('utf8',errors='replace')
        require(d['line_convention'] in ['splitlines','LF'],'line convention')
        ls=txt.splitlines() if d['line_convention']=='splitlines' else txt.split('\n')
        require(len(ls)==d['total_lines'],'reading total lines '+d['path'])
        require(1<=d['start']<=d['end']<=len(ls),'reading bounds')
        require(sha('\n'.join(ls[d['start']-1:d['end']]).encode())==d['passage_sha256'],'passage membership '+d['path'])
        if '/corpus/' in d['path']:
            require(d['path'] in mapped,'corpus passage missing original binding')
            m=mapped[d['path']]
            require(m['sha256']==d['sha256'],'passage/domain hash')
            require(d['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+m['path'],'passage raw pin')
    results['reading_passages']=len(readings)
    contracts=obj(S+'/source-contracts.json')
    replay=[]
    for d in readings:
        if '/corpus/' not in d['path']:continue
        for i,line in enumerate(read(d['path']).decode().splitlines(),1):
            if d['start']<=i<=d['end']:
                for m in re.finditer(r'\\label\{(?:lem|thm|prop|cor|eq):[^}]+\}',line):
                    replay.append({'path':d['path'],'line':i,'needle':m.group(),'line_text':line})
    require(replay==contracts,'exact source-contract lexical membership')
    results['exact_source_contract_memberships']=len(contracts)
    pages=obj(S+'/external-manifest.json')
    require(len(pages)==4,'external page count')
    versions={}
    for d in pages:
        require(d['status']==200,'external page retrieval')
        b=checked(d['path'],d['sha256'],d['bytes'])
        versions[d['url']]=re.findall(r'\[v[0-9]+\]',b.decode('utf8',errors='replace'))
    require(versions=={'https://arxiv.org/abs/2609.19118':['[v1]'],
                       'https://arxiv.org/abs/2507.09507':['[v1]'],
                       'https://arxiv.org/abs/2406.12799':['[v1]'],
                       'https://arxiv.org/abs/1911.07945':['[v1]','[v2]']},'frozen version membership')
    results['external_version_pages']=versions

    # Accepted identity verifier is hash-bound above. No source truth audit.
    old=runpy.run_path(str(ROOT/OLD_E/'verify.py'),run_name='i113_inherited_readonly')
    results['inherited_inventory']=old['validate_inventory'](oldseal)
    inherited=old['validate_core']()
    require(inherited['corpus']['original_positions']==10373,'full inherited corpus')
    results['inherited_corpus_and_exact_lexical_replay']=inherited
    diag=runpy.run_path(str(ROOT/E/'diagnostics.py'),run_name='i116_readonly_diagnostics')['run']()
    require(diag==obj(E+'/diagnostics.json'),'new deterministic diagnostic mismatch')
    results['diagnostics']=diag
    return results


def main():
    inv=inventory(obj(SEAL)) # Every owned immutable byte is checked before diagnostics.
    result=core()
    print(json.dumps({'status':'PASS','offline':True,'read_only':True,
          'certifies':'exact source/artifact identities and specified finite diagnostics only',
          'inventory':inv,'validation':result},indent=2,sort_keys=True))


if __name__=='__main__':
    try:main()
    except Exception as ex:
        print(json.dumps({'status':'FAIL','error':type(ex).__name__+': '+str(ex)},sort_keys=True))
        sys.exit(1)
