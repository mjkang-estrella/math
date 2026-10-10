"""I119 offline READ-ONLY verifier, with one full inherited corpus replay.
Every owned byte and inherited executable is checked before diagnostics.
No network, subprocess, writes, caches, extraction, repair or resealing.
Identity and finite diagnostics only; not universal proof/contribution certification.
"""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import hashlib,json,re,runpy,os

ROOT=Path(__file__).resolve().parents[3]
S='frontier/sources/i119_one_loss_online_selection'
E='frontier/experiments/i119_one_loss_online_selection'
REPORT='frontier/iterations/i119-one-loss-online-selection.md'
SEAL=S+'/seal.json'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
DRIFT={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
OLD_S='frontier/sources/i113_online_optimization_discovery'
OLD_E='frontier/experiments/i113_online_optimization_discovery'
PREV_S='frontier/sources/i116_robust_prophet_continuation'
PREV_E='frontier/experiments/i116_robust_prophet_continuation'


def require(c,msg):
    if not c:raise ValueError(msg)


def read(p):
    rel=Path(p)
    require(not rel.is_absolute() and '..' not in rel.parts,'unsafe path '+p)
    f=ROOT/rel
    require(f.is_file() and not f.is_symlink(),'missing/nonregular '+p)
    return f.read_bytes()


def sha(b):return hashlib.sha256(b).hexdigest()
def obj(p):return json.loads(read(p))


def checked(p,digest,size=None):
    b=read(p);require(sha(b)==digest,'hash mismatch '+p)
    if size is not None:require(len(b)==size,'size mismatch '+p)
    return b


def paths(report,s,e):
    out={report}
    for base in [s,e]:
        for p in (ROOT/base).rglob('*'):
            require(not p.is_symlink(),'symlink in inventory '+str(p))
            if p.is_file():out.add(str(p.relative_to(ROOT)))
    return out


def inventory(seal,unsealed=False):
    require(seal['schema']=='i119-exact-owned-v1' and seal['pin']==PIN,'seal metadata')
    require(seal['roots']==[REPORT,S+'/',E+'/'],'seal roots')
    rows=seal['files'];ps=[r['path'] for r in rows]
    require(ps==sorted(set(ps)) and SEAL not in ps,'canonical inventory')
    expect=set(ps)|(set() if unsealed else {SEAL})
    actual=paths(REPORT,S,E)
    require(actual==expect,'owned inventory mismatch '+str(sorted(actual^expect)))
    for d in rows:checked(d['path'],d['sha256'],d['bytes'])
    return {'owned_files_excluding_seal':len(rows),'seal_is_inventory_envelope':True}


def input_snapshots(base):
    inp=obj(base+'/inputs.json')
    require({d['original'] for d in inp if d['may_drift']}==DRIFT,'drift allowlist '+base)
    drift=[]
    for d in inp:
        checked(d['snapshot'],d['sha256'])
        if d['may_drift']:
            if sha(read(d['original']))!=d['sha256']:drift.append(d['original'])
        else:checked(d['original'],d['sha256'])
    return {'count':len(inp),'allowed_live_ledger_drift':sorted(drift)}


def passage_replay(base,domain,contracts_splitlines=False):
    rows=obj(base+'/read-manifest.json')['passages'];contracts=[]
    for d in rows:
        txt=checked(d['path'],d['sha256']).decode('utf8',errors='replace')
        require(d['line_convention'] in ('LF','splitlines'),'line convention')
        ls=txt.split('\n') if d['line_convention']=='LF' else txt.splitlines()
        require(len(ls)==d['total_lines'],'passage line count '+d['path'])
        require(1<=d['start']<=d['end']<=len(ls),'passage bounds')
        require(sha('\n'.join(ls[d['start']-1:d['end']]).encode())==d['passage_sha256'],'passage hash '+d['path'])
        if '/corpus/' in d['path']:
            require(d['path'] in domain,'unbound corpus reading '+d['path'])
            m=domain[d['path']]
            require(d['sha256']==m['sha256'],'reading representation hash')
            require(d['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+m['path'],'reading source-position URL')
            cs=txt.splitlines() if contracts_splitlines else ls
            for i in range(d['start'],d['end']+1):
                for match in re.finditer(r'\\label\{(?:lem|thm|prop|cor|eq):[^}]+\}',cs[i-1]):
                    contracts.append({'path':d['path'],'line':i,'needle':match.group(),'line_text':cs[i-1]})
    require(contracts==obj(base+'/source-contracts.json'),'exact contract lexical multiset '+base)
    return {'passages':len(rows),'exact_contract_memberships':len(contracts)}


def versions(base):
    expected={'https://arxiv.org/abs/2609.19118':['[v1]'],
              'https://arxiv.org/abs/2507.09507':['[v1]'],
              'https://arxiv.org/abs/2406.12799':['[v1]'],
              'https://arxiv.org/abs/1911.07945':['[v1]','[v2]']}
    got={}
    for d in obj(base+'/external-manifest.json'):
        require(d.get('status')==200 and 'error' not in d,'primary page error')
        b=checked(d['path'],d['sha256'],d['bytes'])
        got[d['url']]=re.findall(r'\[v[0-9]+\]',b.decode('utf8',errors='replace'))
    require(got==expected,'frozen primary version membership')
    return got


def core():
    result={}
    require(obj('sources/upstream.json')['commit']==PIN,'pin')
    result['snapshots']=input_snapshots(S)
    refs=obj(S+'/inherited-references.json')
    require([d['path'] for d in refs]==sorted({d['path'] for d in refs}),'inherited reference canonicality')
    for d in refs:checked(d['path'],d['sha256'],d['bytes'])
    expected=set()
    for name,report in [('i113_online_optimization_discovery','frontier/iterations/i113-online-optimization-discovery.md'),
                        ('i116_robust_prophet_continuation','frontier/iterations/i116-robust-prophet-continuation.md')]:
        s='frontier/sources/'+name;e='frontier/experiments/'+name;sp=s+'/seal.json';seal=obj(sp)
        require(seal['pin']==PIN and seal['roots']==[report,s+'/',e+'/'],'inherited seal metadata')
        rows=seal['files'];ps=[d['path'] for d in rows]
        require(ps==sorted(set(ps)) and sp not in ps,'inherited seal canonicality')
        owned=set(ps)|{sp};require(paths(report,s,e)==owned,'inherited exact inventory '+name)
        for d in rows:checked(d['path'],d['sha256'],d['bytes'])
        expected|=owned
    expected|={'frontier/experiments/i113-parent-verification.json','frontier/experiments/i116-parent-verification.json'}
    require({d['path'] for d in refs}==expected,'inherited flattened inventory')
    result['inherited_owned_and_receipt_references']=len(refs)
    # Validate I116's additional artifacts directly, without recursively replaying its core.
    result['i116_snapshots']=input_snapshots(PREV_S)
    for base in [PREV_S,S]:
        for d in obj(base+'/reading-references.json'):checked(d['path'],d['sha256'],d['bytes'])
    oldexpected={d['path'] for d in obj(OLD_S+'/seal.json')['files']}|{OLD_S+'/seal.json'}
    prevrefs=obj(PREV_S+'/inherited-references.json')
    require({d['path'] for d in prevrefs}==oldexpected,'I116 inherited exact bindings')
    for d in prevrefs:checked(d['path'],d['sha256'],d['bytes'])
    domain={d['local']:d for d in obj(OLD_S+'/search-domain.json')}
    result['i116_passages']=passage_replay(PREV_S,domain,contracts_splitlines=True)
    result['i119_passages']=passage_replay(S,domain)
    result['i116_primary_versions']=versions(PREV_S)
    result['i119_primary_versions']=versions(S)
    verdict=obj(S+'/original-audit-verdicts.json')
    require(verdict['original_report_sha256']==sha(read('frontier/iterations/i116-robust-prophet-continuation.md')),'audit-original binding')
    # All owned/inherited executable bytes are now checked. Replay corpus only here.
    old=runpy.run_path(str(ROOT/OLD_E/'verify.py'),run_name='i119_bound_i113_readonly')
    inherited=old['validate_core']()
    require(inherited['corpus']['original_positions']==10373,'corpus coverage')
    require(inherited['lexical_matching_line_multisets']=={'scope':399,'robust':199},'inherited lexical results')
    result['single_inherited_corpus_replay']=inherited
    prevdiag=runpy.run_path(str(ROOT/PREV_E/'diagnostics.py'),run_name='i119_bound_i116_diagnostics')['run']()
    require(prevdiag==obj(PREV_E+'/diagnostics.json'),'I116 diagnostic replay')
    result['i116_diagnostics']=prevdiag
    diag=runpy.run_path(str(ROOT/E/'diagnostics.py'),run_name='i119_diagnostics')['run']()
    require(diag==obj(E+'/diagnostics.json'),'I119 diagnostic replay')
    result['i119_diagnostics']=diag
    return result


def readonly_hook(event,args):
    if event=='open':
        mode=args[1];flags=args[2]
        require(not(isinstance(mode,str) and any(c in mode for c in 'wax+')),'write forbidden')
        require(not(isinstance(flags,int) and flags&(os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND)),'write flags forbidden')
    if event.startswith(('socket.','subprocess.')) or event in {
        'os.system','os.mkdir','os.remove','os.rmdir','os.rename','os.link','os.symlink',
        'os.chmod','os.chown','os.utime','os.truncate','os.exec','os.posix_spawn'}:
        raise RuntimeError('offline/read-only operation forbidden: '+event)


def main():
    sys.addaudithook(readonly_hook)
    inv=inventory(obj(SEAL))
    result=core()
    print(json.dumps({'status':'PASS','offline':True,'read_only':True,
        'certifies':'exact identities, memberships and finite diagnostics only',
        'corpus_replays':1,'inventory':inv,'validation':result},indent=2,sort_keys=True))


if __name__=='__main__':
    try:main()
    except Exception as ex:
        print(json.dumps({'status':'FAIL','error':type(ex).__name__+': '+str(ex)},sort_keys=True))
        sys.exit(1)
