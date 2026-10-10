"""Offline read-only I128 replay. All immutable checks precede diagnostics.
--preseal validates development evidence without creating a seal or claiming a sealed PASS.
No network, subprocess, bytecode, repair, reseal, or extraction.
"""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import os,json,hashlib,re,runpy
ROOT=Path(__file__).resolve().parents[3]
S='frontier/sources/i128_statistical_learning_discovery'
E='frontier/experiments/i128_statistical_learning_discovery'
REPORT='frontier/iterations/i128-statistical-learning-discovery.md'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
SEAL=S+'/seal.json'
DRIFT={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
NAMES=['i113_online_optimization_discovery','i116_robust_prophet_continuation','i119_one_loss_online_selection','i122_variational_free_boundary_discovery','i125_dini_singular_packing']
def require(condition,message):
    if not condition:raise ValueError(message)
def read(p):
    q=Path(p);require(not q.is_absolute() and '..' not in q.parts,'unsafe path '+p)
    q=ROOT/q;require(q.is_file() and not q.is_symlink(),'missing/nonregular '+p);return q.read_bytes()
def sha(b):return hashlib.sha256(b).hexdigest()
def obj(p):return json.loads(read(p))
def check(d):
    b=read(d['path']);require(sha(b)==d['sha256'],'hash '+d['path'])
    if 'bytes' in d:require(len(b)==d['bytes'],'size '+d['path'])
    return b
def owned(report,s,e):
    ps={report}
    for base in [s,e]:
        for p in (ROOT/base).rglob('*'):
            require(not p.is_symlink(),'symlink '+str(p))
            if p.is_file():ps.add(str(p.relative_to(ROOT)))
    return ps
def rows_check(rows,actual,seal_path,canonical=True):
    ps=[d['path'] for d in rows]
    require(len(ps)==len(set(ps)),'duplicate inventory row')
    require(seal_path not in ps,'self-hash row')
    if canonical:require(ps==sorted(ps),'global canonical inventory')
    require(actual==set(ps)|{seal_path},'exact membership '+seal_path)
    for d in rows:check(d)
def readonly(event,args):
    if event=='open':
        mode,flags=args[1:3]
        require(not(isinstance(mode,str) and any(c in mode for c in 'wax+')),'write forbidden')
        require(not(isinstance(flags,int) and flags&(os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND)),'write flags forbidden')
    if event.startswith(('socket.','subprocess.')) or event in {'os.system','os.mkdir','os.remove','os.rmdir','os.rename','os.link','os.symlink','os.chmod','os.chown','os.utime','os.truncate','os.exec','os.posix_spawn'}:
        raise RuntimeError('offline/read-only forbidden: '+event)
def main(preseal=False):
    sys.addaudithook(readonly)
    actual=owned(REPORT,S,E)
    if preseal:
        require(SEAL not in actual,'preseal forbidden after final seal')
        inv=[{'path':p,'bytes':len(read(p)),'sha256':sha(read(p))} for p in sorted(actual)]
        rows_check(inv,actual|{SEAL},SEAL)
    else:
        seal=obj(SEAL)
        require(seal['schema']=='i128-exact-owned-v1' and seal['pin']==PIN,'seal metadata')
        require(seal['roots']==[REPORT,S+'/',E+'/'],'seal roots')
        inv=seal['files'];rows_check(inv,actual,SEAL)
        require(seal['validated_inventory_sha256']==sha(json.dumps(inv,sort_keys=True,separators=(',',':')).encode()),'preseal inventory binding')
    require(obj('sources/upstream.json')['commit']==PIN,'upstream identity')
    snapshots=obj(S+'/snapshots.json');require({d['live'] for d in snapshots if d['drift']}==DRIFT,'only four live ledgers drift')
    drift=[]
    for d in snapshots:
        check({'path':d['snapshot'],'bytes':d['bytes'],'sha256':d['sha256']})
        if d['drift']:
            if sha(read(d['live']))!=d['sha256']:drift.append(d['live'])
        else:check({'path':d['live'],'bytes':d['bytes'],'sha256':d['sha256']})
    for n,tail,digest in [(125,'dini-singular-packing','91a5fd88526b4ba5f7ebd5934dcb305c017ecf6cfcd8682d8d9f07a16251f203'),(122,'variational-free-boundary-discovery','7f2accc06c95b5ccc50e7ca2b898962fd083e4d59f8f3b6275345c9604682024'),(119,'one-loss-online-selection','417f8386d54303348d2bfa6747163f8ebf196cf8cefe640a9135eddb5eadf961')]:
        p=f'frontier/iterations/iteration{n}-{tail}-task.json';raw=read(p);require(sha(raw)==digest,'recursive task hash')
        task=json.loads(raw);decoded='\n'.join('FIELD '+k+'\n'+(v if isinstance(v,str) else json.dumps(v,ensure_ascii=False,indent=2)) for k,v in task.items())
        require(decoded==read(S+f'/decoded-iteration{n}-{tail}-task.txt').decode(),'all decoded fields '+p)
    refs=obj(S+'/inherited-references.json');require([d['path'] for d in refs]==sorted({d['path'] for d in refs}),'flat reference canonicality')
    for d in refs:check(d)
    expected=set()
    original_seal=None
    for name in NAMES:
        sp='frontier/sources/'+name+'/seal.json';seal=obj(sp);report,s,e=seal['roots'];s=s.rstrip('/');e=e.rstrip('/')
        require(seal['pin']==PIN,'inherited pin')
        rows_check(seal['files'],owned(report,s,e),sp,canonical=name!=NAMES[-1])
        expected|={d['path'] for d in seal['files']}|{sp}
        if name==NAMES[-1]:original_seal=seal
    expected|={f'frontier/experiments/i{n}-parent-verification.json' for n in [113,116,119,122,125]}
    expected.add('frontier/experiments/i125-parent-order-replay.py')
    require(expected=={d['path'] for d in refs},'complete flat inherited memberships')
    require(not any(re.search(r'/(?:iteration|i)12[67]',p) for p in expected),'active output dependency')
    oldsp='frontier/sources/i125_dini_singular_packing/seal.json'
    require(sha(read(oldsp))=='8fdd857eeccb0d61279b428c5148915fee4d858fbc63dbc4061b1e2ee9b87f2f','original I125 seal')
    require(sha(read('frontier/experiments/i125-parent-order-replay.py'))=='0507da4a890521e3d8e2b875bd8720c8c3e5ebf6093879fc134ee1178a65227e','frozen parent adapter')
    require(sha(read('frontier/experiments/i125_dini_singular_packing/verify.py'))=='01bcbb659a7eef2c5fce48cb8034802a9925701fec837a2ddb47d9a57f5cfc68','original verifier identity')
    ps=[d['path'] for d in original_seal['files']]
    require(len(ps)==42 and ps!=sorted(ps),'retain original noncanonical presentation')
    receipt=obj('frontier/experiments/i125-parent-verification.json')
    require(receipt['original_replay']['exit_code']==1 and 'ValueError: canonical inventory' in receipt['original_replay']['stdout'],'parent original FAIL')
    require(receipt['ordering_only_replay']['result']['status']=='PASS','separate parent ordering-only PASS')
    evidence=obj(S+'/original-evidence-audit.json')
    require(evidence['exit_code']==1 and 'ValueError: canonical inventory' in evidence['stdout'],'independent original FAIL')
    require(obj(S+'/original-audit-verdicts.json')['original_report_sha256']==sha(read('frontier/iterations/i125-dini-singular-packing.md')),'original mathematical audit binding')
    for d in obj(S+'/reading-references.json'):check(d)
    domain=obj('frontier/sources/i113_online_optimization_discovery/search-domain.json');mapped={d['local']:d for d in domain}
    selected=obj(S+'/selected-inventory.json');require(len({d['path'] for d in selected})==len(selected),'duplicate selection')
    for d in selected:require(mapped[d['local']]==d,'selected exact mapping')
    contracts=[];passages=obj(S+'/read-manifest.json')['passages']
    for d in passages:
        text=check(d).decode('utf8',errors='replace');conv=d['line_convention'];require(conv in {'LF','splitlines'},'line convention')
        ls=text.split('\n') if conv=='LF' else text.splitlines()
        require(len(ls)==d['total_lines'] and 1<=d['start']<=d['end']<=len(ls),'range bounds')
        require(sha('\n'.join(ls[d['start']-1:d['end']]).encode())==d['passage_sha256'],'reading passage')
        if 'source_path' in d:
            require(mapped[d['path']]['path']==d['source_path'] and mapped[d['path']]['sha256']==d['sha256'],'source membership')
            require(d['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+d['source_path'],'source URL')
            for i in range(d['start'],d['end']+1):
                for m in re.finditer(r'\\label\{[^}]+\}',ls[i-1]):contracts.append({'path':d['path'],'line':i,'needle':m.group(),'text':ls[i-1]})
    require(contracts==obj(S+'/source-contracts.json'),'source label occurrences')
    lex=obj(S+'/focused-lexical.json');hits=[]
    for p in lex['paths']:
        for i,line in enumerate(read(p).decode().splitlines(),1):
            mm=list(re.finditer(lex['expression'],line,re.I))
            if mm:hits.append({'path':p,'line':i,'text':line,'occurrences':[{'start':m.start(),'end':m.end(),'text':m.group()} for m in mm]})
    require(hits==lex['hits'],'exact focused lexical matches')
    ledger=obj(S+'/ledger-overlap.json');lh=[]
    for d in snapshots:
        if d['drift']:
            for i,line in enumerate(read(d['snapshot']).decode().splitlines(),1):
                mm=list(re.finditer(ledger['expression'],line,re.I))
                if mm:lh.append({'snapshot':d['snapshot'],'line':i,'text':line,'occurrences':[{'start':m.start(),'end':m.end(),'text':m.group()} for m in mm]})
    require(lh==ledger['hits'],'frozen ledger lexical matches')
    for d in obj(S+'/external-manifest.json'):
        require(d['status']==200,'retrieval status');b=check(d)
        if 'versions' in d:require(re.findall(r'\[v[0-9]+\]',b.decode())==d['versions'],'primary version membership')
        if 'text' in d:check(d['text'])
    # One inherited validation chain, not a verifier subprocess tree. Its
    # callbacks are intercepted, so no diagnostic source executes yet.
    real=runpy.run_path;pending=[]
    allowed={f'frontier/experiments/{name}/diagnostics.py' for name in NAMES}
    def deferred(path,*args,**kwargs):
        p=str(Path(path).resolve().relative_to(ROOT))
        if p.endswith('/diagnostics.py'):
            require(p in allowed and p not in pending,'unexpected/duplicate diagnostic '+p);pending.append(p)
            return {'run':lambda:obj(p[:-3]+'.json')}
        return real(path,*args,**kwargs)
    runpy.run_path=deferred
    try:
        old=real(str(ROOT/'frontier/experiments/i125_dini_singular_packing/verify.py'),run_name='i128_bound_original_core')
        try:old['inventory'](original_seal)
        except ValueError as ex:require(str(ex)=='canonical inventory','different original failure')
        else:raise ValueError('original I125 FAIL erased')
        inherited=old['core']()
    finally:runpy.run_path=real
    require(set(pending)==allowed,'five suites deferred')
    corpus=inherited['inherited_evidence']['inherited_evidence']['single_inherited_corpus_replay']['corpus']
    require(corpus=={'additional_originals':1033,'i14_originals':9340,'inherited_pdf_texts':776,'manuscripts':749,'original_positions':10373,'tree_entries':13223},'complete single inherited corpus')
    # Every immutable check has finished before the first diagnostic source.
    results={}
    for p in pending+[E+'/diagnostics.py']:
        got=real(str(ROOT/p),run_name='i128_validated_diagnostic')['run']()
        require(got==obj(p[:-3]+'.json'),'finite diagnostic '+p);results[p]=got
    return {'status':'PRESEAL PASS' if preseal else 'PASS','validated_inventory_sha256':sha(json.dumps(inv,sort_keys=True,separators=(',',':')).encode()),'offline':True,'read_only':True,'all_immutable_checks_before_diagnostics':True,'corpus_replays':1,'corpus':corpus,'owned_files_excluding_seal':len(inv),'original_i125_verifier':'FAIL: ValueError: canonical inventory','parent_ordering_only_replay':'PASS, distinct, no inherited bytes changed','inherited_flat_references':len(refs),'passages':len(passages),'source_contract_occurrences':len(contracts),'focused_lexical_lines':len(hits),'live_ledger_drift':sorted(drift),'finite_diagnostics_once':results,'certifies':'artifact identities, exact memberships and finite identities only; no universal-proof or contribution certification'}

if __name__=='__main__':
    try:
        require(sys.argv[1:] in [[],['--preseal']],'unknown arguments')
        print(json.dumps(main(bool(sys.argv[1:])),indent=2,sort_keys=True))
    except Exception as ex:
        print(json.dumps({'status':'FAIL','error':type(ex).__name__+': '+str(ex)},sort_keys=True));sys.exit(1)
