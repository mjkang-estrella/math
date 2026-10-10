"""Offline/read-only I125 evidence replay; every immutable check before diagnostics.
No extraction, network, subprocess, write, bytecode, repair or reseal.
One inherited corpus replay; all diagnostic callbacks deferred and deduplicated.
"""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import hashlib,json,re,runpy,os
ROOT=Path(__file__).resolve().parents[3]
S='frontier/sources/i125_dini_singular_packing'
E='frontier/experiments/i125_dini_singular_packing'
REPORT='frontier/iterations/i125-dini-singular-packing.md'
SEAL=S+'/seal.json'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
DRIFT={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
PREV_S='frontier/sources/i122_variational_free_boundary_discovery'
PREV_E='frontier/experiments/i122_variational_free_boundary_discovery'

def require(c,msg):
    if not c:raise ValueError(msg)
def read(p):
    q=Path(p);require(not q.is_absolute() and '..' not in q.parts,'unsafe path '+p)
    q=ROOT/q;require(q.is_file() and not q.is_symlink(),'missing/nonregular '+p)
    return q.read_bytes()
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
            require(not p.is_symlink(),'symlink '+str(p))
            if p.is_file():out.add(str(p.relative_to(ROOT)))
    return out
def inventory(seal,unsealed=False):
    require(seal['schema']=='i125-exact-owned-v1' and seal['pin']==PIN,'seal metadata')
    require(seal['roots']==[REPORT,S+'/',E+'/'],'seal roots')
    rows=seal['files'];ps=[d['path'] for d in rows]
    require(ps==sorted(set(ps)) and SEAL not in ps,'canonical inventory')
    require(paths(REPORT,S,E)==set(ps)|(set() if unsealed else {SEAL}),'exact owned inventory')
    for d in rows:checked(d['path'],d['sha256'],d['bytes'])
    return {'owned_files_excluding_seal':len(rows),'owned_artifacts_including_seal':len(rows)+(not unsealed),'seal_is_inventory_envelope':True}
def readonly_hook(event,args):
    if event=='open':
        mode,flags=args[1:3]
        require(not(isinstance(mode,str) and any(c in mode for c in 'wax+')),'write forbidden')
        require(not(isinstance(flags,int) and flags&(os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND)),'write flags forbidden')
    if event.startswith(('socket.','subprocess.')) or event in {'os.system','os.mkdir','os.remove','os.rmdir','os.rename','os.link','os.symlink','os.chmod','os.chown','os.utime','os.truncate','os.exec','os.posix_spawn'}:
        raise RuntimeError('offline/read-only operation forbidden: '+event)

def core():
    result={}
    require(obj('sources/upstream.json')['commit']==PIN,'pin')
    snapshots=obj(S+'/snapshots.json')
    require({d['live'] for d in snapshots if d['drift']}==DRIFT,'drift allowlist')
    drift=[]
    for d in snapshots:
        checked(d['snapshot'],d['sha256'])
        if d['drift']:
            if sha(read(d['live']))!=d['sha256']:drift.append(d['live'])
        else:checked(d['live'],d['sha256'])
    result['snapshots']={'count':len(snapshots),'allowed_live_ledger_drift':sorted(drift)}
    recursive=obj(S+'/recursive-originals.json')
    for d in recursive:
        checked(d['task'],d['sha256']);checked(d['snapshot'],d['sha256'])
        require(read(d['brief']).decode()==obj(d['task'])['brief'],'complete recursive brief '+d['task'])
    brief=read(S+'/original-task-125-brief.txt').decode()
    report,parent=brief.split('--- ORIGINAL I122 REPORT ---\n',1)[1].split('\n--- FINALIZED PARENT RESPONSE ---\n',1)
    require(report.strip()==read('frontier/iterations/i122-variational-free-boundary-discovery.md').decode().strip(),'supplied original report')
    require(json.loads(parent)==obj('frontier/experiments/i122-parent-verification.json'),'supplied final parent response')
    require(obj(S+'/original-audit-verdicts.json')['original_report_sha256']==sha(read('frontier/iterations/i122-variational-free-boundary-discovery.md')),'audit binding')
    require(obj(S+'/original-audit-addendum.json')['verdict']=='FAIL as a general-Lambda equality','preserved audit addendum')
    refs=obj(S+'/inherited-references.json')
    require([d['path'] for d in refs]==sorted({d['path'] for d in refs}),'canonical inherited references')
    for d in refs:checked(d['path'],d['sha256'],d['bytes'])
    expected=set()
    for name,report in [('i113_online_optimization_discovery','frontier/iterations/i113-online-optimization-discovery.md'),('i116_robust_prophet_continuation','frontier/iterations/i116-robust-prophet-continuation.md'),('i119_one_loss_online_selection','frontier/iterations/i119-one-loss-online-selection.md'),('i122_variational_free_boundary_discovery','frontier/iterations/i122-variational-free-boundary-discovery.md')]:
        s='frontier/sources/'+name;e='frontier/experiments/'+name;sp=s+'/seal.json';seal=obj(sp)
        require(seal['pin']==PIN and seal['roots']==[report,s+'/',e+'/'],'inherited metadata')
        ps=[d['path'] for d in seal['files']];require(ps==sorted(set(ps)),'inherited canonicality')
        require(paths(report,s,e)==set(ps)|{sp},'inherited exact inventory '+name)
        for d in seal['files']:checked(d['path'],d['sha256'],d['bytes'])
        expected|=set(ps)|{sp}
    expected|={'frontier/experiments/'+n+'-parent-verification.json' for n in ['i113','i116','i119','i122']}
    require({d['path'] for d in refs}==expected,'complete flat inherited inventory')
    require(not any(re.search(r'/(?:iteration|i)12[34]',p) for p in expected),'active dependency')
    result['inherited_references']=len(refs)
    for d in obj(S+'/reading-references.json'):checked(d['path'],d['sha256'],d['bytes'])
    domain=obj('frontier/sources/i113_online_optimization_discovery/search-domain.json')
    mapped={d['local']:d for d in domain};contracts=[]
    for d in obj(S+'/read-manifest.json')['passages']:
        t=checked(d['path'],d['sha256']).decode('utf8',errors='replace')
        require(d['line_convention']=='LF','reading line convention')
        ls=t.split('\n');require(len(ls)==d['total_lines'] and 1<=d['start']<=d['end']<=len(ls),'passage bounds')
        require(sha('\n'.join(ls[d['start']-1:d['end']]).encode())==d['passage_sha256'],'passage hash')
        if '/corpus/' in d['path']:
            require(mapped[d['path']]['sha256']==d['sha256'],'source position')
            require(d['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+mapped[d['path']]['path'],'source URL')
            for i in range(d['start'],d['end']+1):
                for m in re.finditer(r'\\label\{(?:lem|thm|prop|cor|eq):[^}]+\}',ls[i-1]):
                    contracts.append({'path':d['path'],'line':i,'needle':m.group(),'text':ls[i-1]})
    require(contracts==obj(S+'/source-contracts.json'),'source contract occurrences')
    lex=obj(S+'/focused-lexical.json');pat=re.compile(lex['expression'],re.I);hits=[]
    for p in lex['paths']:
        for i,line in enumerate(read(p).decode('utf8',errors='replace').splitlines(),1):
            mm=list(pat.finditer(line))
            if mm:hits.append({'path':p,'line':i,'text':line,'occurrences':[{'start':m.start(),'end':m.end(),'text':m.group()} for m in mm]})
    require(hits==lex['hits'],'focused exact lexical matches')
    ledger=obj(S+'/ledger-overlap.json');pat=re.compile(ledger['expression'],re.I);hits=[]
    for d in snapshots:
        if d['drift']:
            for i,line in enumerate(read(d['snapshot']).decode().splitlines(),1):
                mm=list(pat.finditer(line))
                if mm:hits.append({'snapshot':d['snapshot'],'live':d['live'],'line':i,'text':line,'occurrences':[{'start':m.start(),'end':m.end(),'text':m.group()} for m in mm]})
    require(hits==ledger['hits'],'ledger exact occurrences')
    extracts=0
    for d in obj(S+'/external-manifest.json'):
        require(d['status']==200,'external status');b=checked(d['path'],d['sha256'],d['bytes'])
        if 'versions' in d:require(re.findall(r'\[v[0-9]+\]',b.decode())==d['versions'],'version membership')
        if 'extraction' in d:
            x=d['extraction'];require(x['exit_code']==0,'extraction status');checked(x['path'],x['sha256']);extracts+=1
    require(extracts==2,'selective extraction count')
    result['new_pdf_texts']=extracts
    result['readings']={'passages':len(obj(S+'/read-manifest.json')['passages']),'source_contracts':len(contracts),'focused_lexical_lines':len(lex['hits'])}
    # The I122 core already defers its own inherited suites. This outer layer
    # defers those and I122 as well, until every I125 and inherited check ends.
    real=runpy.run_path;pending=[]
    allowed={'frontier/experiments/'+n+'/diagnostics.py' for n in ['i113_online_optimization_discovery','i116_robust_prophet_continuation','i119_one_loss_online_selection','i122_variational_free_boundary_discovery']}
    def deferred(path,*args,**kwargs):
        p=str(Path(path).resolve().relative_to(ROOT))
        if p.endswith('/diagnostics.py'):
            require(p in allowed and p not in pending,'unexpected/duplicate diagnostic '+p)
            pending.append(p)
            return {'run':lambda:obj(p[:-3]+'.json')}
        return real(path,*args,**kwargs)
    runpy.run_path=deferred
    try:
        previous=real(str(ROOT/PREV_E/'verify.py'),run_name='i125_bound_i122_core')
        inherited=previous['core']()
    finally:runpy.run_path=real
    require(set(pending)==allowed,'all inherited diagnostics deferred')
    require(inherited['inherited_evidence']['single_inherited_corpus_replay']['corpus']['original_positions']==10373,'one complete corpus replay')
    # No immutable check is left below this line.
    actual={}
    for p in pending+[E+'/diagnostics.py']:
        got=real(str(ROOT/p),run_name='i125_checked_diagnostic')['run']()
        require(got==obj(p[:-3]+'.json'),'diagnostic replay '+p);actual[p]=got
    result['all_immutable_checks_before_diagnostic_execution']=True
    result['actual_diagnostic_replays_after_all_immutable_checks']=actual
    result['inherited_evidence']=inherited
    return result

def main():
    sys.addaudithook(readonly_hook)
    inv=inventory(obj(SEAL));validation=core()
    print(json.dumps({'status':'PASS','offline':True,'read_only':True,'corpus_replays':1,'inventory':inv,'validation':validation,'certifies':'artifact identities, exact memberships and finite diagnostics only'},indent=2,sort_keys=True))
if __name__=='__main__':
    try:main()
    except Exception as ex:
        print(json.dumps({'status':'FAIL','error':type(ex).__name__+': '+str(ex)},sort_keys=True));sys.exit(1)
