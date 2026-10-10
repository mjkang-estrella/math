"""I122 offline read-only verification. All immutable bytes before ALL diagnostics.
One flat corpus replay through the hash-bound I119/I113 core. No I116 core.
No writes, bytecode, network, subprocesses, extraction, repairs or resealing.
"""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import hashlib,json,re,runpy,os
ROOT=Path(__file__).resolve().parents[3]
S='frontier/sources/i122_variational_free_boundary_discovery'
E='frontier/experiments/i122_variational_free_boundary_discovery'
REPORT='frontier/iterations/i122-variational-free-boundary-discovery.md'
SEAL=S+'/seal.json'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
DRIFT={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
PREV_S='frontier/sources/i119_one_loss_online_selection'
PREV_E='frontier/experiments/i119_one_loss_online_selection'
OLD_S='frontier/sources/i113_online_optimization_discovery'

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
    require(seal['schema']=='i122-exact-owned-v1' and seal['pin']==PIN,'seal metadata')
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
    inputs=obj(S+'/inputs.json');require({d['original'] for d in inputs if d['may_drift']}==DRIFT,'drift allowlist')
    drift=[]
    for d in inputs:
        checked(d['snapshot'],d['sha256'])
        if d['may_drift']:
            if sha(read(d['original']))!=d['sha256']:drift.append(d['original'])
        else:checked(d['original'],d['sha256'])
    result['snapshots']={'count':len(inputs),'allowed_live_ledger_drift':sorted(drift)}
    require(sha(read('frontier/iterations/iteration119-one-loss-online-selection-task.json'))=='417f8386d54303348d2bfa6747163f8ebf196cf8cefe640a9135eddb5eadf961','original task binding')
    require(read(S+'/original-i119-recursive-brief.txt').decode()==obj('frontier/iterations/iteration119-one-loss-online-selection-task.json')['brief'],'complete recursive brief field identity')
    verdict=obj(S+'/original-audit-verdicts.json')
    require(verdict['original_report_sha256']==sha(read('frontier/iterations/i119-one-loss-online-selection.md')),'original report verdict binding')
    refs=obj(S+'/inherited-references.json');require([d['path'] for d in refs]==sorted({d['path'] for d in refs}),'canonical flattened references')
    for d in refs:checked(d['path'],d['sha256'],d['bytes'])
    expected=set()
    for name,report in [('i113_online_optimization_discovery','frontier/iterations/i113-online-optimization-discovery.md'),('i116_robust_prophet_continuation','frontier/iterations/i116-robust-prophet-continuation.md'),('i119_one_loss_online_selection','frontier/iterations/i119-one-loss-online-selection.md')]:
        s='frontier/sources/'+name;e='frontier/experiments/'+name;sp=s+'/seal.json';seal=obj(sp)
        require(seal['pin']==PIN and seal['roots']==[report,s+'/',e+'/'],'inherited seal metadata')
        ps=[d['path'] for d in seal['files']];require(ps==sorted(set(ps)) and sp not in ps,'inherited canonicality')
        owned=set(ps)|{sp};require(paths(report,s,e)==owned,'inherited exact owned inventory '+name)
        for d in seal['files']:checked(d['path'],d['sha256'],d['bytes'])
        expected|=owned
    expected|={'frontier/experiments/'+n+'-parent-verification.json' for n in ['i113','i116','i119']}
    require({d['path'] for d in refs}==expected,'complete flattened inherited references')
    require(not any('/i120' in p or '/i121' in p or '/iteration120' in p or '/iteration121' in p for p in expected),'active output dependency')
    result['inherited_references']=len(refs)
    for d in obj(S+'/reading-references.json'):checked(d['path'],d['sha256'],d['bytes'])
    domain=obj(OLD_S+'/search-domain.json');mapped={d['local']:d for d in domain}
    rows=obj(S+'/read-manifest.json')['passages'];contracts=[]
    for d in rows:
        t=checked(d['path'],d['sha256']).decode('utf8',errors='replace')
        require(d['line_convention'] in ['LF','splitlines'],'line convention')
        ls=t.split('\n') if d['line_convention']=='LF' else t.splitlines()
        require(len(ls)==d['total_lines'] and 1<=d['start']<=d['end']<=len(ls),'passage bounds/count')
        require(sha('\n'.join(ls[d['start']-1:d['end']]).encode())==d['passage_sha256'],'passage identity '+d['path'])
        if '/corpus/' in d['path']:
            require(d['path'] in mapped and mapped[d['path']]['sha256']==d['sha256'],'source position binding')
            require(d['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+mapped[d['path']]['path'],'pinned source URL')
            for i in range(d['start'],d['end']+1):
                for m in re.finditer(r'\\label\{(?:lem|thm|prop|cor|eq):[^}]+\}',ls[i-1]):contracts.append({'path':d['path'],'line':i,'needle':m.group(),'line_text':ls[i-1]})
    require(contracts==obj(S+'/source-contracts.json'),'complete reading contract occurrences')
    result['readings']={'passages':len(rows),'source_contract_memberships':len(contracts)}
    lex=obj(S+'/lexical-results.json');found={k:[] for k in lex};patterns={k:re.compile(d['expression'],re.I) for k,d in lex.items()}
    for d in domain:
        for i,line in enumerate(read(d['local']).decode('utf8',errors='replace').splitlines(),1):
            for k,pattern in patterns.items():
                matches=list(pattern.finditer(line))
                if matches:found[k].append({'path':d['local'],'source_path':d['path'],'line':i,'text':line,'occurrences':[{'start':m.start(),'end':m.end(),'text':m.group()} for m in matches]})
    for k in lex:require(found[k]==lex[k]['hits'],'exact lexical occurrences '+k)
    result['lexical_matching_lines']={k:len(v) for k,v in found.items()}
    ledger=obj(S+'/ledger-overlap.json');hits=[]
    for d in inputs:
        if d['may_drift']:
            for i,line in enumerate(read(d['snapshot']).decode().splitlines(),1):
                matches=list(re.finditer(ledger['expression'],line,re.I))
                if matches:hits.append({'snapshot':d['snapshot'],'original':d['original'],'line':i,'text':line,'occurrences':[{'start':m.start(),'end':m.end(),'text':m.group()} for m in matches]})
    require(hits==ledger['hits'],'frozen ledger occurrence replay')
    external=obj(S+'/external-manifest.json');errors=[];extracts=0
    for d in external:
        if 'error' in d:errors.append(d);continue
        require(d['status']==200,'retrieval status');checked(d['path'],d['sha256'],d['bytes'])
        if 'extraction' in d:
            ex=d['extraction'];require(ex['exit_code']==0,'extraction failure');checked(ex['text'],ex['sha256']);extracts+=1
    require(len(errors)==1 and 'bs4' in errors[0]['error'],'preserved conversion failure')
    require(extracts==4,'selective extraction inventory')
    versions=[]
    for d in obj(S+'/primary-versions.json'):
        b=checked(d['path'],d['sha256']);require(re.findall(r'\[v[0-9]+\]',b.decode())==d['versions'],'primary version membership');versions.append({'url':d['url'],'versions':d['versions']})
    result['primary_versions']=versions;result['new_pdf_texts']=extracts
    # Defer ALL diagnostics. Inherited core still performs its exact corpus/reference
    # checks, but its diagnostic callbacks return already hash-bound expected data.
    # No diagnostic source is loaded or executed until the entire core returns.
    real_run_path=runpy.run_path;pending=[]
    allowed={'frontier/experiments/'+name+'/diagnostics.py' for name in ['i113_online_optimization_discovery','i116_robust_prophet_continuation','i119_one_loss_online_selection']}
    def deferred(path,*args,**kwargs):
        p=str(Path(path).resolve().relative_to(ROOT))
        if p.endswith('/diagnostics.py'):
            require(p in allowed and p not in pending,'unexpected/duplicate diagnostic '+p)
            pending.append(p)
            return {'run':lambda:obj(p[:-3]+'.json')}
        return real_run_path(path,*args,**kwargs)
    runpy.run_path=deferred
    try:
        previous=real_run_path(str(ROOT/PREV_E/'verify.py'),run_name='i122_bound_i119_core')
        inherited=previous['core']()
    finally:runpy.run_path=real_run_path
    require(set(pending)==allowed,'all inherited diagnostics deferred')
    require(inherited['single_inherited_corpus_replay']['corpus']['original_positions']==10373,'flat full corpus replay')
    # Every bound artifact and source-position is now checked. Execute diagnostics.
    actual={}
    for p in pending+[E+'/diagnostics.py']:
        got=real_run_path(str(ROOT/p),run_name='i122_checked_diagnostic')['run']()
        require(got==obj(p[:-3]+'.json'),'diagnostic replay '+p)
        actual[p]=got
    result['inherited_evidence']=inherited
    result['actual_diagnostic_replays_after_all_immutable_checks']=actual
    result['all_immutable_checks_before_diagnostic_execution']=True
    return result

def main():
    sys.addaudithook(readonly_hook)
    inv=inventory(obj(SEAL));validation=core()
    print(json.dumps({'status':'PASS','offline':True,'read_only':True,'corpus_replays':1,'inventory':inv,'certifies':'exact artifact identities, passage/lexical memberships and finite diagnostics only','validation':validation},indent=2,sort_keys=True))

if __name__=='__main__':
    try:main()
    except Exception as ex:
        print(json.dumps({'status':'FAIL','error':type(ex).__name__+': '+str(ex)},sort_keys=True));sys.exit(1)
