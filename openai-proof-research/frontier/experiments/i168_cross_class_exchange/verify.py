"""I168 immutable-first read-only verifier. Invoke with python3 -I -B."""
import sys,os,json,hashlib,time,pathlib,sysconfig,importlib,importlib.util
# Preload only standard-library dependencies before installing the execution hook.
import random,fractions,math,itertools,collections,re,enum,dataclasses
HERE=pathlib.Path(__file__).resolve().parent
BASE=HERE.parents[2]
SOURCES=BASE/'frontier/sources/i168_cross_class_exchange'
REPORT=BASE/'frontier/iterations/i168-cross-class-exchange.md'
CONTROLS={HERE/'inventory.json',HERE/'prevalidation.json',HERE/'seal.json'}
CODES={HERE/x for x in ['verify.py','toolkit.py','audit.py','attack.py','support.py']}

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def rel(p):return str(p.relative_to(BASE))
def owned():
    return {p for root in [HERE,SOURCES] for p in root.rglob('*') if p.is_file()}|{REPORT}
def check(entries):
    for x in entries:
        p=BASE/x['path'];assert not p.is_symlink(),('symlink',x['path'])
        assert p.stat().st_size==x['size'] and digest(p)==x['sha256'],('immutable drift',x['path'])
def bindings():
    manifest=HERE/'inventory.json';pre='--prevalidate' in sys.argv
    if pre:assert not (HERE/'seal.json').exists(),'prevalidate prohibited after sealing'
    else:
        seal=json.loads((HERE/'seal.json').read_text())
        assert digest(manifest)==seal['inventory_sha256']
        assert digest(HERE/'prevalidation.json')==seal['prevalidation_sha256']
    inv=json.loads(manifest.read_text());listed={BASE/x['path'] for x in inv['files']}
    assert owned()-CONTROLS==listed,('inventory mismatch',sorted(map(str,(owned()-CONTROLS)^listed)))
    check(inv['files'])
    external=json.loads((SOURCES/'external-bindings.json').read_text())['files']
    policy=json.loads((SOURCES/'replay-policy.json').read_text())
    exclusions=set(policy['context_only_exclusions'])
    assert exclusions=={'frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
    check([x for x in external if x['path'] not in exclusions])
    drift=[]
    for x in external:
        if x['path'] in exclusions:
            p=BASE/x['path'];new=digest(p) if p.exists() else None
            if new!=x['sha256']:drift.append({'path':x['path'],'expected':x['sha256'],'observed':new,'context_only':True})
    return inv,external,drift

def guard(allowed_reads):
    std=pathlib.Path(sysconfig.get_path('stdlib')).resolve()
    # Frozen imports are interpreter-owned standard-library code, not disk executables.
    def stdfile(name):
        if not isinstance(name,str):return False
        if name.startswith('<frozen ') and name.endswith('>'):
            module=name[8:-1].split('.')[0]
            return module in sys.stdlib_module_names or module in {'importlib','_frozen_importlib','_frozen_importlib_external'}
        p=pathlib.Path(name).resolve()
        return p.is_relative_to(std) and 'site-packages' not in p.parts and 'dist-packages' not in p.parts
    def codefile(name):
        return isinstance(name,str) and (pathlib.Path(name).resolve() in CODES or stdfile(name))
    def hook(event,args):
        if event=='open':
            path,mode,flags=args
            if (isinstance(mode,str) and any(c in mode for c in 'wax+')) or (isinstance(flags,int) and flags&(os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND)):
                raise PermissionError('I168 read-only: file write')
            if isinstance(path,(str,bytes,os.PathLike)):
                p=pathlib.Path(os.fsdecode(path)).resolve()
                if p not in allowed_reads and not stdfile(str(p)):
                    raise PermissionError('I168 unbound read: '+str(p))
        if event in {'os.remove','os.rename','os.rmdir','os.mkdir','os.chmod','os.chown','os.truncate','os.link','os.symlink','os.utime','os.chdir','os.fchdir','os.putenv','os.unsetenv'}:
            raise PermissionError('I168 mutation: '+event)
        if event.startswith(('socket.','subprocess.','ctypes.')) or event in {'os.system','os.fork','os.forkpty','os.posix_spawn','os.exec','os.spawn','pty.spawn'}:
            raise PermissionError('I168 external action: '+event)
        if event=='compile' and not codefile(args[1]):raise PermissionError('I168 unowned compilation: '+str(args[1]))
        if event=='exec' and not codefile(args[0].co_filename):raise PermissionError('I168 unowned execution: '+str(args[0].co_filename))
    sys.addaudithook(hook)

def probes():
    tests=[('write',lambda:open(HERE/'forbidden-probe.tmp','w')),
           ('network',lambda:sys.audit('socket.__new__',None,2,1,0)),
           ('subprocess',lambda:os.system('true')),
           ('ancestor execution',lambda:compile('pass',str(BASE/'frontier/experiments/i167_exchange_step_braces/diagnostics.py'),'exec'))]
    result=[]
    for name,f in tests:
        try:f()
        except PermissionError:result.append(name)
        else:raise AssertionError(('guard probe escaped',name))
    return result

def main():
    assert sys.flags.isolated and sys.dont_write_bytecode,'require -I -B'
    start=time.perf_counter();inv,external,drift=bindings()
    receipt={'inventory_sha256':digest(HERE/'inventory.json'),'report_sha256':digest(REPORT),'verifier_sha256':digest(HERE/'verify.py'),'external_bindings_sha256':digest(SOURCES/'external-bindings.json')}
    reads={BASE/x['path'] for x in inv['files']}|{BASE/x['path'] for x in external}|CONTROLS
    sys.path.insert(0,str(HERE));guard(reads);blocked=probes();checks=[]
    for module,payload in [('audit','audit-attempt-02.json'),('attack','attack-attempt-01.json'),('support','support-attempt-02.json')]:
        m=importlib.import_module(module)
        assert pathlib.Path(m.__file__).resolve()==HERE/(module+'.py')
        t=time.perf_counter();result=m.main();expected=(HERE/payload).read_text()
        actual=json.dumps(result,sort_keys=True,indent=2)+'\n'
        assert actual==expected,('deterministic payload mismatch',payload)
        checks.append({'module':module,'payload':payload,'equal':True,'seconds':round(time.perf_counter()-t,6)})
    return {'status':'PASS','mode':'prevalidate' if '--prevalidate' in sys.argv else 'sealed-replay','bindings':receipt,'owned_bytes_verified':len(inv['files']),'external_bytes_verified':len(external)-2,'guard_probes_blocked':blocked,'context_drift_receipt':drift,'diagnostics':checks,'runtime_seconds':round(time.perf_counter()-start,6)}
if __name__=='__main__':print(json.dumps(main(),sort_keys=True,indent=2))
