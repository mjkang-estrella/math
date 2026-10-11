"""I170 immutable-first, read-only, byte-exact replay. Standard library only."""
import sys, os, json, hashlib, time, types, pathlib, sysconfig, socket, subprocess
import itertools, math, fractions, functools, importlib.util, gc
BASE=pathlib.Path(__file__).resolve().parent
ROOT=BASE.parents[2]
SOURCES=ROOT/'frontier/sources/i170_quadrilateral_coefficient'
REPORT=ROOT/'frontier/iterations/i170-quadrilateral-coefficient.md'
CONTROLS={BASE/'inventory.json',BASE/'prevalidation.json',BASE/'seal.json'}

def digest(b):return hashlib.sha256(b).hexdigest()
def encode(d):return (json.dumps(d,sort_keys=True,indent=2)+'\n').encode()
def owned_files():
    return sorted([REPORT]+[p for directory in (BASE,SOURCES) for p in directory.rglob('*') if p.is_file() and p not in CONTROLS])

def main():
    start=time.monotonic();pre=sys.argv[1:]==['--prevalidate']
    invraw=(BASE/'inventory.json').read_bytes();inv=json.loads(invraw)
    seal=None
    if not pre:
        assert len(sys.argv)==3 and sys.argv[1]=='--seal-sha256','Supply --prevalidate or --seal-sha256 HASH'
        raw=(BASE/'seal.json').read_bytes();assert digest(raw)==sys.argv[2],'seal anchor mismatch';seal=json.loads(raw)
        assert seal['inventory_sha256']==digest(invraw)
        pvraw=(BASE/'prevalidation.json').read_bytes();assert seal['prevalidation_sha256']==digest(pvraw)
        pv=json.loads(pvraw);assert pv['status']=='PASS' and pv['inventory_sha256']==digest(invraw)
    records={ROOT/z['path']:z for z in inv['files']}
    assert set(records)==set(owned_files()),'owned inventory set changed'
    bound={};owned=set(records)
    for path,z in records.items():
        raw=path.read_bytes();assert len(raw)==z['size'] and digest(raw)==z['sha256'],str(path)
        bound[path]=raw
    assert (ROOT/inv['report'])==REPORT
    if seal:
        assert seal['report_sha256']==digest(bound[REPORT])
        assert seal['verifier_sha256']==digest(bound[BASE/'verify.py'])
    policy=json.loads(bound[SOURCES/'replay-policy.json']);contexts=set(policy['context_only_exclusions'])
    ext=json.loads(bound[SOURCES/'external-bindings.json']);drift=[]
    for z in ext['files']:
        path=ROOT/z['path'];raw=path.read_bytes();actual=digest(raw)
        if z['path'] in contexts:
            if actual!=z['sha256']:drift.append({'path':z['path'],'bound':z['sha256'],'current':actual,'status':'context-only drift'})
        else:assert actual==z['sha256'] and len(raw)==z['size'],z['path']
        bound[path]=raw
    for path in CONTROLS:
        if path.exists():bound[path]=path.read_bytes()
    # No diagnostic source has been compiled or executed before all the bindings above.
    trusted=pathlib.Path(sysconfig.get_path('stdlib')).resolve()
    original_open=open
    guarded_exec_ids=set();inside=False
    def pathof(p):
        if isinstance(p,int):return None
        try:return pathlib.Path(os.fsdecode(p)).resolve()
        except (TypeError,ValueError):raise PermissionError('unrecognized file target')
    def isstdlib(p):
        return p is not None and trusted in p.parents and 'site-packages' not in p.parts and 'dist-packages' not in p.parts
    def hook(event,args):
        nonlocal inside
        if inside:return
        if event=='open':
            target,mode,flags=args
            if (mode and any(c in mode for c in 'wax+')) or (flags & (os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND)):
                raise PermissionError('read-only audit: write open')
            p=pathof(target)
            if p is None:raise PermissionError('unbound fd read')
            if p not in bound and not isstdlib(p):raise PermissionError('unbound read: '+str(p))
            if p in bound:
                inside=True
                try:
                    with original_open(p,'rb') as f:raw=f.read()
                finally:inside=False
                if raw!=bound[p]:raise PermissionError('bound read drift: '+str(p))
        elif event.startswith(('socket.','subprocess.')) or event in {'os.system','os.posix_spawn','os.posix_spawnp','os.fork','os.forkpty','os.exec','pty.spawn'}:
            raise PermissionError('network/process blocked: '+event)
        elif event in {'os.remove','os.unlink','os.rename','os.rmdir','os.mkdir','os.link','os.symlink','os.chmod','os.chown','os.utime','os.truncate','os.chdir','os.putenv','os.unsetenv'} or event.startswith('shutil.'):
            raise PermissionError('mutation blocked: '+event)
        elif event=='compile':
            source,filename=args;p=pathof(filename)
            if isinstance(source,str):source=source.encode()
            if not isinstance(source,bytes):raise PermissionError('AST compilation not authorized')
            if p in owned and (str(p).endswith('.py') or str(p).endswith('.py.disabled')):
                if source!=bound[p]:raise PermissionError('forged owned source')
            elif isstdlib(p):
                with original_open(p,'rb') as f:actual=f.read()
                if source!=actual:raise PermissionError('forged stdlib source')
            else:raise PermissionError('outside compile')
        elif event=='exec':
            code=args[0];p=pathof(code.co_filename)
            if id(code) not in guarded_exec_ids and not isstdlib(p) and not code.co_filename.startswith('<frozen '):
                raise PermissionError('outside exec')
        elif event in {'code.__new__','ctypes.dlopen','ctypes.dlsym'}:raise PermissionError('dynamic native/code construction blocked')
    outside=compile('pass','<i170-outside-probe>','exec')
    sys.addaudithook(hook)
    probes={}
    def probe(name,fn):
        try:fn()
        except PermissionError:probes[name]='BLOCKED'
        else:raise AssertionError('guard failed '+name)
    probe('write',lambda:open(BASE/'guard-probe-never-created','w'))
    probe('mutation',lambda:os.mkdir(BASE/'guard-directory-never-created'))
    probe('network',lambda:socket.socket())
    probe('subprocess',lambda:subprocess.run([sys.executable,'--version']))
    probe('outside_compile',lambda:compile('x=1','<outside>','exec'))
    probe('outside_exec',lambda:exec(outside,{}))
    probe('unbound_read',lambda:open(ROOT/'sources/tree.json','rb'))
    probe('forged_owned_source',lambda:compile('forged=True',str(BASE/'core.py'),'exec'))
    def register(code):
        guarded_exec_ids.add(id(code))
        for x in code.co_consts:
            if isinstance(x,types.CodeType):register(x)
    def load(filename,name):
        p=BASE/filename;raw=bound[p];code=compile(raw,str(p),'exec');register(code)
        m=types.ModuleType(name);m.__file__=str(p);exec(code,m.__dict__);return m
    jobs=[
      ('audit-attempt-01.py.disabled','core-attempt-01.py.disabled','audit-attempt-01.json'),
      ('prism-attempt-01.py.disabled','core-attempt-01.py.disabled','prism-attempt-01.json'),
      ('coefficient-attempt-01.py.disabled','core-attempt-01.py.disabled','coefficient-attempt-01.json'),
      ('residual-attempt-01.py.disabled','core-attempt-01.py.disabled','residual-attempt-01.json'),
      ('residual-attempt-02.py.disabled','core-attempt-02.py.disabled','residual-attempt-02.json'),
      ('residual.py','core.py','residual-attempt-03.json'),
      ('longscan.py','core.py','longscan-attempt-01.json')]
    results=[];cores={}
    for module,core,payload in jobs:
        if core not in cores:cores[core]=load(core,core)
        m=load(module,module);output=m.run(cores[core],ROOT);raw=encode(output)
        assert raw==bound[BASE/payload],'non-deterministic or mismatched payload: '+payload
        results.append({'payload':payload,'sha256':digest(raw),'byte_equality':'PASS'})
        del output,raw,m;gc.collect()
    # Current authoritative sources must match the audited versions.
    for name in ('audit','prism','coefficient','longscan'):
        assert bound[BASE/(name+'.py')]==bound[BASE/(name+'-attempt-01.py.disabled')]
    assert bound[BASE/'core.py']==bound[BASE/'core-attempt-02.py.disabled']
    assert bound[BASE/'residual.py']==bound[BASE/'residual-attempt-03.py.disabled']
    assert bound[BASE/'residual-attempt-02.json']==bound[BASE/'residual-attempt-03.json']
    receipt={'status':'PASS','mode':'prevalidate' if pre else 'sealed replay','inventory_sha256':digest(invraw),'report_sha256':digest(bound[REPORT]),'verifier_sha256':digest(bound[BASE/'verify.py']),'guard_probes':probes,'payloads':results,'context_drift':drift,'owned_bound_files':len(records),'external_bound_files':len(ext['files']),'runtime_seconds':round(time.monotonic()-start,6)}
    print(json.dumps(receipt,sort_keys=True,indent=2))
if __name__=='__main__':main()
