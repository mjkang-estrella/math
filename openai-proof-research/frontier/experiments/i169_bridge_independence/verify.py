"""Immutable-first I169 replay. Run using python3 -I -B verify.py [--prevalidate]."""
import sys,os,json,hashlib,time,io,contextlib,runpy,sysconfig,types
import socket,subprocess,pathlib,traceback,pkgutil,importlib.util,importlib.machinery
# Preload the numerical standard library before the restrictive execution policy.
import fractions,decimal,math,itertools,functools,collections,tokenize
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
SOURCES=ROOT/'frontier/sources/i169_bridge_independence'
REPORT=ROOT/'frontier/iterations/i169-bridge-independence.md'
CONTROLS={'inventory.json','prevalidation.json','seal.json'}
def digest(data):return hashlib.sha256(data).hexdigest()
def encoded(obj):return (json.dumps(obj,sort_keys=True,indent=2)+'\n').encode()
def load(path):return json.loads(path.read_bytes())
def current_owned():
    return sorted([REPORT]+[p for directory in [HERE,SOURCES] for p in directory.rglob('*') if p.is_file() and not (p.parent==HERE and p.name in CONTROLS)])
def bind(prevalidate):
    inventory=load(HERE/'inventory.json');entry={x['path']:x for x in inventory['files']}
    assert set(entry)=={str(p.relative_to(ROOT)) for p in current_owned()},'owned inventory set mismatch'
    bound={}
    for rel,item in entry.items():
        p=ROOT/rel;data=p.read_bytes();assert len(data)==item['size'] and digest(data)==item['sha256'],rel;bound[str(p.resolve())]=data
    policy=load(SOURCES/'replay-policy.json');exclusions=set(policy['context_only_exclusions']);external=load(SOURCES/'external-bindings.json');drift=[]
    for item in external['files']:
        p=ROOT/item['path'];data=p.read_bytes();actual=digest(data)
        if item['path'] in exclusions:drift.append({'path':item['path'],'bound':item['sha256'],'current':actual,'changed':actual!=item['sha256']})
        else:assert actual==item['sha256'] and len(data)==item['size'],item['path']
        bound[str(p.resolve())]=data
    invhash=digest((HERE/'inventory.json').read_bytes())
    if not prevalidate:
        seal=load(HERE/'seal.json');pre=load(HERE/'prevalidation.json')
        assert seal['inventory_sha256']==invhash
        assert seal['prevalidation_sha256']==digest((HERE/'prevalidation.json').read_bytes())
        assert seal['report_sha256']==digest(REPORT.read_bytes())
        assert seal['verifier_sha256']==digest(Path(__file__).read_bytes())
        assert pre['status']=='PASS' and pre['mode']=='prevalidation' and pre['inventory_sha256']==invhash
    else:
        assert not (HERE/'seal.json').exists(),'prevalidation after sealing forbidden'
    return bound,drift,invhash

def install_guard(bound):
    stdlib=Path(sysconfig.get_path('stdlib')).resolve()
    approved_source={path:data for path,data in bound.items() if Path(path).parent==HERE and (path.endswith('.py') or path.endswith('.py.disabled'))}
    read_paths=set(bound)|{str(HERE/x) for x in CONTROLS}
    def standard(path):
        try:p=Path(path).resolve()
        except (ValueError,TypeError):return False
        return p.is_relative_to(stdlib) and 'site-packages' not in p.parts and 'dist-packages' not in p.parts
    def codepath(path):return path in approved_source or standard(path) or path.startswith('<frozen ')
    forbidden=('socket.','subprocess.','urllib.','http.client.','ctypes.','os.exec','os.spawn','os.posix_spawn')
    mutations={'os.remove','os.unlink','os.rename','os.replace','os.rmdir','os.mkdir','os.chmod','os.chown','os.utime','os.link','os.symlink','os.truncate','os.system','os.fork','os.forkpty','shutil.copyfile','shutil.copymode','shutil.copystat','shutil.rmtree','code.__new__','function.__new__'}
    def hook(event,args):
        if event in mutations or event.startswith(forbidden):raise PermissionError('I169 guard: '+event)
        if event=='open':
            path,mode,flags=args
            if (flags or 0)&(os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND) or isinstance(mode,str) and any(c in mode for c in 'wax+'):
                raise PermissionError('I169 guard: write open')
            if isinstance(path,(str,bytes,os.PathLike)):
                resolved=str(Path(os.fsdecode(path)).resolve())
                if resolved not in read_paths and not standard(resolved):raise PermissionError('I169 guard: unbound read '+resolved)
        if event=='compile':
            source,filename=args
            if not isinstance(filename,str) or not codepath(filename):raise PermissionError('I169 guard: compile outside approved code')
            if filename in approved_source:
                source=source.encode() if isinstance(source,str) else source
                if source!=approved_source[filename]:raise PermissionError('I169 guard: source bytes differ from binding')
        if event=='exec':
            code=args[0]
            if not codepath(code.co_filename):raise PermissionError('I169 guard: execute outside approved code')
    # Compile this deliberately alien code before installing the hook, so exec
    # rejection is tested independently of compile rejection.
    alien=compile('pass','/i169-unowned-exec-probe.py','exec')
    sys.addaudithook(hook)
    probes=[]
    actions=[('write',lambda:open(HERE/'forbidden-write.txt','w')),('filesystem mutation',lambda:os.mkdir(HERE/'forbidden-directory')),('network',lambda:socket.socket()),('subprocess',lambda:subprocess.run([sys.executable,'-c','pass'])),('outside compile',lambda:compile('pass','/i169-unowned-compile-probe.py','exec')),('outside exec',lambda:exec(alien)),('unbound read',lambda:open('/etc/passwd','rb')),('forged owned source',lambda:compile('pass',str(HERE/'toolkit.py'),'exec'))]
    for label,action in actions:
        try:action()
        except PermissionError as e:probes.append({'probe':label,'status':'BLOCKED','reason':str(e)})
        else:raise AssertionError('guard probe unexpectedly succeeded: '+label)
    return probes

def main():
    started=time.monotonic();prevalidate=sys.argv[1:]==['--prevalidate'];assert not sys.argv[1:] or prevalidate
    assert sys.flags.isolated and sys.dont_write_bytecode,'must run python3 -I -B'
    bound,drift,invhash=bind(prevalidate)  # Must finish before diagnostics import.
    probes=install_guard(bound)
    sys.path.insert(0,str(HERE))
    import audit,support,attack
    results=[]
    for name,runner,targets in [('audit',audit.run,['audit-attempt-02.json']),('support',support.run,['support-attempt-01.json','support-attempt-02.json']),('attack',attack.run,['attack-attempt-01.json'])]:
        payload=encoded(runner(ROOT))
        for target in targets:
            expected=bound[str(HERE/target)];assert payload==expected,'payload mismatch '+target
            results.append({'payload':target,'sha256':digest(payload),'status':'BYTE-EQUAL'})
    for source,target in [('explore01.py','explore-attempt-01.json'),('explore02.py','explore-attempt-02.json')]:
        stream=io.StringIO()
        with contextlib.redirect_stdout(stream):runpy.run_path(str(HERE/source),run_name='__main__')
        payload=stream.getvalue().encode();assert payload==bound[str(HERE/target)],'payload mismatch '+target
        results.append({'payload':target,'sha256':digest(payload),'status':'BYTE-EQUAL'})
    result={'status':'PASS','mode':'prevalidation' if prevalidate else 'sealed replay','inventory_sha256':invhash,'report_sha256':digest(bound[str(REPORT)]),'verifier_sha256':digest(bound[str(Path(__file__).resolve())]),'owned_and_external_binding':'COMPLETE before diagnostics','guard_probes':probes,'payloads':results,'context_drift':drift,'runtime_seconds':round(time.monotonic()-started,6)}
    if not prevalidate:result['seal_sha256']=digest((HERE/'seal.json').read_bytes())
    print(json.dumps(result,sort_keys=True,indent=2))

if __name__=='__main__':main()
