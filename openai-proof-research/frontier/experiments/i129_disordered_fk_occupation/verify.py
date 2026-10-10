"""Offline read-only verification: all immutable evidence before diagnostics.

I126's hash-bound immutable-validation prefix is adapted structurally; its
recursive replay is never executed. I123's flat corpus engine runs once.
This program has no acquisition, write, repair, seal, or reseal path.
"""
import sys
sys.dont_write_bytecode=True
import os


def readonly(event,args):
    if event=='open':
        mode=args[1];flags=args[2] if len(args)>2 else 0
        if ((isinstance(mode,str) and any(c in mode for c in 'wax+')) or
            (isinstance(flags,int) and flags & (os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND))):
            raise RuntimeError('Read-only replay blocked write: '+repr(args[0]))
    if event.startswith(('socket.','subprocess.')) or event in {
        'os.system','os.remove','os.rename','os.rmdir','os.mkdir','os.chmod','os.chown',
        'os.utime','os.truncate','os.link','os.symlink','shutil.copyfile',
        'os.putenv','os.unsetenv','os.exec','os.posix_spawn'}:
        raise RuntimeError('Offline read-only replay blocked '+event)


sys.addaudithook(readonly)
import ast,contextlib,hashlib,io,json,re,runpy
from pathlib import Path
ROOT=Path.cwd().resolve()
S=Path('frontier/sources/i129_disordered_fk_occupation')
X=Path('frontier/experiments/i129_disordered_fk_occupation')
R=Path('frontier/iterations/i129-disordered-fk-occupation.md')
V126=Path('frontier/experiments/i126_random_geometry_discovery/verify.py')
SHA126='606c6162a25f2ca4f0af38b8cc985f9b203863296dbf19d335cd596f1676d8fd'
V123=Path('frontier/experiments/i123_thermal_production_stability/verify.py')
SHA123='feef6639e9a4c9916f4b845f771263e795a25fbee83227c0716e339d7a5ef4c3'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
MUTABLE={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}


def require(ok,msg):
    if not ok:raise AssertionError(msg)


def read(p):
    p=Path(p)
    require(p.is_file() and not p.is_symlink() and p.resolve().is_relative_to(ROOT),'Missing/symlink/outside '+str(p))
    return p.read_bytes()


def sha(b):return hashlib.sha256(b).hexdigest()
def load(p):return json.loads(read(p))
def row(p):
    b=read(p);return dict(path=str(p),sha256=sha(b),bytes=len(b))


def inventory():
    files=[str(R)];dirs=[]
    for root in (S,X):
        require(root.is_dir() and not root.is_symlink(),'Owned root')
        dirs.append(str(root))
        for p in root.rglob('*'):
            require(not p.is_symlink(),'Owned symlink')
            if p.is_dir():dirs.append(str(p))
            elif p.is_file() and p!=S/'seal.json':files.append(str(p))
            elif p!=S/'seal.json':require(False,'Unexpected object '+str(p))
    require(len(files)==len(set(files)) and len(dirs)==len(set(dirs)),'Duplicate inventory')
    return sorted(files),sorted(dirs)


def validate_i126_without_replay():
    source=read(V126)
    require(sha(source)==SHA126,'Exact original I126 verifier')
    tree=ast.parse(source,filename=str(V126))
    mains=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='main']
    require(len(mains)==1,'I126 structural main')
    main=mains[0]
    cuts=[i for i,n in enumerate(main.body) if isinstance(n,ast.Assign) and
          any(isinstance(t,ast.Name) and t.id=='saved_args' for t in n.targets)]
    require(len(cuts)==1,'I126 immutable-prefix cut')
    # Every statement before this cut is an immutable check. The original
    # saved_args assignment starts its I123 replay and subsequent diagnostics.
    prefix=main.body[:cuts[0]]
    require(not any(isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute)
                    and n.func.attr=='run_path' and any(isinstance(a,ast.Call) for a in n.args)
                    for stmt in prefix for n in ast.walk(stmt)), 'Unexpected dynamic replay in prefix')
    main.body=prefix+ast.parse("return dict(files=len(files), reads=len(records), lexical=len(result), drift=sorted(drift))").body
    require(isinstance(tree.body[-1],ast.If),'I126 original entrypoint')
    tree.body.pop()  # Do not execute original entrypoint or recursive replay.
    ast.fix_missing_locations(tree)
    namespace={'__name__':'i126_immutable_prefix','__file__':str(V126)}
    exec(compile(tree,str(V126)+' [immutable prefix only]','exec'),namespace)
    saved=sys.argv;sys.argv=[str(V126)]
    try:return namespace['main']()
    finally:sys.argv=saved


def main():
    require(sys.argv[1:] in ([],['--preseal']),'Only --preseal supported')
    preseal=bool(sys.argv[1:]);files,dirs=inventory()
    require(files==sorted(set(files)) and dirs==sorted(set(dirs)),'Globally sorted exact inventory')
    validated=[row(p) for p in files if p!=str(S/'preseal-validation.json')]
    if preseal:require(not (S/'seal.json').exists(),'Preseal refuses existing seal')
    else:
        seal=load(S/'seal.json')
        require(seal['schema']=='i129-one-final-seal-v1','Seal schema')
        require(seal['globally_sorted_exact_inventory'] is True,'Explicit global inventory assertion')
        require(seal['directories']==dirs and seal['files']==[row(p) for p in files],'Exact owned inventory and all bytes')
        receipt=load(S/'preseal-validation.json')
        require(receipt['status']=='PASS' and receipt['validated_files']==validated,'Preseal exact final immutable bytes')
    deps=load(S/'engine-dependencies.json')
    require([r['path'] for r in deps]==sorted(set(r['path'] for r in deps)),'Dependency order')
    for r in deps:require(row(r['path'])==r,'Immutable execution dependency '+r['path'])
    require(sha(read(V123))==SHA123,'Flat engine identity')
    refs=load(S/'references.json');drift=[]
    require({r['path'] for r in refs if r['mutable']}==MUTABLE,'Only four mutable ledgers')
    require(len(refs)==len({r['path'] for r in refs}),'Duplicate references')
    for r in refs:
        require(not re.search(r'(?:/i|/iteration)(127|128)(?:[-_/])',r['path']),'Active output bound')
        require(row(r['snapshot'])==dict(path=r['snapshot'],sha256=r['sha256'],bytes=r['bytes']),'Immutable snapshot')
        if r['mutable']:
            if sha(read(r['path']))!=r['sha256']:drift.append(r['path'])
        else:require(row(r['path'])==dict(path=r['path'],sha256=r['sha256'],bytes=r['bytes']),'Original immutable reference '+r['path'])
    manifest=load(S/'read-manifest.json')
    domain=load('frontier/sources/i114_quantum_information_discovery/search-domain.json')
    require(len(domain)==10373,'Original position count')
    bypath={r['path']:r for r in domain}
    for r in manifest:
        b=read(r['local']);raw=b.decode('utf-8')
        require((sha(b),len(b),b.count(b'\n'),len(raw.splitlines()),b.endswith(b'\n'))==
                (r['sha256'],r['bytes'],r['lf_count'],r['splitlines_count'],r['ends_lf']),'Read bytes and conventions '+r['local'])
        t=json.loads(raw)[r['field']] if r['field'] is not None else raw
        if not isinstance(t,str):t=json.dumps(t,indent=2,ensure_ascii=False)
        ls=t.splitlines();a,z=r['start'],r['end']
        require(len(ls)==r['decoded_lines'] and 1<=a<=z<=len(ls),'Decoded lines')
        require(sha('\n'.join(ls[a-1:z]).encode())==r['range_sha256'],'Read range hash')
        if 'domain_path' in r:
            require(bypath[r['domain_path']]['local']==r['local'],'Original source mapping')
            require(r['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+r['domain_path'],'Pinned source URL')
    task_hashes={
        '126-random-geometry-discovery':'38e2d007ce9cb236a9601392a586e72263279bdc28744e394d8997cd457f6651',
        '123-thermal-production-stability':'c0a4216b88cf7bde8e7ff4517c0d4fb2144e5457d1ab57fc5315f1d739653172',
        '120-thermal-trace-stability':'d1b09ad8939c4842ddba3c672336e31f52ea6b0ec0433ac6e0ace2cbacad292d'}
    for suffix,digest in task_hashes.items():
        p='frontier/iterations/iteration'+suffix+'-task.json';require(sha(read(p))==digest,'Required recursive original hash')
        for k,v in load(p).items():
            t=v if isinstance(v,str) else json.dumps(v,indent=2,ensure_ascii=False)
            covered={i for r in manifest if r['local'] in (p,str(S/'snapshots'/p)) and r['field']==k for i in range(r['start'],r['end']+1)}
            require(covered==set(range(1,len(t.splitlines())+1)),'All decoded fields covered '+p+':'+k)
    brief=load(S/'snapshots/frontier/iterations/iteration129-disordered-fk-occupation-task.json')['brief']
    original=brief.split('--- ORIGINAL I126 REPORT ---\n',1)[1].split('\n--- FINALIZED PARENT RESPONSE ---',1)[0]
    require(original.strip()==read(S/'snapshots/frontier/iterations/i126-random-geometry-discovery.md').decode().strip(),'Exact original report in supplied context')
    parent=json.loads(brief.split('--- FINALIZED PARENT RESPONSE ---\n',1)[1])
    require(parent==load(S/'snapshots/frontier/experiments/i126-parent-verification.json'),'Full finalized original parent response')
    roots=load(S/'family-roots.json')
    require(roots==sorted(set(roots)) and len(roots)==3,'Selected roots')
    require(load(S/'selected-inventory.json')==[r for r in domain if r['path'].split('/')[1] in roots],'Complete selected source inventory')
    lexical=load(S/'lexical-query.json');require(lexical['files']==sorted(set(lexical['files'])),'Lexical file order')
    results=[];regex=re.compile(lexical['pattern'],re.I)
    for p in lexical['files']:
        require(not re.search(r'(?:/i|/iteration)(127|128)(?:[-_/])',p),'Active lexical dependency')
        for n,line in enumerate(read(p).decode().splitlines(),1):
            for m in regex.finditer(line):results.append(dict(path=p,line=n,start=m.start(),end=m.end(),text=m.group(),line_text=line))
    require(results==load(S/'lexical-results.json'),'Exact lexical occurrence multiset')
    converter=runpy.run_path('frontier/experiments/i114_quantum_information_discovery/html_text.py')['convert']
    views=load(S/'html-views.json');http=load(S/'http-log.json')
    require(len(views)==6 and len(http)==6,'All acquired views')
    for v in views:
        require(sha(read(v['html']))==v['html_sha256'] and sha(read(v['text']))==v['text_sha256'],'HTML/text binding')
        require(converter(read(v['html']).decode())==read(v['text']).decode(),'Deterministic HTML conversion')
        rr=[r for r in http if r.get('local')==v['html']]
        require(len(rr)==1 and rr[0]['status']==200 and rr[0]['sha256']==v['html_sha256'] and rr[0]['bytes']==len(read(v['html'])),'HTTP provenance')
    # Original I126 immutable checks only, with no nested execution.
    inherited126=validate_i126_without_replay()
    # The flat engine now checks ALL remaining inherited immutable bytes and
    # corpus/PDF bindings, and only then starts any diagnostic program.
    saved=sys.argv;sys.argv=[str(V123)];capture=io.StringIO()
    try:
        with contextlib.redirect_stdout(capture):runpy.run_path(str(V123),run_name='__main__')
    finally:sys.argv=saved
    inherited=json.loads(capture.getvalue())
    require(inherited['status']=='PASS' and inherited['corpus_traversals']==1 and inherited['original_positions']==10373,'One complete flat traversal')
    require(inherited['domain_kinds']['outside_pdf']==776,'All inherited PDF bindings')
    diag126=runpy.run_path('frontier/experiments/i126_random_geometry_discovery/check.py')['run']()
    diag129=runpy.run_path(str(X/'check.py'))['run']()
    print(json.dumps(dict(status='PASS',mode='preseal-read-only' if preseal else 'sealed-read-only',
        globally_sorted_exact_inventory=True,all_immutable_checks_before_diagnostics=True,
        corpus_traversals=1,original_positions=inherited['original_positions'],original_bytes=inherited['original_bytes'],
        domain_kinds=inherited['domain_kinds'],i126_immutable_prefix=inherited126,
        inherited_diagnostics=inherited['diagnostics'],i126_diagnostics=diag126,i129_diagnostics=diag129,
        inherited_lexical_occurrences=inherited['inherited_lexical_occurrences'],own_lexical_occurrences=len(results),
        own_read_records=len(manifest),own_html_views=len(views),owned_files_without_seal=len(files),owned_directories=len(dirs),
        permitted_mutable_drift=sorted(drift),validated_files=validated,
        scope='Immutable evidence and finite diagnostics; no universal proof, fixed-disorder limit or substantiality certification'),indent=2))


if __name__=='__main__':main()
