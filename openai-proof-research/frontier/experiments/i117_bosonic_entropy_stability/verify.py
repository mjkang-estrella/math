"""Offline read-only replay. No repair, writes, downloads, subprocesses or bytecode.

All owned artifacts, immutable references, inherited package artifacts,
original corpus positions, source views, passages and lexical results are
checked before any diagnostic program is executed. The inherited verifier
is executed only after these checks and also enforces its original bindings.
"""
import sys
sys.dont_write_bytecode=True
import os

def readonly(event,args):
    if event=='open':
        mode=args[1]; flags=args[2] if len(args)>2 else 0
        if (isinstance(mode,str) and any(x in mode for x in 'wax+')) or (isinstance(flags,int) and flags & (os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND)):
            raise RuntimeError('Read-only replay blocked write '+repr(args[0]))
    if event.startswith(('socket.','subprocess.')) or event in {'os.system','os.remove','os.rename','os.rmdir','os.mkdir','os.chmod','os.chown','os.utime','os.truncate','os.link','os.symlink','shutil.copyfile','os.putenv','os.unsetenv','os.exec','os.posix_spawn'}:
        raise RuntimeError('Offline read-only replay blocked '+event)

sys.addaudithook(readonly)
from pathlib import Path
import hashlib,json,re,runpy,io,contextlib

ROOT=Path.cwd().resolve()
S=Path('frontier/sources/i117_bosonic_entropy_stability')
X=Path('frontier/experiments/i117_bosonic_entropy_stability')
R=Path('frontier/iterations/i117-bosonic-entropy-stability.md')
SEAL=S/'seal.json'
OLD=Path('frontier/sources/i114_quantum_information_discovery')
OLDX=Path('frontier/experiments/i114_quantum_information_discovery')
MUTABLE={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'

def require(x,msg):
    if not x:raise AssertionError(msg)
def read(p):
    p=Path(p)
    require(p.is_file() and not p.is_symlink(),'Missing/symlink file '+str(p))
    require(p.resolve().is_relative_to(ROOT),'Path outside root '+str(p))
    return p.read_bytes()
def sha(b):return hashlib.sha256(b).hexdigest()
def load(p):return json.loads(read(p))
def bind(row):
    b=read(row['path'])
    require(sha(b)==row['sha256'],'Immutable hash mismatch '+row['path'])
    if 'bytes' in row:require(len(b)==row['bytes'],'Immutable length mismatch')

def inventory():
    files=[R];dirs=[]
    for base in [S,X]:
        require(base.is_dir() and not base.is_symlink(),'Owned root absent/symlink')
        dirs.append(str(base))
        for p in base.rglob('*'):
            require(not p.is_symlink(),'Owned symlink '+str(p))
            if p.is_dir():dirs.append(str(p))
            elif p.is_file():
                if p!=SEAL:files.append(p)
            else:require(False,'Unexpected owned entry '+str(p))
    return sorted(files),sorted(dirs)

def main():
    require(sys.argv[1:] in [[],['--preseal']],'Only --preseal is allowed')
    preseal=bool(sys.argv[1:]);files,dirs=inventory()
    if preseal:require(not SEAL.exists(),'Cannot preseal an already sealed package')
    else:
        seal=load(SEAL)
        require(seal['schema']=='i117-one-final-seal-v1','Wrong schema')
        require(seal['directories']==dirs,'Exact directory inventory mismatch')
        require([str(p) for p in files]==[x['path'] for x in seal['files']],'Exact file inventory mismatch')
        for row in seal['files']:bind(row)
    refs=load(S/'references.json');drift=[]
    require({x['path'] for x in refs if x['mutable']}==MUTABLE,'Wrong mutable set')
    for x in refs:
        require(sha(read(x['snapshot']))==x['sha256'],'Snapshot changed '+x['path'])
        if x['mutable']:
            if sha(read(x['path']))!=x['sha256']:drift.append(x['path'])
        else:bind(x)
    inherited=load(S/'inherited.json')
    require(inherited['seal_sha256']=='f4850563e1ca604d248e0cf8956aed950aadb2ab6977c3237b53e15897540764','Wrong original seal identity')
    require(sha(read(inherited['seal']))==inherited['seal_sha256'],'Original seal changed')
    for row in inherited['files']:bind(row)
    original_seal=load(inherited['seal'])
    require(original_seal['directories']==inherited['directories'],'Original directory binding changed')
    require(sorted(original_seal['files'],key=lambda x:x['path'])==[x for x in inherited['files'] if x['path']!=inherited['seal']],'Incomplete inherited artifact inventory')
    domain=load(OLD/'search-domain.json')
    tree=load(OLD/'snapshots/sources/preprints-tree.json')
    require(not tree['truncated'] and len(tree['tree'])==13223,'Wrong tree scope')
    blobs={x['path']:x['sha'] for x in tree['tree'] if x['type']=='blob'}
    require(len(domain)==10373 and {x['path'] for x in domain}==set(blobs),'Original position coverage failed')
    queries=load(S/'queries.json');patterns={k:re.compile(v) for k,v in queries.items()}
    hits={k:[] for k in queries};original_bytes=0
    for x in domain:
        require(not any(y in x['local'].lower() for y in ['i112','i113']),'Active working output dependency')
        b=read(x['original_local']);original_bytes+=len(b)
        require(sha(b)==x['original_sha256'],'Original byte binding '+x['path'])
        git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        require(git==x['git_sha']==blobs[x['path']],'Git/tree binding '+x['path'])
        view=b if x['local']==x['original_local'] else read(x['local'])
        require(sha(view)==x['sha256'],'Source view changed '+x['path'])
        for number,line in enumerate(view.decode('utf-8',errors='replace').splitlines(),1):
            for key,pat in patterns.items():
                for mt in pat.finditer(line):hits[key].append(dict(path=x['path'],local=x['local'],line_splitlines=number,start=mt.start(),end=mt.end(),match=mt.group(),text=line))
    for key,rows in hits.items():require(rows==load(S/('search-'+key+'.json')),'Exact lexical occurrence multiset/order '+key)
    titles=load(S/'title-screen.json');roots=sorted({x['path'].split('/')[1] for x in tree['tree']})
    require(len(roots)==titles['roots']==749,'Wrong manuscript count')
    require([x for x in roots if re.search(titles['expression'],x,re.I)]==titles['matches'],'Title expression results changed')
    dm={x['path']:x for x in domain};passages=[]
    manifest=load(S/'read-manifest.json')['reads']
    for x in manifest:
        b=read(x['local']);ls=b.decode('utf-8',errors='replace').splitlines()
        require((sha(b),len(b),b.count(b'\n'),len(ls),b.endswith(b'\n'))==(x['sha256'],x['bytes'],x['lf_count'],x['splitlines_count'],x['ends_lf']),'Source/line convention changed '+x['local'])
        if 'domain_path' in x:
            require(dm[x['domain_path']]['local']==x['local'],'Original source mapping mismatch')
            require(x['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+x['domain_path'],'Unpinned original URL')
        for a,z in x['ranges_inclusive_splitlines']:
            require(1<=a<=z<=len(ls),'Passage range invalid')
            txt='\n'.join(ls[a-1:z]);passages.append(dict(local=x['local'],source_sha256=x['sha256'],start_splitlines=a,end_splitlines=z,text=txt,passage_utf8_sha256=sha(txt.encode())))
    require(passages==load(S/'passages.json'),'Exact passage hashes/text mismatch')
    for path in MUTABLE:
        lines=read(S/'snapshots'/path).decode(errors='replace').splitlines()
        for row in load(S/(path.replace('/','_')+'.read-extract.json')):
            require(lines[row['line']-1]==row['text'],'Frozen ledger extract mismatch')
    # Conversion code is already bound by the inherited inventory above.
    convert=runpy.run_path(str(OLDX/'html_text.py'))['convert']
    html_count=0
    for p in sorted((S/'external').glob('*.html')):
        require(convert(read(p).decode(errors='replace')).encode()==read(p.with_suffix('.txt')),'HTML conversion mismatch')
        html_count+=1
    for row in load(S/'http-log.json'):
        if row.get('status')==200:
            b=read(S/'external'/(row['name']+'.html'))
            require(sha(b)==row['sha256'] and len(b)==row['bytes'],'HTTP response identity changed')
    require(read(S/'external/li-v1.txt')==read(OLD/'external/li-html.txt'),'Fresh Li text differs from inherited version')
    # No diagnostic program has run before this point. The original verifier
    # now rechecks all its immutable references and exact searches before
    # running its own finite diagnostics. Restore argv only in memory.
    saved=sys.argv[:];sys.argv=[str(OLDX/'verify.py')]
    output=io.StringIO()
    try:
        with contextlib.redirect_stdout(output):runpy.run_path(str(OLDX/'verify.py'),run_name='__main__')
    finally:sys.argv=saved
    old_result=json.loads(output.getvalue());require(old_result['status']=='PASS','Inherited replay failed')
    diagnostics=runpy.run_path(str(X/'check.py'))['run']()
    require(diagnostics['status']=='PASS','New diagnostic failure')
    if not preseal:
        prior=load(S/'preseal-validation.json')
        require(prior['status']=='PASS' and prior['mode']=='preseal','No successful preseal validation')
        require(prior['diagnostics']==diagnostics,'Diagnostics differ from preseal')
    result=dict(status='PASS',mode='preseal' if preseal else 'sealed-read-only',
                owned_files_without_seal=len(files),owned_directories=len(dirs),
                original_positions=len(domain),original_bytes=original_bytes,
                inherited_lexical_occurrences=old_result['lexical_occurrences'],
                lexical_occurrences={k:len(v) for k,v in hits.items()},read_sources=len(manifest),
                passages=len(passages),html_views=html_count,permitted_mutable_drift=sorted(drift),
                inherited_status=old_result['status'],diagnostics=diagnostics,
                scope='Provenance and finite exact diagnostics only; analytic verdicts are in the report, not certified by this replay')
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=='__main__':main()
