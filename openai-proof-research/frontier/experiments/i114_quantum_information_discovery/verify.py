"""Offline READ-ONLY provenance and exact-diagnostic replay.

No downloads, writes, bytecode, subprocesses, repair, or resealing. Run from
the repository root with python -B. --preseal validates before the one seal
exists; the default additionally enforces its exact owned inventory.
This program does not certify universal mathematical truth or significance.
"""
import sys
sys.dont_write_bytecode = True
import os

def readonly_audit(event, args):
    if event == 'open':
        mode = args[1]
        flags = args[2] if len(args) > 2 else 0
        if (isinstance(mode,str) and any(c in mode for c in 'wax+')) or (isinstance(flags,int) and flags & (os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND)):
            raise RuntimeError('Read-only verifier blocked write: '+repr(args[0]))
    if event.startswith(('socket.', 'subprocess.')) or event in {
        'os.system','os.remove','os.rename','os.rmdir','os.mkdir','os.chmod',
        'os.chown','os.utime','os.truncate','os.link','os.symlink','shutil.copyfile',
        'os.putenv','os.unsetenv','os.exec','os.posix_spawn',
    }:
        raise RuntimeError('Offline read-only verifier blocked '+event)

sys.addaudithook(readonly_audit)
from pathlib import Path
import hashlib
import json
import re
import runpy

ROOT = Path.cwd().resolve()
SOURCE = Path('frontier/sources/i114_quantum_information_discovery')
EXPERIMENT = Path('frontier/experiments/i114_quantum_information_discovery')
REPORT = Path('frontier/iterations/i114-quantum-information-discovery.md')
SEAL = SOURCE/'seal.json'
MUTABLE = {'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'

def require(value, message):
    if not value: raise AssertionError(message)

def read(path):
    p = Path(path)
    require(p.is_file() and not p.is_symlink(), 'Missing/symlink file '+str(p))
    require(p.resolve().is_relative_to(ROOT), 'Outside repository '+str(p))
    return p.read_bytes()

def load(path):
    return json.loads(read(path))

def digest(b):
    return hashlib.sha256(b).hexdigest()

def inventory():
    files = [REPORT]; directories = []
    for base in [SOURCE,EXPERIMENT]:
        require(base.is_dir() and not base.is_symlink(), 'Missing/symlink owned root')
        directories.append(str(base))
        for p in base.rglob('*'):
            require(not p.is_symlink(), 'Owned symlink '+str(p))
            if p.is_dir(): directories.append(str(p))
            elif p.is_file():
                if p != SEAL: files.append(p)
            else: require(False,'Unexpected owned entry '+str(p))
    return sorted(files), sorted(directories)

def main():
    require(sys.argv[1:] in [[], ['--preseal']], 'Only --preseal is allowed')
    preseal = bool(sys.argv[1:])
    files, directories = inventory()
    if preseal:
        require(not SEAL.exists(), 'Preseal validation refuses an existing seal')
    else:
        seal = load(SEAL)
        require(seal['schema']=='i114-one-final-seal-v1','Wrong seal schema')
        require(seal['directories']==directories,'Owned directory inventory changed')
        expected = seal['files']
        require([str(p) for p in files]==[x['path'] for x in expected], 'Exact owned file inventory changed')
        for p,x in zip(files,expected):
            b=read(p)
            require(len(b)==x['bytes'] and digest(b)==x['sha256'], 'Owned hash mismatch '+str(p))
    inputs=load(SOURCE/'inputs.json')
    require({x['path'] for x in inputs if x['mutable']}==MUTABLE,'Unexpected mutable-reference set')
    require(len({x['path'] for x in inputs})==len(inputs),'Duplicate reference path')
    drift=[]
    for x in inputs:
        require('i112' not in x['path'].lower() and 'i113' not in x['path'].lower(), 'Forbidden active dependency')
        require(digest(read(x['snapshot']))==x['sha256'],'Frozen reference changed '+x['path'])
        live=digest(read(x['path']))
        if x['mutable']:
            if live!=x['sha256']: drift.append(x['path'])
        else: require(live==x['sha256'],'Immutable live reference changed '+x['path'])
    require(load(SOURCE/'snapshots/sources/upstream.json')['commit']==PIN,'Wrong stipulated revision')
    tree=load(SOURCE/'snapshots/sources/preprints-tree.json')
    require(tree['truncated'] is False and len(tree['tree'])==13223,'Incomplete tree')
    blobs={x['path']:x['sha'] for x in tree['tree'] if x['type']=='blob'}
    require(len(blobs)==10373,'Original blob count changed')
    domain=load(SOURCE/'search-domain.json')
    require(domain==load(SOURCE/'snapshots/frontier/sources/i88_nonlinear_banach_discovery/search-domain.json'),'Augmented mapping changed')
    require(len(domain)==10373 and len({x['path'] for x in domain})==10373,'Duplicate/missing domain positions')
    require({x['path'] for x in domain}==set(blobs),'Domain does not equal full tree blob set')
    queries=load(SOURCE/'queries.json'); patterns={k:re.compile(v) for k,v in queries.items()}
    hits={k:[] for k in patterns}; kinds={}; byte_total=0
    for x in domain:
        require('i112' not in x['local'].lower() and 'i113' not in x['local'].lower(),'Forbidden active source')
        original=read(x['original_local']); byte_total+=len(original)
        require(digest(original)==x['original_sha256'],'Original SHA-256 mismatch '+x['path'])
        git=hashlib.sha1(b'blob '+str(len(original)).encode()+b'\0'+original).hexdigest()
        require(git==x['git_sha']==blobs[x['path']],'Original Git blob mismatch '+x['path'])
        b=original if x['original_local']==x['local'] else read(x['local'])
        require(digest(b)==x['sha256'],'Search view mismatch '+x['path'])
        kinds[x['kind']]=kinds.get(x['kind'],0)+1
        for number,line in enumerate(b.decode('utf-8',errors='replace').splitlines(),1):
            for name,pattern in patterns.items():
                for match in pattern.finditer(line):
                    hits[name].append(dict(path=x['path'],local=x['local'],line_splitlines=number,start=match.start(),end=match.end(),match=match.group(),text=line))
    require(kinds=={'corpus':9340,'outside_pdf':776,'outside_bytes':257},'Domain kind counts changed')
    for name,rows in hits.items():
        require(rows==load(SOURCE/('search-'+name+'.json')),'Exact lexical occurrence multiset/order changed '+name)
    require({k:len(v) for k,v in hits.items()}=={'topics':98,'stability':143},'Lexical hit count changed')
    corpus_base=Path('frontier/sources/i14_spectral_width_novelty_r3/corpus')
    corpus_paths=sorted(str(p) for p in corpus_base.rglob('*') if p.is_file())
    require(corpus_paths==load(SOURCE/'corpus-rg-inventory.json'),'Original rg corpus inventory changed')
    require(set(corpus_paths)=={x['original_local'] for x in domain if x['kind']=='corpus'},'Corpus/domain mismatch')
    title=load(SOURCE/'title-screen.json')
    roots={x['path'].split('/')[1] for x in tree['tree']}
    require(len(roots)==title['roots']==749,'Manuscript root count changed')
    require(sorted(x for x in roots if re.search(title['expression'],x))==title['matches'],'Full-tree title expression mismatch')
    selected=load(SOURCE/'selected-inventory.json')
    require(selected==[x for x in domain if x['path'].split('/')[1] in title['matches']],'Selected pinned inventory mismatch')
    source_map={x['path']:x for x in domain}
    manifest=load(SOURCE/'read-manifest.json')
    for x in manifest['reads']:
        b=read(x['local']); lines=b.decode('utf-8',errors='replace').splitlines()
        require((digest(b),len(b),b.count(b'\n'),len(lines),b.endswith(b'\n'))==(x['sha256'],x['bytes'],x['lf_count'],x['splitlines_count'],x['ends_lf']),'Read-source identity/convention mismatch')
        if 'domain_path' in x:
            require(source_map[x['domain_path']]['local']==x['local'],'Read source mapping mismatch')
            require(x['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+x['domain_path'],'Unpinned source URL')
    expected_passages=[]
    for x in manifest['reads']:
        lines=read(x['local']).decode('utf-8',errors='replace').splitlines()
        for start,end in x['ranges_inclusive_splitlines']:
            require(1<=start<=end<=len(lines),'Invalid passage range')
            text='\n'.join(lines[start-1:end])
            expected_passages.append(dict(local=x['local'],source_sha256=x['sha256'],start_splitlines=start,end_splitlines=end,text=text,passage_utf8_sha256=digest(text.encode())))
    require(expected_passages==load(SOURCE/'passages.json'),'Exact source passages changed')
    for path in MUTABLE:
        excerpt=load(SOURCE/(path.replace('/','_')+'.read-extract.json'))
        frozen=(SOURCE/'snapshots'/path).read_bytes().decode('utf-8',errors='replace').splitlines()
        require(all(frozen[x['line']-1]==x['text'] for x in excerpt),'Ledger excerpt mismatch '+path)
    convert=runpy.run_path(str(EXPERIMENT/'html_text.py'))['convert']
    html_count=0
    for p in sorted((SOURCE/'external').glob('*.html')):
        require(convert(read(p).decode('utf-8',errors='replace')).encode()==read(p.with_suffix('.txt')),'HTML conversion mismatch '+str(p))
        html_count+=1
    for x in load(SOURCE/'http-log.json'):
        if x.get('status')==200:
            suffix='.tex' if x['url'].endswith('.tex') else '.html'
            b=read(SOURCE/'external'/(x['name']+suffix))
            require(digest(b)==x['sha256'] and len(b)==x['bytes'],'HTTP acquisition identity mismatch '+x['name'])
            if suffix=='.tex':
                path='preprints/'+x['url'].split('/preprints/',1)[1]
                require(b==read(source_map[path]['original_local']),'Fresh pinned/current source no longer matches saved original')
    diagnostics=runpy.run_path(str(EXPERIMENT/'check.py'))['run']()
    require(diagnostics['status']=='PASS','Diagnostic failure')
    if not preseal:
        validation=load(SOURCE/'preseal-validation.json')
        require(validation['status']=='PASS' and validation['mode']=='preseal','Missing prior successful validation')
        require(validation['diagnostics']==diagnostics,'Diagnostic result changed since validation')
    result=dict(status='PASS',mode='preseal' if preseal else 'sealed-read-only',owned_files_without_seal=len(files),owned_directories=len(directories),immutable_reference_count=sum(not x['mutable'] for x in inputs),permitted_mutable_drift=sorted(drift),original_positions=len(domain),original_bytes=byte_total,domain_kinds=kinds,lexical_occurrences={k:len(v) for k,v in hits.items()},read_sources=len(manifest['reads']),passages=len(expected_passages),html_views=html_count,diagnostics=diagnostics,scope='Provenance and finite diagnostics only; no universal proof, priority, significance, or independent-review certification')
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=='__main__': main()
