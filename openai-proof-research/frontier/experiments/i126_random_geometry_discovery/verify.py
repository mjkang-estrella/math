"""Offline read-only replay. All immutable checks precede finite diagnostics.

The sealed I123 engine is called ONCE: it is a flat corpus verifier, not a
recursive invocation of older corpus verifiers. No acquisition helper runs.
--preseal validates without writing and refuses an existing seal.
"""
import sys
sys.dont_write_bytecode = True
import os


def readonly(event, args):
    if event == 'open':
        mode = args[1]
        flags = args[2] if len(args) > 2 else 0
        if ((isinstance(mode, str) and any(c in mode for c in 'wax+')) or
            (isinstance(flags, int) and flags &
             (os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND))):
            raise RuntimeError('Read-only replay blocked write: '+repr(args[0]))
    if event.startswith(('socket.', 'subprocess.')) or event in {
        'os.system','os.remove','os.rename','os.rmdir','os.mkdir','os.chmod',
        'os.chown','os.utime','os.truncate','os.link','os.symlink','shutil.copyfile',
        'os.putenv','os.unsetenv','os.exec','os.posix_spawn',
    }:
        raise RuntimeError('Offline read-only replay blocked '+event)


sys.addaudithook(readonly)
import contextlib
import hashlib
import io
import json
from pathlib import Path
import re
import runpy

ROOT = Path.cwd().resolve()
S = Path('frontier/sources/i126_random_geometry_discovery')
X = Path('frontier/experiments/i126_random_geometry_discovery')
R = Path('frontier/iterations/i126-random-geometry-discovery.md')
OLD = Path('frontier/experiments/i123_thermal_production_stability/verify.py')
OLD_SHA = 'feef6639e9a4c9916f4b845f771263e795a25fbee83227c0716e339d7a5ef4c3'
OLD_SEAL = Path('frontier/sources/i123_thermal_production_stability/seal.json')
OLD_SEAL_SHA = '6637f83d73e1270a4d7b5b61d5d1596859e273b4bb10b9ba771c29f596759756'
MUTABLE = {'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def read(p):
    p = Path(p)
    require(p.is_file() and not p.is_symlink(), 'Missing/symlink '+str(p))
    require(p.resolve().is_relative_to(ROOT), 'Outside root '+str(p))
    return p.read_bytes()


def sha(b):
    return hashlib.sha256(b).hexdigest()


def load(p):
    return json.loads(read(p))


def inventory():
    files = [str(R)]
    dirs = []
    for root in (S, X):
        require(root.is_dir() and not root.is_symlink(), 'Missing owned root')
        dirs.append(str(root))
        for p in root.rglob('*'):
            require(not p.is_symlink(), 'Owned symlink '+str(p))
            if p.is_dir():
                dirs.append(str(p))
            elif p.is_file() and p != S/'seal.json':
                files.append(str(p))
    return sorted(files), sorted(dirs)


def row(p):
    b = read(p)
    return dict(path=str(p), sha256=sha(b), bytes=len(b))


def main():
    require(sys.argv[1:] in [[], ['--preseal']], 'Only --preseal is supported')
    preseal = bool(sys.argv[1:])
    files, dirs = inventory()
    validated = [row(p) for p in files if p != str(S/'preseal-validation.json')]
    if preseal:
        require(not (S/'seal.json').exists(), 'Preseal refuses existing seal')
    else:
        seal = load(S/'seal.json')
        require(seal['schema'] == 'i126-one-final-seal-v1', 'Seal schema')
        require(seal['directories'] == dirs, 'Owned directory inventory')
        require(seal['files'] == [row(p) for p in files], 'All owned immutable bytes')
        receipt = load(S/'preseal-validation.json')
        require(receipt['status']=='PASS' and receipt['validated_files']==validated,
                'Preseal validated exact final bytes')
    require(sha(read(OLD)) == OLD_SHA, 'Flat engine immutable bytes')
    require(sha(read(OLD_SEAL)) == OLD_SEAL_SHA, 'Original I123 seal')
    refs = load(S/'references.json')
    require({r['path'] for r in refs if r['mutable']}==MUTABLE, 'Mutable set')
    require(len({r['path'] for r in refs})==len(refs), 'Duplicate reference')
    drift=[]
    for r in refs:
        require(not re.search(r'(?:/i|/iteration)(124|125)(?:[-_/])',r['path']),
                'Active output dependency')
        require(sha(read(r['snapshot']))==r['sha256'] and len(read(r['snapshot']))==r['bytes'],
                'Frozen snapshot '+r['path'])
        if r['mutable']:
            if sha(read(r['path'])) != r['sha256']:
                drift.append(r['path'])
        else:
            require(sha(read(r['path']))==r['sha256'] and len(read(r['path']))==r['bytes'],
                    'Original reference '+r['path'])
    for r in load(S/'read-manifest.json'):
        b=read(r['local']); raw=b.decode('utf-8')
        require((sha(b),len(b),b.count(b'\n'),len(raw.splitlines()),b.endswith(b'\n')) ==
                (r['sha256'],r['bytes'],r['lf_count'],r['splitlines_count'],r['ends_lf']),
                'Read source conventions '+r['local'])
        t=json.loads(raw)[r['field']] if r['field'] is not None else raw
        if not isinstance(t,str): t=json.dumps(t,indent=2,ensure_ascii=False)
        ls=t.splitlines(); a,z=r['start'],r['end']
        require(len(ls)==r['decoded_lines'] and 1<=a<=z<=len(ls), 'Decoded/range convention')
        require(sha('\n'.join(ls[a-1:z]).encode())==r['range_sha256'], 'Read range bytes')
    # Verify all decoded original context fields are covered, not just task titles.
    records=load(S/'read-manifest.json')
    for name in ('iteration123-thermal-production-stability-task.json',
                 'iteration120-thermal-trace-stability-task.json'):
        p='frontier/iterations/'+name; task=load(p)
        for k,v in task.items():
            t=v if isinstance(v,str) else json.dumps(v,indent=2,ensure_ascii=False)
            covered=set()
            for rr in records:
                if rr['local'] in (p, str(S/'snapshots'/p)) and rr['field']==k:
                    covered.update(range(rr['start'],rr['end']+1))
            require(covered==set(range(1,len(t.splitlines())+1)), 'Recursive field not covered '+k)
    brief=load('frontier/iterations/iteration126-random-geometry-discovery-task.json')['brief']
    original=brief.split('--- ORIGINAL I123 REPORT ---\n',1)[1].split('\n--- FINALIZED PARENT RESPONSE ---',1)[0]
    require(original.strip()==read('frontier/iterations/i123-thermal-production-stability.md').decode().strip(),
            'Complete original I123 report in supplied task')
    parent=json.loads(brief.split('--- FINALIZED PARENT RESPONSE ---\n',1)[1])
    require(parent==load('frontier/experiments/i123-parent-verification.json'), 'Finalized parent receipt')
    require(parent['seal_sha256']==OLD_SEAL_SHA, 'Parent seal identity')
    domain=load('frontier/sources/i114_quantum_information_discovery/search-domain.json')
    # Read only mapping metadata here; the flat engine hashes the corpus once below.
    domain_rows=domain['files'] if isinstance(domain,dict) else domain
    bypath={r['path']:r for r in domain_rows}
    selected=load(S/'selected-inventory.json')
    catalogue=read(S/'snapshots/sources/CONTENTS.md').decode().splitlines()
    roots=set()
    for number in (211,223,230,237):
        a=next(i for i,l in enumerate(catalogue) if l.startswith('**'+str(number)+'.'))
        z=next((i for i in range(a+1,len(catalogue)) if re.match(r'\*\*\d+\.',catalogue[i])),len(catalogue))
        roots.update(re.findall(r'preprints/([^/]+)/','\n'.join(catalogue[a:z])))
    require(sorted(roots)==load(S/'family-roots.json'), 'Exact companion roots from frozen catalogue')
    require(selected==[r for r in domain_rows if r['path'].split('/')[1] in roots],
            'Complete selected companion inventory')
    for r in selected:
        require(bypath[r['path']]==r, 'Selected original-position mapping')
    for rr in records:
        if 'domain_path' in rr:
            require(bypath[rr['domain_path']]['local']==rr['local'] and
                    rr['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+rr['domain_path'],
                    'Pinned read source URL/mapping')
    lexical=load(S/'lexical-query.json'); result=[]
    regex=re.compile(lexical['pattern'], re.I)
    for p in lexical['files']:
        for number,line in enumerate(read(p).decode().splitlines(),1):
            for match in regex.finditer(line):
                result.append(dict(path=p,line=number,start=match.start(),end=match.end(),text=match.group(),line_text=line))
    require(result==load(S/'lexical-results.json'), 'Exact lexical occurrence multiset')
    converter_path='frontier/experiments/i114_quantum_information_discovery/html_text.py'
    for dep in load(S/'engine-dependencies.json'):
        require(row(dep['path'])==dep, 'Execution dependency immutable bytes')
    converter=runpy.run_path(converter_path)['convert']
    for r in load(S/'html-views.json'):
        require(sha(read(r['html']))==r['html_sha256'] and sha(read(r['text']))==r['text_sha256'], 'HTML view binding')
        require(converter(read(r['html']).decode())==read(r['text']).decode(), 'Deterministic HTML conversion')
    # All I126 immutable checks are finished. The engine checks ALL inherited
    # immutable bytes before it runs any of its finite diagnostics.
    saved_args=sys.argv[:]
    sys.argv=[str(OLD)]
    output=io.StringIO()
    with contextlib.redirect_stdout(output):
        runpy.run_path(str(OLD),run_name='__main__')
    sys.argv=saved_args
    inherited=json.loads(output.getvalue())
    require(inherited['status']=='PASS' and inherited['corpus_traversals']==1,
            'Flat inherited replay')
    diagnostic=runpy.run_path(str(X/'check.py'))['run']()
    print(json.dumps(dict(status='PASS',mode='preseal-read-only' if preseal else 'sealed-read-only',
        corpus_traversals=1,original_positions=inherited['original_positions'],
        original_bytes=inherited['original_bytes'],domain_kinds=inherited['domain_kinds'],
        inherited_diagnostics=inherited['diagnostics'],i126_diagnostics=diagnostic,
        inherited_lexical_occurrences=inherited['inherited_lexical_occurrences'],
        own_lexical_occurrences=len(result),own_read_records=len(records),
        own_html_views=len(load(S/'html-views.json')),owned_files_without_seal=len(files),
        owned_directories=len(dirs),permitted_mutable_drift=sorted(drift),
        validated_files=validated,
        scope='Immutable provenance and finite diagnostics only; analytic and contribution verdicts are in the report'),indent=2))


if __name__=='__main__':
    main()
