"""Offline, read-only, one-pass inherited-corpus replay.

All immutable bytes and provenance checks precede diagnostic execution.
There is no download, repair, reseal, subprocess or bytecode path.
--preseal validates an unsealed package; it does not create anything.
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
        'os.system', 'os.remove', 'os.rename', 'os.rmdir', 'os.mkdir',
        'os.chmod', 'os.chown', 'os.utime', 'os.truncate', 'os.link',
        'os.symlink', 'shutil.copyfile', 'os.putenv', 'os.unsetenv',
        'os.exec', 'os.posix_spawn',
    }:
        raise RuntimeError('Offline read-only replay blocked '+event)


sys.addaudithook(readonly)
from pathlib import Path
import hashlib
import json
import re
import runpy

ROOT = Path.cwd().resolve()
S = Path('frontier/sources/i120_thermal_trace_stability')
X = Path('frontier/experiments/i120_thermal_trace_stability')
R = Path('frontier/iterations/i120-thermal-trace-stability.md')
SEAL = S/'seal.json'
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
MUTABLE = {'README.md', 'frontier/README.md', 'frontier/TEN-FINDINGS.md',
           'frontier/iterations/README.md'}
ORIGINAL_SEALS = {
    114: 'f4850563e1ca604d248e0cf8956aed950aadb2ab6977c3237b53e15897540764',
    117: '1b443f3b148bc01bd2df57678a330f199ceb688ae8389959f51421aee5ba9523',
}


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def read(path):
    p = Path(path)
    require(p.is_file() and not p.is_symlink(), 'Missing/symlink file '+str(p))
    require(p.resolve().is_relative_to(ROOT), 'Outside root '+str(p))
    return p.read_bytes()


def sha(b):
    return hashlib.sha256(b).hexdigest()


def load(p):
    return json.loads(read(p))


def bind(row):
    b = read(row['path'])
    require(sha(b) == row['sha256'], 'Immutable hash mismatch '+row['path'])
    if 'bytes' in row:
        require(len(b) == row['bytes'], 'Immutable size mismatch '+row['path'])


def inventory(source, experiment, report):
    seal = Path(source)/'seal.json'
    files = [str(report)]
    directories = []
    for base in [Path(source), Path(experiment)]:
        require(base.is_dir() and not base.is_symlink(), 'Missing/symlink root')
        directories.append(str(base))
        for p in base.rglob('*'):
            require(not p.is_symlink(), 'Owned symlink '+str(p))
            if p.is_dir():
                directories.append(str(p))
            elif p.is_file():
                if p != seal:
                    files.append(str(p))
            else:
                require(False, 'Unexpected entry '+str(p))
    return sorted(files), sorted(directories)


def reference_check(rows):
    require({r['path'] for r in rows if r['mutable']} == MUTABLE,
            'Unexpected mutable set')
    require(len({r['path'] for r in rows}) == len(rows), 'Duplicate reference')
    drift = []
    for r in rows:
        require(not any(s in r['path'].lower() for s in ['i112', 'i113']),
                'Forbidden working-output reference')
        if 'snapshot' in r:
            require(sha(read(r['snapshot'])) == r['sha256'], 'Snapshot changed')
        if r['mutable']:
            if sha(read(r['path'])) != r['sha256']:
                drift.append(r['path'])
        else:
            bind(r)
    return sorted(drift)


def passage_check(source, source_map):
    manifest = load(source/'read-manifest.json')['reads']
    passages = []
    for row in manifest:
        b = read(row['local'])
        lines = b.decode('utf-8', errors='replace').splitlines()
        require((sha(b), len(b), b.count(b'\n'), len(lines), b.endswith(b'\n')) ==
                (row['sha256'], row['bytes'], row['lf_count'],
                 row['splitlines_count'], row['ends_lf']),
                'Read-source/line convention changed '+row['local'])
        if 'domain_path' in row:
            original = source_map[row['domain_path']]
            require(original['local'] == row['local'], 'Source mapping changed')
            require(row['url'] == 'https://raw.githubusercontent.com/openai/math/'+
                    PIN+'/'+row['domain_path'], 'Unpinned source URL')
        for a, z in row['ranges_inclusive_splitlines']:
            require(1 <= a <= z <= len(lines), 'Invalid passage range')
            text = '\n'.join(lines[a-1:z])
            passages.append(dict(local=row['local'], source_sha256=row['sha256'],
                                 start_splitlines=a, end_splitlines=z, text=text,
                                 passage_utf8_sha256=sha(text.encode())))
    require(passages == load(source/'passages.json'), 'Passage text/hash mismatch')
    return len(manifest), len(passages)


def main():
    require(sys.argv[1:] in [[], ['--preseal']], 'Only --preseal is supported')
    preseal = bool(sys.argv[1:])
    files, directories = inventory(S, X, R)
    if preseal:
        require(not SEAL.exists(), 'Preseal refuses an existing seal')
    else:
        seal = load(SEAL)
        require(seal['schema'] == 'i120-one-final-seal-v1', 'Wrong seal schema')
        require(seal['directories'] == directories, 'Owned directory mismatch')
        require([x['path'] for x in seal['files']] == files, 'Owned file mismatch')
        for row in seal['files']:
            bind(row)
    drift = {'i120': reference_check(load(S/'references.json'))}
    packages = load(S/'inherited.json')
    require([p['iteration'] for p in packages] == [114, 117], 'Inherited scope')
    for p in packages:
        require(sha(read(p['seal'])) == p['seal_sha256'] ==
                ORIGINAL_SEALS[p['iteration']], 'Original seal changed')
        seal = load(p['seal'])
        require(seal['files'] == p['files'] and seal['directories'] == p['directories'],
                'Incomplete original package binding')
        f, d = inventory(p['source'], p['experiment'], p['report'])
        require(f == [r['path'] for r in p['files']] and d == p['directories'],
                'Inherited exact inventory changed')
        for row in p['files']:
            bind(row)
        source = Path(p['source'])
        refname = 'inputs.json' if p['iteration'] == 114 else 'references.json'
        drift['i'+str(p['iteration'])] = reference_check(load(source/refname))
    old = Path(packages[0]['source'])
    mid = Path(packages[1]['source'])
    inherited = load(mid/'inherited.json')
    require(inherited['seal_sha256'] == ORIGINAL_SEALS[114], 'I117 original binding')
    require(inherited['directories'] == packages[0]['directories'], 'I117 original dirs')
    for row in inherited['files']:
        bind(row)
    require([r for r in inherited['files'] if r['path'] != inherited['seal']] ==
            sorted(packages[0]['files'], key=lambda r:r['path']),
            'I117 incomplete I114 binding')
    require(load(old/'snapshots/sources/upstream.json')['commit'] == PIN, 'Wrong pin')
    tree = load(old/'snapshots/sources/preprints-tree.json')
    require(tree['truncated'] is False and len(tree['tree']) == 13223, 'Incomplete tree')
    blobs = {r['path']:r['sha'] for r in tree['tree'] if r['type'] == 'blob'}
    domain = load(old/'search-domain.json')
    require(domain == load(old/'snapshots/frontier/sources/i88_nonlinear_banach_discovery/search-domain.json'),
            'I88 original mapping changed')
    require(len(domain) == len(blobs) == 10373 and
            {r['path'] for r in domain} == set(blobs), 'Original coverage changed')
    queries = {}
    for label, base in [('i114', old), ('i117', mid)]:
        for key, expression in load(base/'queries.json').items():
            queries[(label, key)] = re.compile(expression)
    hits = {key:[] for key in queries}
    kinds = {}
    original_bytes = 0
    # One traversal verifies each position and both inherited lexical domains.
    for row in domain:
        require(not any(s in row['local'].lower() for s in ['i112','i113']),
                'Working-output source dependency')
        b = read(row['original_local'])
        original_bytes += len(b)
        require(sha(b) == row['original_sha256'], 'Original bytes changed '+row['path'])
        git = hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        require(git == row['git_sha'] == blobs[row['path']], 'Original Git binding')
        view = b if row['local'] == row['original_local'] else read(row['local'])
        require(sha(view) == row['sha256'], 'View changed '+row['path'])
        kinds[row['kind']] = kinds.get(row['kind'],0)+1
        for number, line in enumerate(view.decode('utf-8',errors='replace').splitlines(),1):
            for key, pattern in queries.items():
                for mt in pattern.finditer(line):
                    hits[key].append(dict(path=row['path'],local=row['local'],
                                          line_splitlines=number,start=mt.start(),end=mt.end(),
                                          match=mt.group(),text=line))
    require(kinds == {'corpus':9340,'outside_pdf':776,'outside_bytes':257}, 'Domain kinds')
    for (label,key), rows in hits.items():
        base = old if label == 'i114' else mid
        require(rows == load(base/('search-'+key+'.json')), 'Exact inherited lexical results')
    corpus = Path('frontier/sources/i14_spectral_width_novelty_r3/corpus')
    corpus_paths = sorted(str(p) for p in corpus.rglob('*') if p.is_file())
    require(corpus_paths == load(old/'corpus-rg-inventory.json'), 'Original rg inventory')
    require(set(corpus_paths) == {r['original_local'] for r in domain if r['kind']=='corpus'},
            'Original corpus positions')
    roots = {r['path'].split('/')[1] for r in tree['tree']}
    for base, flags in [(old,0),(mid,re.I)]:
        titles = load(base/'title-screen.json')
        require(len(roots) == titles['roots'] == 749, 'Manuscript roots')
        require(sorted(r for r in roots if re.search(titles['expression'],r,flags)) ==
                titles['matches'], 'Exact title results')
    selected = load(old/'title-screen.json')['matches']
    require(load(old/'selected-inventory.json') ==
            [r for r in domain if r['path'].split('/')[1] in selected], 'Selected original inventory')
    dm = {r['path']:r for r in domain}
    passages = {str(base):passage_check(base,dm) for base in [old,mid,S]}
    for base in [old,mid]:
        for path in MUTABLE:
            frozen = read(base/'snapshots'/path).decode(errors='replace').splitlines()
            for row in load(base/(path.replace('/','_')+'.read-extract.json')):
                require(frozen[row['line']-1] == row['text'], 'Frozen ledger excerpt')
    scoped = load(S/'lexical-query.json')
    local_hits = []
    pattern = re.compile(scoped['expression'])
    for path in scoped['selected_sources']:
        for number,line in enumerate(read(path).decode(errors='replace').splitlines(),1):
            for mt in pattern.finditer(line):
                local_hits.append(dict(local=path,line_splitlines=number,start=mt.start(),
                                       end=mt.end(),match=mt.group(),text=line))
    require(local_hits == load(S/'lexical-results.json'), 'Exact selected-source lexical results')
    # The converter's bytes were checked in the original inventory above.
    convert = runpy.run_path('frontier/experiments/i114_quantum_information_discovery/html_text.py')['convert']
    html_views = 0
    for base in [old,mid]:
        for path in sorted((base/'external').glob('*.html')):
            require(convert(read(path).decode(errors='replace')).encode() == read(path.with_suffix('.txt')),
                    'Deterministic HTML view changed')
            html_views += 1
        for row in load(base/'http-log.json'):
            if row.get('status') == 200:
                suffix = '.tex' if row['url'].endswith('.tex') else '.html'
                b = read(base/'external'/(row['name']+suffix))
                require(sha(b) == row['sha256'] and len(b) == row['bytes'], 'HTTP response binding')
                if suffix == '.tex':
                    path = 'preprints/'+row['url'].split('/preprints/',1)[1]
                    require(b == read(dm[path]['original_local']), 'Pinned/current source binding')
    require(read(mid/'external/li-v1.txt') == read(old/'external/li-html.txt'), 'Li version identity')
    # All immutable bytes, original bindings, passages and lexical results
    # have passed. No diagnostic program was executed before this point.
    diagnostics = {}
    for label, path in [('i114',packages[0]['experiment']),
                        ('i117',packages[1]['experiment']), ('i120',str(X))]:
        diagnostics[label] = runpy.run_path(str(Path(path)/'check.py'))['run']()
        require(diagnostics[label]['status'] == 'PASS', 'Diagnostic failure '+label)
    for label,base in [('i114',old),('i117',mid)]:
        prior = load(base/'preseal-validation.json')
        require(prior['status']=='PASS' and prior['mode']=='preseal', 'Inherited validation missing')
        require(prior['diagnostics'] == diagnostics[label], 'Inherited diagnostics changed')
    if not preseal:
        prior = load(S/'preseal-validation.json')
        require(prior['status']=='PASS' and prior['mode']=='preseal', 'No preseal validation')
        require(prior['diagnostics']==diagnostics, 'Diagnostics changed since validation')
    result = dict(status='PASS', mode='preseal' if preseal else 'sealed-read-only',
                  owned_files_without_seal=len(files), owned_directories=len(directories),
                  original_positions=len(domain), original_bytes=original_bytes,
                  corpus_traversals=1, domain_kinds=kinds,
                  inherited_lexical_occurrences={label+':'+key:len(rows)
                                                 for (label,key),rows in hits.items()},
                  selected_source_lexical_occurrences=len(local_hits),
                  read_sources_and_passages=passages, html_views=html_views,
                  permitted_mutable_drift=drift, diagnostics=diagnostics,
                  scope='Immutable provenance and finite exact diagnostics only; analytic verdicts and contribution assessment are in the report')
    print(json.dumps(result,indent=2,sort_keys=True))


if __name__ == '__main__':
    main()
