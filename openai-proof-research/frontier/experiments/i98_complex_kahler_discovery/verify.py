#!/usr/bin/env python3
"""Offline, read-only replay. No network, writes, repair, reseal or bytecode.

--preseal skips only the final inventory root, for validation before sealing.
External commands are rg (listing), pdftotext to stdout, and -B diagnostics.
"""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
import hashlib
import json
import re
import html
import subprocess
from collections import Counter

ROOT = Path(__file__).resolve().parents[3]
S = ROOT / 'frontier/sources/i98_complex_kahler_discovery'
E = ROOT / 'frontier/experiments/i98_complex_kahler_discovery'
REPORT = ROOT / 'frontier/iterations/i98-complex-kahler-discovery.md'
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
DRIFT = {'README.md', 'frontier/README.md', 'frontier/TEN-FINDINGS.md',
         'frontier/iterations/README.md'}

def sha(b):
    return hashlib.sha256(b).hexdigest()

def rel(p):
    return str(p.relative_to(ROOT))

def read_json(p):
    return json.loads(p.read_bytes())

def require(condition, message):
    if not condition:
        raise AssertionError(message)

def owned():
    paths = [REPORT]
    for d in (S, E):
        for p in d.rglob('*'):
            require(not p.is_symlink(), 'owned symlink: '+rel(p))
            if p.is_file():
                paths.append(p)
    return sorted(paths)

def main():
    require(sys.argv[1:] in ([], ['--preseal']), 'unexpected arguments')
    preseal = sys.argv[1:] == ['--preseal']
    inventory = owned()
    require(all('__pycache__' not in p.parts for p in inventory), 'bytecode in inventory')
    seal_path = S/'seal.json'
    if not preseal:
        seal = read_json(seal_path)
        require(seal['pin'] == PIN, 'seal pin')
        require(seal['excluded_owned_files'] == [rel(seal_path)], 'seal exclusion')
        expected = [{'path':rel(p), 'sha256':sha(p.read_bytes())}
                    for p in inventory if p != seal_path]
        require(seal['files'] == expected, 'exact owned inventory or bytes changed')
        require(seal['owned_file_count'] == len(inventory), 'owned count')

    inputs = read_json(S/'inputs.json')
    require({r['original'] for r in inputs if r['may_drift']} == DRIFT, 'drift list')
    require(len(inputs) == 8, 'input inventory')
    drifted = []
    for row in inputs:
        require(sha((ROOT/row['snapshot']).read_bytes()) == row['sha256'], 'snapshot')
        same = sha((ROOT/row['original']).read_bytes()) == row['sha256']
        require(same or row['original'] in DRIFT, 'immutable input: '+row['original'])
        if not same:
            drifted.append(row['original'])
    require(read_json(S/'snapshots/sources/upstream.json')['commit'] == PIN, 'upstream pin')
    refs = read_json(S/'immutable-references.json')
    require(len(refs) == 1 and refs[0]['path'] ==
            'frontier/sources/i88_nonlinear_banach_discovery/search-domain.json', 'reference scope')
    for row in refs:
        require(sha((ROOT/row['path']).read_bytes()) == row['sha256'], 'immutable reference')
    domain = read_json(S/'search-domain.json')
    require(domain == read_json(ROOT/refs[0]['path']), 'inherited mapping')
    tree = read_json(S/'snapshots/sources/preprints-tree.json')
    require(tree.get('truncated') is False and len(tree['tree']) == 13223, 'complete tree')
    blobs = {r['path']:r for r in tree['tree'] if r['type'] == 'blob'}
    require(len(domain) == len(blobs) == 10373, 'blob-position count')
    require({r['path'] for r in domain} == set(blobs), 'full-domain path bijection')
    kinds = Counter(r['kind'] for r in domain)
    require(kinds == {'corpus':9340, 'outside_bytes':257, 'outside_pdf':776}, 'domain kinds')
    titles = sorted({x['path'].split('/')[1] for x in tree['tree']
                     if len(x['path'].split('/')) > 2})
    require(len(titles) == 749 and titles == read_json(S/'all-titles.json'), 'all titles')
    corpus = read_json(S/'i14-files.json')
    require(corpus['command'] == ['rg', '--files', '--no-ignore',
            'frontier/sources/i14_spectral_width_novelty_r3/corpus'], 'corpus command')
    files = sorted(subprocess.check_output(corpus['command'], cwd=ROOT).decode().splitlines())
    require(files == corpus['files'] == sorted(r['local'] for r in domain
                                              if r['kind'] == 'corpus'), 'I14 exact inventory')

    queries = read_json(S/'queries.json')
    require(set(queries) == {'relative','covers','quantitative'}, 'query names')
    hits = {name:[] for name in queries}
    compiled = {name:re.compile(expr,re.I) for name,expr in queries.items()}
    texts = {}
    for row in domain:
        original = (ROOT/row['original_local']).read_bytes()
        require(sha(original) == row['original_sha256'], 'original SHA256: '+row['path'])
        git = hashlib.sha1(b'blob '+str(len(original)).encode()+b'\0'+original).hexdigest()
        require(git == row['git_sha'] == blobs[row['path']]['sha'], 'Git blob: '+row['path'])
        representative = (ROOT/row['local']).read_bytes()
        require(sha(representative) == row['sha256'], 'representation SHA256: '+row['path'])
        # Path.read_text uses universal-newline translation; splitlines itself
        # also recognizes formfeeds and other separators. Preserve exact hits.
        t = (ROOT/row['local']).read_text(errors='replace')
        texts[row['path']] = t
        for number,line in enumerate(t.splitlines(),1):
            for name,rx in compiled.items():
                if rx.search(line):
                    hits[name].append({'path':row['path'],'local':row['local'],
                                       'splitline':number,'text':line})
    for name in queries:
        require(hits[name] == read_json(S/('search-'+name+'.json')), 'exact hit multiset: '+name)

    families = read_json(S/'families.json')
    require(len(families) == 28 and set(families) <= set(titles), 'selected family scope')
    selected = [r for r in domain if r['path'].split('/')[1] in families]
    require(len(selected) == 423 and selected == read_json(S/'selected-inventory.json'), 'selected inventory')
    statements = []
    rx = re.compile(r'\\begin\{(?:theorem|corollary|assumption)\}.*?\\end\{(?:theorem|corollary|assumption)\}',re.S)
    labels = ('thm:main','thm:finite','hyp:campana','hyp:effective','asm:log-iitaka','thm:abelianity')
    for row in selected:
        if not row['path'].endswith('.tex'):
            continue
        t = texts[row['path']]
        for match in rx.finditer(t):
            if any(label in match.group() for label in labels):
                statements.append({'path':row['path'],'local':row['local'],
                                   'LF_start':t.count('\n',0,match.start())+1,'text':match.group()})
    require(statements == read_json(S/'statement-screen.json'), 'statement slices')

    read = read_json(S/'read-manifest.json')
    bylocal = {r['local']:r for r in domain}
    for row in read:
        raw = (ROOT/row['local']).read_bytes()
        t = raw.decode(errors='replace')
        lines = t.split('\n')
        passage = '\n'.join(lines[row['start']-1:row['end']])
        require(row['line_convention'] == 'LF split; formfeeds remain within a line', 'line convention')
        require(row['total_LF_lines'] == len(lines) and row['total_LF_newlines'] == raw.count(b'\n')
                and row['total_splitlines'] == len(t.splitlines()), 'line counts')
        require(sha(raw) == row['sha256'] and passage == row['passage']
                and sha(passage.encode()) == row['passage_sha256'], 'passage')
        if row['local'] in bylocal:
            d = bylocal[row['local']]
            require(row['upstream_path'] == d['path'] and row['git_sha'] == d['git_sha']
                    and row['url'] == 'https://raw.githubusercontent.com/openai/math/'+PIN+'/'+d['path'], 'passage provenance')
    history = read_json(S/'history-screen.json')
    require(history['convention'] == 'splitlines' and set(history['hits']) == DRIFT, 'history scope')
    rx = re.compile(history['expression'],re.I)
    for path,expected in history['hits'].items():
        actual = [{'splitline':n,'text':line} for n,line in enumerate(
            (S/'snapshots'/path).read_text().splitlines(),1) if rx.search(line)]
        require(actual == expected, 'history exact hits')

    primaries = read_json(S/'primary-manifest.json')
    requests = []
    for p in sorted((S/'external').glob('*requests.json')):
        for row in read_json(p):
            r = dict(row)
            f = S/'external'/r['file']
            r.update(local=rel(f),sha256=sha(f.read_bytes()))
            if f.suffix == '.pdf' and f.read_bytes().startswith(b'%PDF'):
                txt = Path(str(f)+'.txt')
                r.update(text=rel(txt),text_sha256=sha(txt.read_bytes()))
            requests.append(r)
    require(requests == primaries and all(r['status'] == 200 for r in requests), 'primary request records')
    versions = []
    for p in sorted((S/'external').glob('*abs.html')):
        t = p.read_text()
        title = re.search(r'<title>(.*?)</title>',t,re.S)
        start = t.find('class="submission-history"')
        if start < 0: start = t.find('submission-history')
        end = t.find('class="extra-services"',start)
        if end < 0: end = start+2500
        raw = t[start:end]
        versions.append({'local':rel(p),'title':html.unescape(title.group(1)) if title else None,
                         'sha256':sha(p.read_bytes()),'history_html':raw,
                         'history_text':html.unescape(re.sub('<[^>]*>',' ',raw))})
    require(versions == read_json(S/'versions.json'), 'version metadata')
    require((S/'external/xie-zhao-latest.pdf').read_bytes() ==
            (S/'external/xie-zhao-v2.pdf').read_bytes(), 'Xie current/fixed version binding')
    require('arXiv:2608.24392v2' in (S/'external/xie-zhao-v2.pdf.txt').read_text(), 'Xie PDF version')
    seen_pdf = set()
    warnings = []
    for row in primaries:
        if 'text' not in row or row['sha256'] in seen_pdf:
            continue
        seen_pdf.add(row['sha256'])
        proc = subprocess.run(['pdftotext','-layout',str(ROOT/row['local']),'-'],
                              stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True)
        require(sha(proc.stdout) == row['text_sha256'], 'primary PDF stdout replay: '+row['file'])
        if proc.stderr:
            warnings.append({'file':row['file'],'stderr':proc.stderr.decode(errors='replace')})
    require(len(seen_pdf) == 5, 'unique primary PDF scope')
    replays = read_json(S/'pdf-replays.json')
    require(len(replays) == 3 and all(r in domain for r in replays), 'selective pinned PDF scope')
    for row in replays:
        proc = subprocess.run(['pdftotext','-layout',str(ROOT/row['original_local']),'-'],
                              stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True)
        require(sha(proc.stdout) == row['sha256'], 'pinned PDF stdout replay: '+row['path'])
        if proc.stderr:
            warnings.append({'file':row['path'],'stderr':proc.stderr.decode(errors='replace')})
    result = subprocess.check_output([sys.executable,'-B',str(E/'diagnostics.py')],cwd=ROOT)
    require(json.loads(result) == read_json(E/'diagnostic-results.json'), 'diagnostic replay')
    print(json.dumps({'status':'PASS','mode':'preseal' if preseal else 'final-read-only',
        'owned_files':len(inventory),'original_blob_positions':len(domain),
        'inherited_PDF_text_hashes':kinds['outside_pdf'],
        'lexical_hits':{k:len(v) for k,v in hits.items()},'theorem_slices':len(statements),
        'read_records':len(read),'unique_primary_PDF_replays':len(seen_pdf),
        'pinned_PDF_replays':len(replays),'allowed_live_drift':drifted,
        'PDF_warnings':warnings,'diagnostics':json.loads(result),
        'scope':'evidence replay, not proof or contribution certification'},ensure_ascii=False,indent=2))

if __name__ == '__main__':
    main()
