#!/usr/bin/env python3
"""Offline READ-ONLY evidence replay. No downloads/writes/bytecode/repair/reseal.

The optional --preseal mode skips only the final owned-inventory seal check.
The inherited, hash-bound I98 verifier independently replays the complete
original domain and its exact selective PDF scope. All subprocess output is
captured in memory; this verifier never creates an output file.
"""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
import hashlib
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[3]
S = ROOT/'frontier/sources/i102_relative_k3_oka_construction'
E = ROOT/'frontier/experiments/i102_relative_k3_oka_construction'
REPORT = ROOT/'frontier/iterations/i102-relative-k3-oka-construction.md'
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
DRIFT = {'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def rel(p):
    return str(p.relative_to(ROOT))

def read(p):
    return json.loads(p.read_bytes())

def require(ok, what):
    if not ok:
        raise AssertionError(what)

def owned():
    paths=[REPORT]
    for directory in (S,E):
        for p in directory.rglob('*'):
            require(not p.is_symlink(),'owned symlink '+rel(p))
            if p.is_file(): paths.append(p)
    return sorted(paths)

def main():
    require(sys.argv[1:] in ([],['--preseal']),'unexpected arguments')
    preseal=bool(sys.argv[1:]);inventory=owned();sealpath=S/'seal.json'
    require(all('__pycache__' not in p.parts for p in inventory),'owned bytecode')
    if not preseal:
        seal=read(sealpath)
        require(seal['pin']==PIN,'seal pin')
        require(seal['excluded_owned_files']==[rel(sealpath)],'seal exclusion')
        expected=[{'path':rel(p),'sha256':sha(p.read_bytes())} for p in inventory if p!=sealpath]
        require(seal['files']==expected,'exact owned bytes/inventory')
        require(seal['owned_file_count']==len(inventory),'owned count')

    inputs=read(S/'inputs.json')
    require(len(inputs)==12,'frozen input count')
    require({x['original'] for x in inputs if x['may_drift']}==DRIFT,'drift scope')
    drifted=[]
    for x in inputs:
        require(sha((ROOT/x['snapshot']).read_bytes())==x['sha256'],'frozen snapshot '+x['snapshot'])
        same=sha((ROOT/x['original']).read_bytes())==x['sha256']
        require(same or x['original'] in DRIFT,'immutable original '+x['original'])
        if not same:drifted.append(x['original'])
    snap=S/'snapshots'
    require(read(snap/'sources/upstream.json')['commit']==PIN,'upstream pin')
    original=(snap/'frontier/iterations/i98-complex-kahler-discovery.md').read_text()
    parent=read(snap/'frontier/experiments/i98-parent-verification.json')
    require(sha(original.encode())=='f7be1188a95868a235d31b1a0ae59264b218c7db620836246ff3a70d9ed5dcb8','exact original report')
    require(parent['seal_sha256']=='2c9329951ec86f97c4928e887cb94c9752c24b3c9dabd0e1da6fb198290bbab1','immutable parent seal anchor')
    brief=read(snap/'frontier/iterations/iteration102-relative-k3-oka-construction-task.json')['brief']
    require('FULL ORIGINAL I98 BRIEF' in brief and 'FULL ORIGINAL I98 REPORT' in brief and
            'FINALIZED PARENT RESPONSE' in brief,'full original input sections')
    require(original.strip() in brief,'unabridged original report in task input')
    require(read(snap/'frontier/iterations/iteration98-complex-kahler-discovery-task.json')['brief'].strip() in brief,
            'unabridged original I98 brief in task input')

    refs=read(S/'immutable-references.json')
    require(len(refs)==57,'reference count')
    require(len({x['path'] for x in refs})==len(refs),'duplicate references')
    require(not any(re.search(r'i10[01][_/.-]',x['path']) for x in refs),'active I100/I101 reference')
    for x in refs:require(sha((ROOT/x['path']).read_bytes())==x['sha256'],'immutable reference '+x['path'])
    scope=read(S/'scope.json')
    require(scope['pin']==PIN and scope['nomination'] is False,'scope contract')
    domain=read(ROOT/scope['domain_reference'])
    require(len(domain)==10373,'domain count')
    bylocal={x['local']:x for x in domain}
    manifest=read(S/'read-manifest.json')
    for x in manifest:
        raw=(ROOT/x['local']).read_bytes();t=raw.decode(errors='replace');lines=t.split('\n')
        require(1<=x['start']<=x['end']<=len(lines),'read range '+x['local'])
        passage='\n'.join(lines[x['start']-1:x['end']])
        require(x['line_convention']=='LF split; formfeeds remain within a line; no appended newline','LF convention')
        require(x['sha256']==sha(raw) and x['passage_sha256']==sha(passage.encode()),'read passage '+x['local'])
        require(x['total_LF_lines']==len(lines) and x['total_LF_newlines']==raw.count(b'\n') and
                x['total_splitlines']==len(t.splitlines()),'line-count convention')
        if x['local'] in bylocal:
            d=bylocal[x['local']]
            require(x['upstream_path']==d['path'] and x['git_sha']==d['git_sha'] and
                    x['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+d['path'],'pinned reading provenance')
        if 'pdf_local' in x:
            require(sha((ROOT/x['pdf_local']).read_bytes())==x['pdf_sha256'],'read PDF binding')

    queries=read(S/'queries.json')
    require(set(queries)=={'family_criterion','lower_operations'},'query scope')
    patterns={k:re.compile(v,re.I) for k,v in queries.items()};hits={k:[] for k in queries}
    for x in domain:
        for i,line in enumerate((ROOT/x['local']).read_text(errors='replace').splitlines(),1):
            for k,pat in patterns.items():
                if pat.search(line):hits[k].append({'path':x['path'],'local':x['local'],'splitline':i,'text':line})
    for k in queries:require(hits[k]==read(S/('search-'+k+'.json')),'exact lexical multiset '+k)

    requests=read(S/'current-primary-requests.json')
    expected={'2003.03757':1,'1106.5300':1,'2608.24392':2,'2610.12175':1,'2502.20028':6}
    require(len(requests)==len(expected),'current metadata scope')
    for x in requests:
        aid=x['url'].rsplit('/',1)[-1]
        require(aid in expected and x['status']==200,'primary response')
        data=(ROOT/x['local']).read_bytes()
        require(sha(data)==x['sha256'],'primary metadata bytes')
        history=re.sub('<[^>]+>',' ',data.decode(errors='replace').split('class="submission-history"')[-1].split('class="extra-services"')[0])
        require(history==x['submission_history'],'version passage')
        versions=[int(v) for v in re.findall(r'\[v(\d+)\]',history)]
        require(versions and max(versions)==expected[aid],'current pinned version')

    diag=subprocess.run([sys.executable,'-B',str(E/'diagnostics.py')],cwd=ROOT,capture_output=True,text=True)
    require(diag.returncode==0,'I102 diagnostics: '+diag.stderr)
    diagnostic=json.loads(diag.stdout)
    require(diagnostic==read(E/'diagnostic-results.json'),'diagnostic reproduction')
    old=subprocess.run([sys.executable,'-B',str(ROOT/scope['inherited_verifier'])],cwd=ROOT,capture_output=True,text=True)
    require(old.returncode==0,'unchanged I98 replay: '+old.stdout+old.stderr)
    inherited=json.loads(old.stdout)
    require(inherited['status']=='PASS' and inherited['original_blob_positions']==10373 and
            inherited['inherited_PDF_text_hashes']==776 and inherited['unique_primary_PDF_replays']==5 and
            inherited['pinned_PDF_replays']==3,'inherited replay scope')
    print(json.dumps({'status':'PASS','mode':'preseal-read-only' if preseal else 'final-read-only',
        'owned_files':len(inventory),'frozen_inputs':len(inputs),'immutable_references':len(refs),
        'read_records':len(manifest),'new_lexical_hits':{k:len(v) for k,v in hits.items()},
        'current_primary_version_pages':len(requests),'allowed_live_drift':drifted,
        'diagnostics':diagnostic,'inherited_I98':inherited,
        'scope':'offline evidence replay only; not universal proof, novelty, human review or formal certification'},indent=2))

if __name__ == '__main__':
    main()
